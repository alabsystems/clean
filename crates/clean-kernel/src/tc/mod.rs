// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Type checker
//!
//! The core type checking algorithm.

pub mod batch;
mod branch_sharing;
mod cert;
mod config;
mod def_eq;
pub mod equiv_manager;
mod eta;
pub mod expr_location;
mod heartbeat;
pub(crate) mod heartbeat_profiler;
mod infer;
mod infer_cubical;
mod infer_proj;
mod infer_zfc;
mod local_context;
mod monad_reduce;
mod reduction;
pub mod reduction_stats;
mod sliding_cache;
mod sliding_equiv_manager;
mod type_error;
mod whnf;
mod whnf_proj;
pub mod whnf_proof;

pub use expr_location::{ExprLocation, ExprPathStep};
pub use local_context::{LocalContext, LocalDecl};
#[cfg(test)]
pub(crate) use reduction::string_lit_to_constructor;
// `isProp A := (x y : A) → Path (λ_.A) x y` — re-exported so the prop-truncation
// HIT recursor (`Environment::build_truncation_recursor`) spells its `isProp P`
// premise with the *same* definition the h-level library uses.
pub(crate) use reduction::kan::is_prop_type;
pub use type_error::TypeError;

/// Opaque container for TypeChecker caches that can be saved and restored
/// across TypeChecker instances. Enables cross-call caching within the same
/// goal context without self-referential struct issues.
///
/// Uses `SlidingCache` for generational eviction — see `sliding_cache.rs`.
///
/// Part of #1671: ProofState creates fresh TypeChecker per operation.
#[derive(Default)]
pub struct TcCaches {
    whnf: SlidingCache<Expr, Expr>,
    whnf_core: SlidingCache<Expr, Expr>,
    def_eq: SlidingCache<DefEqCacheKey, bool>,
    proj_type: SlidingCache<Expr, Expr>,
    unfold: SlidingCache<Expr, Expr>,
    equiv: SlidingEquivManager,
    /// Next FVarId counter from the source TypeChecker's LocalContext.
    ///
    /// When injected into a new TypeChecker via `with_mode_and_caches` or
    /// `with_context_and_caches`, the new LocalContext advances its counter
    /// to at least this value. This prevents FVarId collision: without it,
    /// each new TC starts at next_id=0, and cached WHNF/def_eq entries
    /// referencing FVar(0) from TC1 would be misinterpreted in TC2 where
    /// FVar(0) has a different meaning.
    ///
    /// Part of #2382: FVarId-unreachability invariant for batch cache sharing.
    next_fvar_id: u64,
}

impl std::fmt::Debug for TcCaches {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("TcCaches")
            .field("whnf_entries", &self.whnf.len())
            .field("whnf_core_entries", &self.whnf_core.len())
            .field("def_eq_entries", &self.def_eq.len())
            .field("proj_type_entries", &self.proj_type.len())
            .field("unfold_entries", &self.unfold.len())
            .field("next_fvar_id", &self.next_fvar_id)
            .finish()
    }
}

use crate::cache::TypeCheckCache;
use crate::env::{Environment, TransparencyMode};
use crate::expr::Expr;
#[cfg(any(test, kani))]
use crate::expr::ExprKind;
#[cfg(any(test, kani))]
use crate::expr::{BinderInfo, FVarId};
use crate::level::Level;
use crate::mode::CleanMode;
use crate::name::Name;
use crate::tc::branch_sharing::BranchSharingCache;
#[cfg(test)]
pub(crate) use crate::tc::cert::{abstract_fvar_in_expr, convert_fvar_cert_to_bvar};
use crate::tc::def_eq::DefEqCacheKey;
use crate::tc::heartbeat_profiler::HeartbeatProfiler;
use crate::tc::sliding_cache::SlidingCache;
use crate::tc::sliding_equiv_manager::SlidingEquivManager;
use std::cell::{Cell, RefCell};
#[cfg(kani)]
use std::collections::HashMap;

/// Callback for overriding universe level equality during elaboration.
type LevelEqOverride<'env> = Box<dyn Fn(&Level, &Level) -> bool + 'env>;

// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
// Kani: deterministic BuildHasher to avoid RandomState → platform CSPRNG
// ━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━
//
// HashMap::new() uses RandomState which calls the platform CSPRNG
// (CCRandomGenerateBytes on macOS). CBMC must symbolically model this
// entire code path, causing the GOTO binary to exceed memory limits for
// harnesses that construct TypeChecker (5 HashMap fields + EquivManager).
//
// Under cfg(kani), we use KaniBuildHasher which returns the same
// deterministic KaniHasher used elsewhere in the crate. This eliminates
// RandomState from the GOTO binary entirely.
//
// Part of #982: GOTO-too-large harness category.

/// Deterministic BuildHasher for Kani verification.
///
/// Returns `KaniHasher` (multiply-XOR, O(1) per word for CBMC) instead of
/// `SipHasher` (multi-round compression that CBMC cannot efficiently unwind).
#[cfg(kani)]
#[derive(Default, Clone)]
pub(crate) struct KaniBuildHasher;

#[cfg(kani)]
impl std::hash::BuildHasher for KaniBuildHasher {
    type Hasher = crate::expr::KaniHasher;
    fn build_hasher(&self) -> Self::Hasher {
        crate::expr::KaniHasher::new()
    }
}

/// HashMap type alias for TypeChecker caches.
///
/// Production: hashbrown with ahash (faster than SipHash for pre-hashed Expr keys).
/// Expr::hash() is O(1) via pre-computed 32-bit hash in ExprMeta, making SipHash's
/// ~70-cycle init/finalize overhead wasteful. ahash reduces this to ~10 cycles.
/// Part of #2409.
///
/// Kani: HashMap with KaniBuildHasher (deterministic, no platform CSPRNG).
#[cfg(not(kani))]
pub(crate) type TcHashMap<K, V> = hashbrown::HashMap<K, V, ahash::RandomState>;
#[cfg(kani)]
pub(crate) type TcHashMap<K, V> = HashMap<K, V, KaniBuildHasher>;

/// Default maximum entries per TypeChecker cache before sliding window eviction.
/// When a cache's current generation exceeds this threshold, it slides to
/// the previous generation (not dropped). Safe because all TC caches are pure
/// memoization — evicted entries only cause re-computation, never incorrect results.
/// Part of #2410.
const DEFAULT_MAX_CACHE_ENTRIES: usize = 100_000;

/// Process-global override for the per-TypeChecker cache cap.
///
/// Sentinel value `0` means "not overridden — use [`DEFAULT_MAX_CACHE_ENTRIES`]".
/// Any other value `N` is used verbatim as the cap for every freshly-constructed
/// TypeChecker. `usize::MAX` therefore means "effectively unbounded" because no
/// cache can ever reach `usize::MAX` entries, so the sliding-window trim and the
/// branch-sharing clear never fire.
///
/// SOUNDNESS: this knob is purely a performance memo cap. The TC caches are pure
/// memoization (see [`DEFAULT_MAX_CACHE_ENTRIES`] doc): a larger cap only avoids
/// re-computation, it can never change a typecheck result. Raising or lowering it
/// is TCB-neutral — the kernel still performs every reduction and still demands
/// the same definitional-equality proof. Used by `clean check --max-cache-entries`.
static GLOBAL_MAX_CACHE_ENTRIES: std::sync::atomic::AtomicUsize =
    std::sync::atomic::AtomicUsize::new(0);

/// Set the process-global per-TypeChecker cache cap used by all TypeCheckers
/// constructed after this call.
///
/// `cap == 0` resets to the built-in default ([`DEFAULT_MAX_CACHE_ENTRIES`]).
/// Pass `usize::MAX` for an effectively unbounded cache (no eviction).
///
/// SOUNDNESS: TCB-neutral — see [`GLOBAL_MAX_CACHE_ENTRIES`].
pub fn set_global_max_cache_entries(cap: usize) {
    GLOBAL_MAX_CACHE_ENTRIES.store(cap, std::sync::atomic::Ordering::Relaxed);
}

/// The cache cap a freshly-constructed TypeChecker should start with: the
/// process-global override if one was set, otherwise [`DEFAULT_MAX_CACHE_ENTRIES`].
#[must_use]
fn initial_max_cache_entries() -> usize {
    match GLOBAL_MAX_CACHE_ENTRIES.load(std::sync::atomic::Ordering::Relaxed) {
        0 => DEFAULT_MAX_CACHE_ENTRIES,
        n => n,
    }
}

/// Default heartbeat limit for type checking operations.
///
/// Each major operation (whnf, is_def_eq, infer_type) decrements the counter.
/// When it hits zero, `infer_type` / `check_type` / `infer_sort` return
/// `HeartbeatExceeded`.
///
/// A limit of 0 means unlimited.
///
/// Lean 4's *kernel* type checker has no heartbeat limit — the 200K
/// Default heartbeat limit for the type checker.
///
/// Lean 4's kernel uses a cooperative interrupt flag (`check_system`) rather
/// than a deterministic heartbeat counter. Setting this to 0 (unlimited)
/// causes unbounded memory consumption for some Init/Std constants whose
/// WHNF reduction generates enormous intermediate terms.
///
/// 2,000,000 is large enough for all Init+Std constants while preventing
/// runaway reduction. Callers needing different limits can use
/// `set_heartbeat_limit()`. Part of #3134.
pub const DEFAULT_HEARTBEAT_LIMIT: u32 = 2_000_000;

/// Type checker for clean kernel expressions.
///
/// The type checker verifies that expressions are well-typed according to
/// the Calculus of Inductive Constructions. It provides methods for:
/// - Type inference (`infer_type`)
/// - Type checking against an expected type (`check_type`)
/// - Definitional equality (`is_def_eq`)
/// - Weak head normal form reduction (`whnf`)
///
/// # RefCell Borrow Safety (Audit: #1754)
///
/// This struct uses 8 `RefCell` fields for interior mutability (caches + context).
/// `RefCell` panics at runtime on overlapping borrows (`borrow()` while a
/// `borrow_mut()` is alive, or two `borrow_mut()` calls on the same cell).
///
/// **All borrows are confirmed short-lived.** Every borrow site follows one of
/// three safe patterns:
///
/// 1. **Temporary borrow — dropped at semicolon before any recursive call.**
///    Example: `self.ctx.borrow().get(*id).and_then(|d| d.value.clone())`
///    The `Ref<>` is created, the `.get()` + `.clone()` execute, and the
///    temporary is dropped before `whnf_recurse` or `is_def_eq_impl` is called.
///
/// 2. **Block-scoped borrow_mut — dropped at closing brace.**
///    Example: `{ let mut cache = self.whnf_cache.borrow_mut(); cache.insert(...); }`
///    The `RefMut<>` lives only within the block, ensuring it is dropped before
///    any subsequent method call that might re-borrow.
///
/// 3. **Single-expression borrow_mut for cache lookup — dropped before branch.**
///    Example: `if let Some(cached) = self.whnf_cache.borrow_mut().get(e) { return cached; }`
///    The `RefMut<>` temporary is dropped at the semicolon. The `cached` value
///    is an owned `Expr` (cloned inside `get`), so no borrow escapes.
///
/// No borrow guard is held across any call to `whnf_impl`, `is_def_eq_impl`,
/// `infer_type`, or other methods that recursively access TypeChecker caches.
/// This has been verified by manual audit of all ~70 borrow sites across:
/// `whnf.rs`, `infer.rs`, `infer_proj.rs`, `def_eq/mod.rs`, `def_eq/delta.rs`,
/// `def_eq/proof_irrel.rs`, `config.rs`, `cert/infer_core.rs`, `whnf_proof.rs`.
///
/// # Example
///
/// ```
/// use clean_kernel::{Environment, TypeChecker, Expr, ExprKind, Level, Name};
///
/// // Create an empty environment
/// let env = Environment::new();
/// let tc = TypeChecker::new(&env);
///
/// // Type `Prop` (Sort 0) - its type is `Type` (Sort 1)
/// let prop = Expr::sort(Level::zero());
/// let prop_type = tc.infer_type(&prop).expect("Prop is well-typed in any environment");
/// assert!(matches!(prop_type.kind(), ExprKind::Sort(_)));
///
/// // Check definitional equality (reflexivity)
/// assert!(tc.is_def_eq(&prop, &prop));
/// ```
pub struct TypeChecker<'env> {
    /// The environment
    env: &'env Environment,
    /// Local context (interior mutability for push/pop in `&self` methods like `is_def_eq`).
    ///
    /// Borrow safety (#1754): all borrows are single-expression temporaries —
    /// `borrow()` for read (get+clone, is_empty, len), `borrow_mut()` for
    /// push/pop/truncate. No borrow is held across recursive TC calls.
    ctx: RefCell<LocalContext>,
    /// Current mode for type checking
    mode: CleanMode,
    /// Transparency mode for definition unfolding in def-eq and WHNF.
    /// Controls which definitions `lazy_delta_reduction` will unfold:
    /// - `None`: no unfolding at all (`with_unfolding_none`)
    /// - `Reducible`: only `@[reducible]` definitions (instance search)
    /// - `Instances`: reducible + typeclass instances
    /// - `Default`: most definitions except `@[irreducible]`
    /// - `All`: everything including `@[irreducible]` (tactic evaluation)
    ///
    /// Note: In Lean 4 this is a Meta/elaborator concept (`Init/MetaTypes.lean:30`),
    /// not part of the kernel. clean embeds it in the kernel to avoid requiring
    /// the full Meta layer for transparency control.
    /// Part of #1636, #1666.
    transparency: TransparencyMode,
    /// Opt-in elaboration-time reducibility gate (gap-sweep brick B14).
    ///
    /// When `false` — every kernel-internal caller, including `add_decl`'s
    /// trusted final proof re-check — the type checker is transparency-BLIND: it
    /// delta-unfolds every definition that has a value (only genuine
    /// `Opaque`/theorem heads stay folded), exactly matching Lean's kernel, so
    /// its def-eq stays complete. When `true` — set ONLY by the elaborator /
    /// unifier — an `@[irreducible]` definition is NOT delta-unfolded at a
    /// non-`All` transparency, in both WHNF and def-eq, matching MetaM's
    /// `canUnfold` at `.default`.
    ///
    /// Strictly narrowing: enabling the gate can only make elaboration-time
    /// def-eq accept a SUBSET of what it accepted before (a former accept can
    /// turn into a reject, never the reverse). The default (`false`) keeps the
    /// trusted kernel path bit-identical to the pre-B14 behavior.
    honor_reducibility: Cell<bool>,
    /// Cache for full WHNF reduction results (the "reduce cache").
    ///
    /// Matches Lean 4's `m_whnf` cache (`type_checker.h:33`): maps an expression
    /// to its fully-reduced weak head normal form. This is the outermost WHNF
    /// cache — it stores results from the full `whnf()` computation including
    /// the outer delta loop (`whnf_outer_loop`), not just the inner `whnf_core`.
    ///
    /// Contrast with `whnf_core_cache` (Lean 4's `m_whnf_core`) which caches
    /// only no-delta whnf_core results, and `unfold_cache` (Lean 4's `m_unfold`)
    /// which caches only constant definition unfolding.
    ///
    /// The cache is checked in `whnf_inner` before entering `whnf_outer_loop`,
    /// and also checked in `whnf_outer_loop` after delta-unfolding produces a
    /// new intermediate expression (an optimization beyond Lean 4 that
    /// short-circuits chains of definition unfoldings when an intermediate form
    /// was already fully WHNF'd in a prior call).
    ///
    /// Uses sliding window eviction to avoid performance cliffs (Part of #2410).
    /// Cleared via `local_context_mut()` since free variables may have
    /// different meanings after context modification.
    ///
    /// Part of #3210.
    ///
    /// Borrow safety (#1754): lookups use temporary `borrow_mut().get()` (dropped
    /// at semicolon before `whnf_core`); inserts use block-scoped `borrow_mut()`.
    whnf_cache: RefCell<SlidingCache<Expr, Expr>>,
    /// Cache for whnf_core (no-delta) results.
    ///
    /// Matches Lean 4's `m_whnf_core` cache (`type_checker.h:33`). Results are
    /// stored only when `cheap_proj=false` (full projection reduction mode), but
    /// lookups are unconditional — cheap-mode calls benefit from full-mode cached
    /// results since full reduction is strictly more reduced. This prevents
    /// exponential blowup in K-reduction mutual recursion with `is_def_eq`
    /// (e.g., HEq proof terms). Cleared alongside `whnf_cache`.
    ///
    /// Part of #1768, #2410.
    ///
    /// Borrow safety (#1754): same pattern as `whnf_cache` — temporary
    /// `borrow_mut().get()` for lookups, block-scoped `borrow_mut()` for inserts.
    whnf_core_cache: RefCell<SlidingCache<Expr, Expr>>,
    /// Cache for definitional equality results to avoid repeated comparisons.
    ///
    /// Keyed by `DefEqCacheKey` using unordered pair semantics:
    /// - Hash: min/max of expression hashes (commutative, collision-resistant)
    /// - Eq: checks both orderings {a,b} == {c,d} || {a,b} == {d,c}
    ///
    /// This ensures is_def_eq(a,b) and is_def_eq(b,a) share the same cache
    /// entry regardless of memory address (fixes #957, #968).
    ///
    /// Cleared: via `local_context_mut()` since FVar meanings depend on context.
    ///
    /// # Negative result caching and the FVarId-unreachability invariant (#1773)
    ///
    /// Both `true` and `false` results are cached. Caching negative results is
    /// sound because of the **FVarId-unreachability invariant**: FVarIds are
    /// allocated monotonically (`LocalContext::next_id` only increases) and are
    /// never reused after `ctx_pop`. Therefore, after popping an FVar from the
    /// context, no future expression will contain that FVarId as a subterm,
    /// so cached negative results involving popped FVars are unreachable.
    ///
    /// This invariant is validated by `debug_assert!` in `is_def_eq_inner`.
    /// It holds for internal usage within `infer_type` and `is_def_eq_binding_impl`,
    /// but could be violated by external callers reusing expressions containing
    /// stale FVarIds across separate TypeChecker sessions. The `local_context_mut()`
    /// invalidation (which clears all caches) provides a safety net for such cases.
    ///
    /// Performance: O(1) cached hash via expression metadata.
    /// Part of #2410: sliding window eviction.
    ///
    /// Borrow safety (#1754): lookups use temporary `borrow_mut().get()` (dropped
    /// at semicolon); inserts use block-scoped `borrow_mut()`. No borrow held
    /// across `is_def_eq_core` or other recursive calls.
    def_eq_cache: RefCell<SlidingCache<DefEqCacheKey, bool>>,
    /// Per-TypeChecker WHNF memo table used by branch-sharing def-eq on
    /// recursor applications. Stores no-delta WHNF results keyed by the
    /// expression's cached structural hash.
    ///
    /// This cache is separate from `whnf_core_cache` because branch sharing
    /// wants cheap-projection no-delta results for many branch subterms, while
    /// `whnf_core_cache` intentionally only persists `cheap_proj=false` calls.
    branch_sharing_cache: Option<RefCell<BranchSharingCache>>,
    /// Optional cache for type inference results.
    /// Keyed by expression fingerprint + environment state.
    /// When enabled, caches `infer_type()` results for expressions without
    /// free variables (closed terms). Open terms with FVars depend on
    /// local context and cannot be cached without additional context tracking.
    ///
    /// See `crates/clean-kernel/src/cache.rs` and
    /// `designs/2026-01-31-content-addressed-caching.md` for details.
    ///
    /// Borrow safety (#1754): borrows are self-contained in `try_get_cached_type`
    /// and `cache_type_result` (borrow_mut → access → drop). Release-only path.
    type_cache: RefCell<Option<TypeCheckCache>>,
    /// Arc-identity inference memo (Track WW).
    ///
    /// Match lowering (`compile_ctor_dispatch_alt_chain` +
    /// `wrap_with_nested_ctor_caseson_with_fallback`) duplicates an accumulated
    /// "fallback" alternative into every non-matching `casesOn` minor. Because
    /// `Expr` children are `Arc<Expr>` and `Expr::clone` is an `Arc` clone, those
    /// duplicates are the SAME node in memory — the term is linear as a DAG but
    /// EXPONENTIAL when walked as a tree. `infer_type` walks it as a tree, so a
    /// chain of N such patterns made inference (and, in debug builds, the
    /// certificate it drives) take `O(branching^N)`; `semIntBinOp` timed out at
    /// >110s. This memo collapses the walk to linear in DISTINCT `Arc<Expr>` nodes.
    ///
    /// Keyed on `(Arc<Expr> node address, infer_only, ctx_len)`. It is consulted
    /// ONLY from `infer_type_with_cert_arc`, which is given a `&Arc<Expr>` whose
    /// pointee address is STABLE (an interned child of the term, not a transient
    /// stack `Expr`) and whose `Arc` clone is pinned into the memo value — so the
    /// address can never be freed and reused while an entry referencing it lives.
    ///
    /// SOUNDNESS: a node's `(type, cert)` is a pure function of (the node, the
    /// immutable env, the types of the FVars it mentions). FVarIds are never
    /// reused (#1773 — the same invariant that lets `whnf_cache` survive
    /// `ctx_push`/`ctx_pop`). `infer_only` is in the key because it changes which
    /// App/Let def-eq checks run (so an inference-mode result is never served to
    /// the stricter `check_type` traversal); `ctx_len` keys the binder-context
    /// snapshot. The memo is cleared whenever it empties back to the outermost
    /// inference frame (`infer_memo_depth == 0`) and by `local_context_mut`.
    #[allow(clippy::type_complexity)]
    infer_arc_memo: RefCell<
        std::collections::HashMap<
            (usize, bool, usize),
            (std::sync::Arc<Expr>, Expr, crate::cert::ProofCert),
        >,
    >,
    /// Track WW: re-entrancy depth for `infer_arc_memo` (see its doc). When this
    /// returns to 0 the memo is cleared so stale Arc addresses cannot leak into a
    /// later top-level inference call.
    infer_memo_depth: Cell<u32>,
    /// Cache for projection field types keyed by full projection expressions.
    ///
    /// This enables O(1) reuse when multiple projection types for the same
    /// structure expression are requested (for example, structure eta expansion
    /// requesting `proj 0 .. proj n`). Cleared on context/mode/transparency
    /// changes just like WHNF/def-eq caches.
    /// Part of #2410: sliding window eviction.
    ///
    /// Borrow safety (#1754): same pattern as `whnf_cache` — temporary
    /// `borrow_mut().get()` for lookups, block-scoped `borrow_mut()` for inserts.
    /// Batch fill in `cache_projection_field_types_*` uses per-iteration blocks.
    proj_type_cache: RefCell<SlidingCache<Expr, Expr>>,
    /// Cache for constant definition unfolding results.
    ///
    /// Matches Lean 4's `m_unfold` cache (`type_checker.h:31`): maps a
    /// `Const(name, levels)` expression to the result of `unfold_definition`
    /// (environment lookup + universe level substitution). Avoids repeating
    /// the `instantiate_level_params_direct` work when the same constant
    /// appears multiple times during type checking.
    ///
    /// Cache soundness: the unfold result depends only on the environment
    /// (immutable for the TC's lifetime) and the constant expression itself
    /// (name + levels). No dependence on local context or transparency mode
    /// — `unfold_definition` unfolds all non-opaque constants regardless of
    /// reducibility hints (kernel has no transparency modes). The cache is
    /// cleared alongside other caches on mode/transparency changes for
    /// consistency, though it is theoretically invariant to those changes.
    ///
    /// Part of #3210.
    ///
    /// Borrow safety (#1754): same pattern as `whnf_cache` — temporary
    /// `borrow_mut().get()` for lookups, block-scoped `borrow_mut()` for inserts.
    unfold_cache: RefCell<SlidingCache<Expr, Expr>>,
    /// Cache for `try_infer_type_quick` results.
    ///
    /// Matches Lean 4's `m_infer_type` cache (`type_checker.h:30`): the kernel
    /// caches every inference result for the lifetime of the declaration check,
    /// because definitional equality re-infers the SAME subterms once per
    /// def-eq comparison that contains them. The hottest caller is the
    /// proof-irrelevance check, which runs quick inference on both sides of
    /// every `is_def_eq_core` pair: without this cache, checking a proof term
    /// with nested rewrite steps (e.g. the `Eq.mpr` towers in
    /// `Lean.Omega.tidy_sat`) re-infers each subterm once per ancestor path —
    /// quadratic in term size, the kernel performance-parity wall of
    /// 2026-06-12. With it, each distinct subterm is inferred once.
    ///
    /// Cache soundness: a quick-inference result is a pure function of the
    /// expression, the immutable environment, and the types of the FVars it
    /// mentions. FVar types are fixed at `ctx_push` and FVarIds are never
    /// reused after `ctx_pop` (the #1773 FVarId-unreachability invariant that
    /// `whnf_cache`/`def_eq_cache` already rely on), so entries mentioning
    /// popped FVars are simply unreachable. Cleared alongside the other
    /// FVar-sensitive caches on mode/transparency/context changes.
    ///
    /// Borrow safety (#1754): same pattern as `whnf_cache` — temporary
    /// `borrow_mut().get()` for lookups, block-scoped `borrow_mut()` for
    /// inserts.
    quick_infer_cache: RefCell<SlidingCache<Expr, Expr>>,
    /// Optional trace collector for Phase 4 self-verification.
    ///
    /// When set, type inference operations emit `TraceEntry::Infer` entries
    /// to the collector. Use `NullCollector` for zero-overhead disabled state,
    /// or `ThreadedCollector` for trace mode.
    ///
    /// See `crates/clean-kernel/src/cert/trace.rs` for trace format.
    /// Part of #546: Trace-checking format for self-verification.
    trace_collector: Option<crate::cert::SharedTraceCollector>,
    /// Union-find equivalence manager for cross-call definitional equality
    /// caching. Accumulates monotonically within the TypeChecker session.
    /// Cleared on context mutation via `local_context_mut()`.
    ///
    /// # Scope safety (#1773)
    ///
    /// Like `def_eq_cache`, the equiv_manager relies on the FVarId-unreachability
    /// invariant: equivalences recorded for expressions containing FVars from an
    /// inner scope (via `ctx_push`) become unreachable after `ctx_pop` because
    /// FVarIds are never reused. The equiv_manager is NOT cleared on `ctx_push`/
    /// `ctx_pop` (matching Lean 4 behavior), but stale entries involving popped
    /// FVars are harmless since no future expression will reference them.
    ///
    /// Lean 4 reference: `src/kernel/equiv_manager.{h,cpp}`
    /// Part of #1326, #2410: sliding window eviction.
    ///
    /// Borrow safety (#1754): `borrow_mut()` temporaries for `is_equiv()` and
    /// `add_equiv()` — dropped at semicolon before any recursive TC call.
    /// Block-scoped `borrow_mut()` in `is_def_eq()` for trim + add_equiv.
    equiv_manager: RefCell<SlidingEquivManager>,
    /// Maximum entries per cache before sliding window eviction. When a cache's
    /// current generation exceeds this threshold, it slides to the previous
    /// generation and a fresh current starts. Lookups check both generations,
    /// promoting hot entries. Memory bounded at ~2x threshold.
    /// Part of #1780, #2410.
    max_cache_entries: usize,
    /// Optional level equality override for elaborator integration.
    ///
    /// When set, replaces `Level::is_def_eq` in structural/delta comparison
    /// so the elaborator can resolve universe-level metavariables (fresh params)
    /// during kernel type checking. Follows Lean 4's `IsDefEqPred` callback
    /// pattern where the elaborator overrides the kernel's definitional equality.
    ///
    /// Default: `None` (uses `Level::is_def_eq` — pure kernel behavior).
    level_eq_override: Option<LevelEqOverride<'env>>,
    /// Cache for failed `is_def_eq_args_only` comparisons during lazy delta reduction.
    ///
    /// When `lazy_delta_step_equal` finds two constants with equal reducibility
    /// hints and the same head name, it tries `is_def_eq_args_only`. If this
    /// fails, the pair is recorded here so subsequent loop iterations skip the
    /// redundant comparison. Matches Lean 4's `m_failure` cache
    /// (`type_checker.cpp:847-863` `failed_before`/`cache_failure`).
    ///
    /// Uses `SlidingCache` for generational eviction (consistent with other TC
    /// caches). Cleared alongside `def_eq_cache` on context/mode/transparency
    /// changes.
    ///
    /// Part of #1360.
    ///
    /// Borrow safety (#1754): same pattern as `def_eq_cache` — temporary
    /// `borrow_mut().get()` for `args_failed_before`, block-scoped for
    /// `cache_args_failure`. Both in `def_eq/delta.rs`.
    args_failure_cache: RefCell<SlidingCache<DefEqCacheKey, ()>>,
    /// Heartbeat counter for resource limiting.
    ///
    /// Decremented on each major operation (whnf_impl, is_def_eq_impl,
    /// infer_type). When it reaches zero, the next `Result`-returning entry
    /// point (infer_type, check_type, infer_sort) returns `HeartbeatExceeded`.
    ///
    /// Uses `Cell` for interior mutability (same pattern as cache RefCells)
    /// so that `&self` methods can decrement without `&mut self`.
    ///
    /// Lean 4 reference: thread-local `inc_heartbeat()` / `check_heartbeat()`
    /// in `src/runtime/interrupt.h`.
    heartbeat_counter: Cell<u32>,
    /// Maximum heartbeat count. 0 means unlimited (no heartbeat checking).
    ///
    /// Default: `DEFAULT_HEARTBEAT_LIMIT` (0 = unlimited, matching Lean 4 kernel).
    heartbeat_limit: u32,
    /// Optional heartbeat profiler for diagnosing timeout causes.
    ///
    /// When enabled, tracks heartbeat consumption by operation category (whnf,
    /// is_def_eq, infer_type) and by constant name being processed. On timeout,
    /// the profiler provides a breakdown of where the budget was spent.
    ///
    /// Opt-in: `None` by default (zero overhead). Enable via
    /// `enable_heartbeat_profiler()`.
    ///
    /// Borrow safety (#1754): same pattern as other RefCell fields — short-lived
    /// `borrow_mut()` in `tick_heartbeat`/`inc_heartbeat`, dropped before any
    /// recursive TC call.
    ///
    /// Part of #3399.
    profiler: Option<RefCell<HeartbeatProfiler>>,
    /// When true, Nat arithmetic reduction and Bool.true reflection proceed
    /// even when free variables are present.
    ///
    /// Set to `true` by `infer_type` / `infer_type_fast` when the current
    /// application argument is wrapped in the `eagerReduce` marker
    /// (`eagerReduce _ _`). Restored to the previous value after the
    /// `is_def_eq` call returns (RAII via `Cell::set`).
    ///
    /// Lean 4 reference: `m_eager_reduce` flag in `type_checker.h:54`,
    /// set in `type_checker.cpp:168-170`, checked in `type_checker.cpp:978`
    /// and `type_checker.cpp:1066`.
    eager_reduce: Cell<bool>,
    /// Nesting depth of the closed-Nat literal-extraction probe
    /// (`get_nat_bignat_whnf`). Incremented for the dynamic extent of each
    /// probe; when it exceeds `NAT_PROBE_MAX_DEPTH`, `reduce_nat`'s UNARY
    /// `Nat.succ`/`Nat.pred` collapse arms decline, breaking the mutual
    /// recursion tower `probe → whnf → iota (materializes one `Nat.succ`
    /// layer) → whnf-core reduce_nat hook → succ arm → probe(rest) → …`
    /// that otherwise re-derives the whole remaining value at every layer
    /// (Θ(major²) work, Θ(major) native stack on 2^16-scale omega towers —
    /// the Init/GrindInstances/ToInt hang). The outermost probes' iterative
    /// succ-peel loop then consumes the constructor-headed WHNFs in Θ(major)
    /// flat iteration with bit-identical extraction. Depth-keyed only —
    /// never value-thresholded. See `reduction/nat.rs`.
    nat_probe_depth: Cell<u32>,
    /// When true, skip type-checking of application arguments and let-value
    /// types during `infer_type`. This matches Lean 4's `infer_only` parameter
    /// in `infer_type_core(expr, bool infer_only)`.
    ///
    /// Lean 4 reference: `type_checker.cpp:163-196` (App), `type_checker.cpp:198-221` (Let).
    /// - `infer_type()` passes `infer_only=true` — fast inference, skips checks
    /// - `check()` passes `infer_only=false` — full checking at App/Let nodes
    ///
    /// Default: `true` (infer-only mode, matching Lean 4's `infer_type()`).
    /// `check_type()` temporarily sets this to `false` for full checking.
    ///
    /// Part of #3134: clean's infer_type was doing MORE checking than Lean 4,
    /// causing false TypeMismatch errors in Init TC diagnostics.
    infer_only: Cell<bool>,
    /// Allowed universe level parameter names for full checking mode.
    ///
    /// When set and `infer_only=false`, the Sort handler validates that all
    /// `Level::Param` references in the sort's level are in this list.
    /// Matches Lean 4's `m_lparams` field set in `check()`.
    ///
    /// Default: `None` (no level param checking — backward compatible).
    /// Set via `set_level_params()` before calling `check_type()`.
    ///
    /// Part of #3225.
    level_params: Option<Vec<Name>>,
    /// When true, unsafe declarations are allowed in type checking.
    ///
    /// Lean 4 reference: `type_checker.cpp:100-104` — the kernel validates
    /// that unsafe constants are only referenced within unsafe contexts.
    ///
    /// Default: `true` (permissive — backward compatible).
    /// Set to `false` via `set_allow_unsafe(false)` for strict checking.
    ///
    /// Part of #3226.
    allow_unsafe: bool,
    /// When true, partial declarations are allowed in type checking.
    ///
    /// Lean 4 reference: `type_checker.cpp:105-108` — the kernel validates
    /// that partial constants are only referenced within partial contexts.
    ///
    /// Default: `true` (permissive — backward compatible).
    /// Set to `false` via `set_allow_partial(false)` for strict checking.
    ///
    /// Part of #3226.
    allow_partial: bool,
    /// When true, the type checker uses CUMULATIVE subtyping (`is_le`) at
    /// type-ascription points instead of symmetric definitional equality:
    /// `Sort i` is accepted where `Sort j` is expected iff `i ≤ j`, and product
    /// codomains are covariant. This is Coq/pCIC semantics (`Prop ≤ Set ≤ Type`),
    /// used ONLY on the Coq verification lane.
    ///
    /// Default: `false` — Lean-faithful non-cumulative checking (the default and
    /// only behavior for the Lean/olean lane; `is_le` degenerates to `is_def_eq`).
    /// Set via `set_cumulative(true)` when re-verifying Coq-sourced declarations.
    ///
    /// SOUNDNESS: cumulative subtyping is a sound rule of pCIC; enabling it only
    /// ACCEPTS additional terms that are genuinely well-typed under Coq's type
    /// theory, and it is gated off for every non-Coq lane. Tracking: #3300.
    cumulative: bool,
    /// Guard flag to prevent infinite recursion in the debug_assert inside
    /// `infer_type`. The assert calls `infer_type` recursively to check
    /// that the type-of-type is a Sort. Without this guard, the recursive
    /// call triggers the same assert, which calls `infer_type` again, etc.
    ///
    /// Part of #3285.
    #[cfg(debug_assertions)]
    in_infer_type_assert: Cell<bool>,
    /// When true, the certificate produced by the current inference is RETAINED
    /// by the caller (the public `infer_type_with_cert` entry point) and will be
    /// replayed / serialized, so it MUST be structurally complete.
    ///
    /// SOUNDNESS: `infer_type_with_cert_arc` caches a cheap placeholder cert for
    /// later shared-`Arc` (DAG) memo HITS when `infer_only` is set, to avoid an
    /// exponential blow-up in the discarded-cert fast path used by `infer_type`.
    /// That placeholder is only safe when the cert is thrown away. When the cert
    /// is retained (this flag set), the memo must cache the REAL cert so every
    /// occurrence of a shared sub-term replays to its actual expression — without
    /// this, a shared `Not P` argument under two projections would replay as the
    /// placeholder `Sort 0`, corrupting the proof term.
    ///
    /// Default: `false`. Set to `true` for the duration of a public
    /// `infer_type_with_cert` call.
    cert_retained: Cell<bool>,
    /// Expression location tracker for error diagnostics.
    ///
    /// Maintains a breadcrumb trail of `ExprPathStep`s as the type checker
    /// descends into sub-expressions. When an error occurs, the current trail
    /// is snapshotted and attached to the error, giving the user a path from
    /// the declaration root to the problematic sub-expression.
    ///
    /// Uses `RefCell` for interior mutability (same pattern as caches) since
    /// `infer_type` and other `&self` methods need to push/pop steps.
    ///
    /// Performance: only a `Vec` push/pop per expression descent — negligible
    /// compared to the actual type checking work. The `ExprLocation` is only
    /// cloned when errors are created (rare path).
    ///
    /// Part of #3425.
    expr_loc: RefCell<ExprLocation>,
}

impl<'env> TypeChecker<'env> {
    /// Create a new type checker inheriting the environment mode
    ///
    /// # Contract
    ///
    /// REQUIRES: `env` is a valid, consistent environment
    ///
    /// ENSURES: `result.mode() == env.mode()`
    /// ENSURES: `result.local_context().is_empty()` (empty context)
    /// ENSURES: `result.type_cache_enabled() == false` (cache disabled by default)
    /// ENSURES: `result.tracing_enabled() == false` (tracing disabled by default)
    pub fn new(env: &'env Environment) -> Self {
        Self {
            env,
            ctx: RefCell::new(LocalContext::new()),
            mode: env.mode(),
            transparency: TransparencyMode::Default,
            honor_reducibility: Cell::new(false),
            whnf_cache: RefCell::new(Default::default()),
            whnf_core_cache: RefCell::new(Default::default()),
            def_eq_cache: RefCell::new(Default::default()),
            branch_sharing_cache: Some(RefCell::new(Default::default())),
            type_cache: RefCell::new(None),
            infer_arc_memo: RefCell::new(Default::default()),
            infer_memo_depth: Cell::new(0),
            proj_type_cache: RefCell::new(Default::default()),
            unfold_cache: RefCell::new(Default::default()),
            quick_infer_cache: RefCell::new(Default::default()),
            trace_collector: None,
            equiv_manager: RefCell::new(SlidingEquivManager::new()),
            max_cache_entries: initial_max_cache_entries(),
            level_eq_override: None,
            args_failure_cache: RefCell::new(Default::default()),
            heartbeat_counter: Cell::new(DEFAULT_HEARTBEAT_LIMIT),
            heartbeat_limit: DEFAULT_HEARTBEAT_LIMIT,
            profiler: None,
            eager_reduce: Cell::new(false),
            nat_probe_depth: Cell::new(0),
            infer_only: Cell::new(true),
            level_params: None,
            allow_unsafe: true,
            allow_partial: true,
            cumulative: false,
            #[cfg(debug_assertions)]
            in_infer_type_assert: Cell::new(false),
            cert_retained: Cell::new(false),
            expr_loc: RefCell::new(ExprLocation::new()),
        }
    }

    /// Create a type checker with a specific mode
    ///
    /// # Contract
    ///
    /// REQUIRES: `env` is a valid, consistent environment
    /// REQUIRES: `mode` is a valid CleanMode variant
    ///
    /// ENSURES: `result.mode() == mode`
    /// ENSURES: `result.local_context().is_empty()` (empty context)
    /// ENSURES: `result.type_cache_enabled() == false` (cache disabled by default)
    /// ENSURES: `result.tracing_enabled() == false` (tracing disabled by default)
    pub fn with_mode(env: &'env Environment, mode: CleanMode) -> Self {
        Self {
            env,
            ctx: RefCell::new(LocalContext::new()),
            mode,
            transparency: TransparencyMode::Default,
            honor_reducibility: Cell::new(false),
            whnf_cache: RefCell::new(Default::default()),
            whnf_core_cache: RefCell::new(Default::default()),
            def_eq_cache: RefCell::new(Default::default()),
            branch_sharing_cache: Some(RefCell::new(Default::default())),
            type_cache: RefCell::new(None),
            infer_arc_memo: RefCell::new(Default::default()),
            infer_memo_depth: Cell::new(0),
            proj_type_cache: RefCell::new(Default::default()),
            unfold_cache: RefCell::new(Default::default()),
            quick_infer_cache: RefCell::new(Default::default()),
            trace_collector: None,
            equiv_manager: RefCell::new(SlidingEquivManager::new()),
            max_cache_entries: initial_max_cache_entries(),
            level_eq_override: None,
            args_failure_cache: RefCell::new(Default::default()),
            heartbeat_counter: Cell::new(DEFAULT_HEARTBEAT_LIMIT),
            heartbeat_limit: DEFAULT_HEARTBEAT_LIMIT,
            profiler: None,
            eager_reduce: Cell::new(false),
            nat_probe_depth: Cell::new(0),
            infer_only: Cell::new(true),
            level_params: None,
            allow_unsafe: true,
            allow_partial: true,
            cumulative: false,
            #[cfg(debug_assertions)]
            in_infer_type_assert: Cell::new(false),
            cert_retained: Cell::new(false),
            expr_loc: RefCell::new(ExprLocation::new()),
        }
    }

    /// Create a type checker with an existing local context
    ///
    /// # Contract
    ///
    /// REQUIRES: `env` is a valid, consistent environment
    /// REQUIRES: All FVar types in `ctx` are well-typed in `env`
    ///
    /// ENSURES: `result.mode() == env.mode()`
    /// ENSURES: `result.local_context()` contains the entries from `ctx`
    /// ENSURES: `result.type_cache_enabled() == false` (cache disabled by default)
    /// ENSURES: `result.tracing_enabled() == false` (tracing disabled by default)
    pub fn with_context(env: &'env Environment, ctx: LocalContext) -> Self {
        Self {
            env,
            ctx: RefCell::new(ctx),
            mode: env.mode(),
            transparency: TransparencyMode::Default,
            honor_reducibility: Cell::new(false),
            whnf_cache: RefCell::new(Default::default()),
            whnf_core_cache: RefCell::new(Default::default()),
            def_eq_cache: RefCell::new(Default::default()),
            branch_sharing_cache: Some(RefCell::new(Default::default())),
            type_cache: RefCell::new(None),
            infer_arc_memo: RefCell::new(Default::default()),
            infer_memo_depth: Cell::new(0),
            proj_type_cache: RefCell::new(Default::default()),
            unfold_cache: RefCell::new(Default::default()),
            quick_infer_cache: RefCell::new(Default::default()),
            trace_collector: None,
            equiv_manager: RefCell::new(SlidingEquivManager::new()),
            max_cache_entries: initial_max_cache_entries(),
            level_eq_override: None,
            args_failure_cache: RefCell::new(Default::default()),
            heartbeat_counter: Cell::new(DEFAULT_HEARTBEAT_LIMIT),
            heartbeat_limit: DEFAULT_HEARTBEAT_LIMIT,
            profiler: None,
            eager_reduce: Cell::new(false),
            nat_probe_depth: Cell::new(0),
            infer_only: Cell::new(true),
            level_params: None,
            allow_unsafe: true,
            allow_partial: true,
            cumulative: false,
            #[cfg(debug_assertions)]
            in_infer_type_assert: Cell::new(false),
            cert_retained: Cell::new(false),
            expr_loc: RefCell::new(ExprLocation::new()),
        }
    }

    /// Create a type checker with an existing local context and specific mode
    ///
    /// # Contract
    ///
    /// REQUIRES: `env` is a valid, consistent environment
    /// REQUIRES: All FVar types in `ctx` are well-typed in `env`
    /// REQUIRES: `mode` is a valid CleanMode variant
    ///
    /// ENSURES: `result.mode() == mode`
    /// ENSURES: `result.local_context()` contains the entries from `ctx`
    /// ENSURES: `result.type_cache_enabled() == false` (cache disabled by default)
    /// ENSURES: `result.tracing_enabled() == false` (tracing disabled by default)
    pub fn with_context_and_mode(
        env: &'env Environment,
        ctx: LocalContext,
        mode: CleanMode,
    ) -> Self {
        Self {
            env,
            ctx: RefCell::new(ctx),
            mode,
            transparency: TransparencyMode::Default,
            honor_reducibility: Cell::new(false),
            whnf_cache: RefCell::new(Default::default()),
            whnf_core_cache: RefCell::new(Default::default()),
            def_eq_cache: RefCell::new(Default::default()),
            branch_sharing_cache: Some(RefCell::new(Default::default())),
            type_cache: RefCell::new(None),
            infer_arc_memo: RefCell::new(Default::default()),
            infer_memo_depth: Cell::new(0),
            proj_type_cache: RefCell::new(Default::default()),
            unfold_cache: RefCell::new(Default::default()),
            quick_infer_cache: RefCell::new(Default::default()),
            trace_collector: None,
            equiv_manager: RefCell::new(SlidingEquivManager::new()),
            max_cache_entries: initial_max_cache_entries(),
            level_eq_override: None,
            args_failure_cache: RefCell::new(Default::default()),
            heartbeat_counter: Cell::new(DEFAULT_HEARTBEAT_LIMIT),
            heartbeat_limit: DEFAULT_HEARTBEAT_LIMIT,
            profiler: None,
            eager_reduce: Cell::new(false),
            nat_probe_depth: Cell::new(0),
            infer_only: Cell::new(true),
            level_params: None,
            allow_unsafe: true,
            allow_partial: true,
            cumulative: false,
            #[cfg(debug_assertions)]
            in_infer_type_assert: Cell::new(false),
            cert_retained: Cell::new(false),
            expr_loc: RefCell::new(ExprLocation::new()),
        }
    }

    /// Try one native reduction step for the given expression.
    ///
    /// This exposes the kernel's `@[implemented_by]` / built-in native reducer
    /// hook to elaborator-layer evaluation code without requiring a defeq query.
    pub fn try_reduce_native(&self, e: &Expr) -> Option<Expr> {
        self.reduce_native(e)
    }

    /// Set the allowed universe level parameter names for full checking mode.
    ///
    /// When set, Sort expressions will be validated to only reference level
    /// parameters in this list when `infer_only=false` (i.e., during
    /// `check_type` and `infer_sort`).
    ///
    /// Lean 4 reference: `m_lparams` set in `type_checker::check()`.
    ///
    /// Part of #3225.
    pub fn set_level_params(&mut self, params: Vec<Name>) {
        self.level_params = Some(params);
    }

    /// Set whether unsafe declarations are allowed.
    ///
    /// When `false`, references to `unsafe` declarations will cause a
    /// `TypeError::UnsafeDeclaration` error during full checking mode.
    ///
    /// Part of #3226.
    pub fn set_allow_unsafe(&mut self, allow: bool) {
        self.allow_unsafe = allow;
    }

    /// Set whether partial declarations are allowed.
    ///
    /// When `false`, references to `partial` declarations will cause a
    /// `TypeError::PartialDeclaration` error during full checking mode.
    ///
    /// Part of #3226.
    pub fn set_allow_partial(&mut self, allow: bool) {
        self.allow_partial = allow;
    }

    /// Enable/disable CUMULATIVE subtyping (Coq/pCIC semantics) at
    /// type-ascription points. See the `cumulative` field docs. Default `false`
    /// (Lean-faithful non-cumulative). Enable only when re-verifying Coq-sourced
    /// declarations, whose type theory is cumulative (`Prop ≤ Set ≤ Type`).
    pub fn set_cumulative(&mut self, cumulative: bool) {
        self.cumulative = cumulative;
    }

    /// Whether cumulative subtyping is currently enabled.
    #[must_use]
    pub fn is_cumulative(&self) -> bool {
        self.cumulative
    }
}

#[cfg(test)]
impl<'env> TypeChecker<'env> {
    /// Test-only accessor for `reduce_native` to allow unit testing
    /// native reducer integration without reaching through private methods.
    pub(crate) fn reduce_native_for_test(&self, e: &Expr) -> Option<Expr> {
        self.try_reduce_native(e)
    }
}

#[cfg(test)]
mod cache_contracts;
#[cfg(test)]
mod equiv_manager_tests;
#[cfg(kani)]
mod kani_proofs;
#[cfg(test)]
mod micro_tests;
#[cfg(test)]
mod mode_tests;
#[cfg(test)]
mod tests;
#[cfg(test)]
mod tests2;
