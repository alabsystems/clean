// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Pure proof-term → clean kernel `Expr` translator (closure replay).
//!
//! Consumes the parsed [`IsaProvenTheorem`] (see [`super::isabelle_pure`]) and
//! produces a closed clean proof term that clean's own kernel re-checks. The
//! embedding is the standard "HOL-in-CIC" one, made **axiom-free** by
//! quantifying the theorem over its free type and term variables:
//!
//! - HOL `prop`/`bool` → clean `Prop` (`Sort 0`); `Trueprop` is the identity.
//! - HOL `fun` → clean non-dependent `Pi` (`arrow`).
//! - every free object **type** (`TFree`/abstract base type) → a `∀ (T : Type)`
//!   binder, so no opaque type axiom is needed;
//! - every free **term** variable → a `∀ (x : T)` binder.
//! - HOL `=` → clean `Eq`; the base equational axioms (`HOL.refl`,
//!   `Pure.reflexive`, …) map to clean `Eq.refl`/`Eq.symm`/`Eq.trans`/`congr`,
//!   which are constructors/recursor-defined and reduce to **zero** axioms.
//!
//! So e.g. `a = a` (over an abstract type) becomes the closed clean theorem
//! `∀ (T : Type) (a : T), @Eq T a a`, proved by `fun T a => @Eq.refl T a` —
//! kernel-checked with an empty axiom closure. The translator returns the
//! `Declaration::Theorem`; the caller ([`super::isabelle_pure_verify`]) is what
//! actually feeds it to `add_decl` and gates on the axiom closure. Nothing here
//! asserts verification the kernel did not perform.

use std::collections::BTreeMap;

use clean_kernel::expr::FVarId;
use clean_kernel::level::Level;
use clean_kernel::Expr;
#[cfg(test)]
use clean_kernel::{BinderInfo, Declaration, Environment, Name};

use super::isabelle_pure::{IsaProof, IsaProvenTheorem, IsaTerm, IsaType};

mod classes;
mod connectives;
#[cfg(test)]
mod conversep_decode_tests;
mod datatypes;
mod def_axioms;
mod embed;
mod embed_const;
mod embed_const2;
mod embed_term;
#[cfg(test)]
mod premise_budget_tests;
mod proof_terms;
#[cfg(test)]
mod reject_decode_tests;
#[cfg(test)]
mod thmspine_decode_tests;
mod translate;

pub use classes::*;
pub(crate) use connectives::*;
pub use datatypes::*;
pub(crate) use def_axioms::*;
pub(crate) use proof_terms::*;
pub use translate::*;

/// Error translating a Pure proof to a clean `Expr`.
#[derive(Clone, Debug, PartialEq, Eq, thiserror::Error)]
pub enum TranslateError {
    /// A proof leaf we do not yet model (oracle hole, OfClass, …).
    #[error("unverifiable proof node: {0}")]
    Hole(&'static str),
    /// A base axiom with no clean bootstrap mapping yet.
    #[error("unmapped base axiom: {0}")]
    UnmappedAxiom(String),
    /// A `PThm` reference whose clean declaration is not in the closure.
    #[error("unresolved PThm dependency: serial {0}")]
    UnresolvedThm(i64),
    /// A term/type shape we cannot embed yet.
    #[error("unsupported shape: {0}")]
    Unsupported(&'static str),
    /// The env-gated per-theorem translation node budget was exhausted
    /// (`ISA_TRANSLATE_NODE_BUDGET`) — a runaway/pathological recorded proof
    /// (multi-hundred-MB congruence tower) whose translation would grind the
    /// whole corpus replay. An HONEST bounded reject: the theorem is counted
    /// rejected, never mis-verified; unset (the default) means no budget.
    #[error("translate node budget exceeded ({0} nodes)")]
    BudgetExceeded(u64),
    /// The global premise-instantiation search step budget was exhausted
    /// (`ISA_PREMISE_STEP_BUDGET`) — the `prove_from_premises` premise-application
    /// walk (`prove_goal`/`drive_premise`/`beta_normal`) is exponential and, on a
    /// pathological premise shape, effectively unbounded even under its nominal
    /// fuel (the v3.2-grand 5-hour single-line spin). An HONEST *deterministic*
    /// bounded reject — counted rejected, never mis-verified — that mirrors
    /// [`Self::BudgetExceeded`]. The budget is ON by default
    /// ([`PREMISE_STEP_BUDGET_DEFAULT`]); `ISA_PREMISE_STEP_BUDGET=0` opts out.
    #[error("premise-search step budget exceeded ({0} steps)")]
    PremiseBudgetExceeded(u64),
}

/// The per-theorem translation node budget (`None` = unlimited). Reads the
/// **installed [`VerifyConfig`](crate::hol::isabelle_verify_config::VerifyConfig)**
/// for the current run when one is installed (the entry points install it), else
/// falls back to the historical first-read env cache — so an un-instrumented
/// caller is byte-identical and two co-hosted runs no longer share one frozen
/// budget. See [`TranslateError::BudgetExceeded`].
pub(crate) fn translate_node_budget() -> Option<u64> {
    crate::hol::isabelle_verify_config::active_translate_node_budget()
}

/// Default global step budget for ONE `prove_from_premises` premise-instantiation
/// search attempt (env `ISA_PREMISE_STEP_BUDGET`, `0` = unbounded opt-out).
///
/// Unlike the translate-node budget (default OFF/unlimited), this one is ON by
/// default: the premise-application walk ([`proof_terms::premise_instantiation_body`]
/// → `prove_goal`/`drive_premise`) is an exponential search whose nominal fuel
/// does NOT bound a pathological premise shape — the v3.2-grand incident spun a
/// single Extended_Real line at 98.6 % CPU for 5+ hours inside it, losing 39 h of
/// progress. Every `prove_goal`/`drive_premise` invocation across the whole
/// attempt (all recursion, including the `beta_normal` work in the leaves) counts
/// one step against this budget.
///
/// Calibration: the arm's known KV successes are the quantifier trio (`allE`
/// s73810, `exE` s75126, `bspec` s279070 — see
/// `docs/analysis/zproof-quantifier-trio.md`). Their measured peak step counts on
/// the real corpus closures are single digits; this default is set **≥ 100× the
/// max observed** so no legitimate KV line is ever cut, while the exponential
/// exploder is bounded to a fast deterministic reject (`≈` sub-second per attempt).
pub(crate) const PREMISE_STEP_BUDGET_DEFAULT: u64 = 20_000;

/// The active premise-instantiation search step budget (`None` = unbounded).
/// Reads the installed [`VerifyConfig`](crate::hol::isabelle_verify_config::VerifyConfig)
/// when one is installed (every entry point installs it), else the historical
/// first-read env cache (which itself defaults to [`PREMISE_STEP_BUDGET_DEFAULT`]).
/// See [`TranslateError::PremiseBudgetExceeded`].
pub(crate) fn premise_step_budget() -> Option<u64> {
    crate::hol::isabelle_verify_config::active_premise_step_budget()
}

/// Whether the stage-3/4 proof-β-redex higher-order (Miller-pattern) interior
/// operand solve ([`Ctx::redex_premise_solve`]) is enabled. A measurement toggle
/// so a SINGLE binary can produce the pre-stage baseline (redex-lane declines,
/// `ISA_S3_MILLER=0`) and the treatment (`ISA_S3_MILLER=1`) for an
/// apples-to-apples 0-lost KV diff. When disabled the `bidir_redex`-gated block
/// is skipped, so the redex lane behaves exactly as it did pre-stage
/// (byte-identical). Parsed once.
///
/// Default is set by [`S3_MILLER_DEFAULT`]: OFF through stage 3 (0 measured flips
/// on the single-arg fragment), flipped ON in stage 4 once the `nargs=2`
/// imitation + cheap pre-check demonstrate `flips > 0` at acceptable cost (see
/// `docs/analysis/zproof-bidir-s4.md`). `ISA_S3_MILLER` overrides the default in
/// either direction.
pub(crate) const S3_MILLER_DEFAULT: bool = false;
/// Reads the **installed [`VerifyConfig`](crate::hol::isabelle_verify_config::VerifyConfig)**
/// for the current run when one is installed, else the historical first-read env
/// cache (byte-identical for an un-instrumented caller).
pub(crate) fn s3_miller_enabled() -> bool {
    crate::hol::isabelle_verify_config::active_s3_miller_enabled()
}

/// Process-global stage-3/4 Miller instrumentation counters (thread-safe;
/// aggregate across the parallel translation workers). Read once at the end of a
/// streaming run to report the CHEAP PRE-CHECK hit rate — how many candidates the
/// bounded [`crate::hol::isabelle_pure_translate::def_axioms::proofs::head_arity_compatible`]
/// pre-check pruned before the expensive kernel re-check, versus how many were
/// emitted. Instrumentation only; never affects a verdict.
pub(crate) static MILLER_CANDIDATES: std::sync::atomic::AtomicU64 =
    std::sync::atomic::AtomicU64::new(0);
/// Candidates the cheap pre-check rejected (a definite head/arity clash against
/// a flex-premise's actual proposition), avoiding the pathological kernel refute.
pub(crate) static MILLER_PRECHECK_REJECTS: std::sync::atomic::AtomicU64 =
    std::sync::atomic::AtomicU64::new(0);
/// Miller candidates actually EMITTED into `presolution` (passed every guard and
/// the pre-check) — the ones the kernel re-checks.
pub(crate) static MILLER_EMITTED: std::sync::atomic::AtomicU64 =
    std::sync::atomic::AtomicU64::new(0);

/// `(considered, precheck_rejects, emitted)` snapshot of the Miller counters.
pub(crate) fn miller_stats() -> (u64, u64, u64) {
    use std::sync::atomic::Ordering::Relaxed;
    (
        MILLER_CANDIDATES.load(Relaxed),
        MILLER_PRECHECK_REJECTS.load(Relaxed),
        MILLER_EMITTED.load(Relaxed),
    )
}

std::thread_local! {
    /// Per-LINE translation node counter (see [`translate_node_budget`]).
    /// Thread-local so it survives across the driver's five escalating
    /// translate modes for one theorem (each mode builds a fresh [`Ctx`], so a
    /// per-`Ctx` counter would hand a pathological line 5x the budget) and is
    /// reset by the driver at the start of each line
    /// ([`reset_translate_steps`]).
    static TRANSLATE_STEPS: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
    /// Per-LINE **substitution poison** flag. The proof-term β-substitution
    /// helpers ([`proof_terms::subst_pbound0_in_proof`]/[`proof_terms::shift_proof`])
    /// deep-clone whole subtrees per step, so a pathological redex telescope over a
    /// huge proof term costs quadratically — cost the per-node `translate_proof`
    /// budget cannot see (it is inside one substitution call). When such a
    /// substitution's own node budget is exhausted, it sets this flag and stops
    /// recursing (returning a partial tree that is DISCARDED); the enclosing
    /// [`Ctx::translate_redex`] checks the flag and rejects the line as
    /// [`TranslateError::BudgetExceeded`]. Under budget the flag is never set and
    /// behaviour is byte-identical.
    static SUBST_POISON: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
    /// **A/B no-preemption toggle** for the OfClass→membership superclass
    /// projection ([`classes::Ctx::project_ofclass_membership`]). Default `true`
    /// (projection active — the production behaviour). A test flips it OFF to
    /// measure the baseline and assert the anchor closures' KV count is IDENTICAL
    /// either way (the arm only ever flips the co-blocked `contains-free-var`
    /// Orderings family, never a byte of a verifying line). Thread-local, so the
    /// single-threaded closure replay's toggle never races a parallel test.
    static OFCLASS_PROJ_ENABLED: std::cell::Cell<bool> = const { std::cell::Cell::new(true) };
    /// **#107 A/B override** for the `ISA_CLASS_OPERAND_ALIGN` superclass-conjunct
    /// spelling-alignment flag ([`class_operand_align_enabled`]). `None` (the
    /// production default) ⇒ read the installed [`VerifyConfig`]/env value
    /// ([`super::isabelle_verify_config::active_class_operand_align`], default OFF);
    /// `Some(v)` ⇒ force `v`. A test flips it to run the in-process closure A/B
    /// without touching the process-global env (which would race parallel tests).
    /// Thread-local, so the single-threaded closure replay's toggle never races.
    static CLASS_OPERAND_ALIGN_OVERRIDE: std::cell::Cell<Option<bool>> =
        const { std::cell::Cell::new(None) };
    /// Per-ATTEMPT **premise-instantiation search** step counter (see
    /// [`premise_step_budget`]). Reset at the start of each `prove_from_premises`
    /// premise-search ([`proof_terms::premise_instantiation_body`]), it counts
    /// every `prove_goal`/`drive_premise` invocation across the WHOLE recursive
    /// walk for one attempt — the exact metric the exponential blow-up grows.
    static PREMISE_STEPS: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
    /// Per-ATTEMPT premise-search **budget poison**: latched by
    /// [`bump_premise_steps`] once [`PREMISE_STEPS`] passes the budget, so the
    /// deep recursion unwinds cheaply (every subsequent `bump` returns "stop")
    /// instead of finishing an exponential walk. The enclosing
    /// `prove_from_premises_inner` checks it via [`premise_budget_exhausted`] and
    /// rejects the line as [`TranslateError::PremiseBudgetExceeded`]. Reset with
    /// the counter; under budget it is never set and behaviour is byte-identical.
    static PREMISE_POISON: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
    /// Test-only per-LINE peak used to calibrate the production budget.
    #[cfg(test)]
    static PREMISE_STEPS_PEAK: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
}

/// Whether the OfClass→membership superclass projection
/// ([`classes::Ctx::project_ofclass_membership`]) is active (default `true`; only
/// a test's [`set_ofclass_proj_enabled`] flips it — production always reads
/// `true`).
pub(crate) fn ofclass_proj_enabled() -> bool {
    OFCLASS_PROJ_ENABLED.with(std::cell::Cell::get)
}

/// Test-only A/B toggle for [`ofclass_proj_enabled`]. Returns the previous value
/// so a test can restore it. Thread-local, so it only affects the calling
/// thread's (single-threaded) closure replay.
#[cfg(test)]
pub(crate) fn set_ofclass_proj_enabled(v: bool) -> bool {
    OFCLASS_PROJ_ENABLED.with(|c| c.replace(v))
}

/// Whether the #107 superclass-conjunct spelling alignment
/// (`ISA_CLASS_OPERAND_ALIGN`) is active for this translation. A test's
/// [`set_class_operand_align_override`] takes precedence (the in-process A/B);
/// otherwise the installed [`VerifyConfig`]/env value is read (default OFF, so
/// production and every un-overridden test are byte-identical to the pre-flag
/// lane). See
/// [`super::isabelle_verify_config::active_class_operand_align`].
pub(crate) fn class_operand_align_enabled() -> bool {
    match CLASS_OPERAND_ALIGN_OVERRIDE.with(std::cell::Cell::get) {
        Some(v) => v,
        None => super::isabelle_verify_config::active_class_operand_align(),
    }
}

/// Test-only A/B override for [`class_operand_align_enabled`]. `Some(v)` forces
/// the flag; `None` restores the installed-config/env read. Returns the previous
/// override so a test can restore it. Thread-local — only the calling (single-
/// threaded) closure replay is affected.
#[cfg(test)]
pub(crate) fn set_class_operand_align_override(v: Option<bool>) -> Option<bool> {
    CLASS_OPERAND_ALIGN_OVERRIDE.with(|c| c.replace(v))
}

/// RAII guard for the test-only align override: installs a value on construction
/// and RESTORES the prior value on drop — panic-safe, so a test that panics mid
/// A/B cannot leak the override onto cargo's reused pooled thread (the flake the
/// v3.2 census round surfaced). Prefer this over the raw setter in tests.
#[cfg(test)]
pub(crate) struct AlignOverrideGuard(Option<bool>);

#[cfg(test)]
impl AlignOverrideGuard {
    pub(crate) fn set(v: bool) -> Self {
        Self(set_class_operand_align_override(Some(v)))
    }
}

#[cfg(test)]
impl Drop for AlignOverrideGuard {
    fn drop(&mut self) {
        set_class_operand_align_override(self.0);
    }
}

/// Reset the per-LINE translation node counter (and substitution poison). Called
/// by the verify driver at the start of each theorem line, BEFORE any translate
/// mode runs.
pub(crate) fn reset_translate_steps() {
    TRANSLATE_STEPS.with(|c| c.set(0));
    SUBST_POISON.with(|c| c.set(false));
    #[cfg(test)]
    PREMISE_STEPS_PEAK.with(|c| c.set(0));
}

/// Reset the per-ATTEMPT premise-instantiation search counter + poison. Called at
/// the very start of each `prove_from_premises` premise-search
/// ([`proof_terms::premise_instantiation_body`]), so the budget covers exactly ONE
/// attempt (the driver runs several escalation modes per line, each a fresh
/// attempt with its own full budget). Test builds separately accumulate a
/// per-line calibration peak, cleared by [`reset_translate_steps`].
pub(crate) fn reset_premise_steps() {
    PREMISE_STEPS.with(|c| c.set(0));
    PREMISE_POISON.with(|c| c.set(false));
}

/// Consume one unit of the premise-instantiation search budget. Returns `true`
/// while it is OK to keep searching; returns `false` (and latches
/// [`PREMISE_POISON`]) once the per-ATTEMPT counter passes the budget, so the
/// recursive walk unwinds cheaply. A no-op returning `true` when no budget is
/// configured (`ISA_PREMISE_STEP_BUDGET=0`, the zero-cost opt-out). Test builds
/// additionally update a calibration-only per-line peak.
pub(crate) fn bump_premise_steps() -> bool {
    let Some(budget) = premise_step_budget() else {
        return true;
    };
    PREMISE_STEPS.with(|c| {
        let n = c.get() + 1;
        c.set(n);
        #[cfg(test)]
        PREMISE_STEPS_PEAK.with(|p| {
            if n > p.get() {
                p.set(n);
            }
        });
        if n > budget {
            PREMISE_POISON.with(|p| p.set(true));
            false
        } else {
            true
        }
    })
}

/// `Some(budget)` when the premise-instantiation search exhausted its per-attempt
/// budget (see [`bump_premise_steps`]); `None` otherwise. Checked by
/// `prove_from_premises_inner` right after the search declines, to reject the line
/// as [`TranslateError::PremiseBudgetExceeded`] instead of silently falling
/// through — a distinct, honest `premise-budget-cut` reject bucket.
pub(crate) fn premise_budget_exhausted() -> Option<u64> {
    if PREMISE_POISON.with(std::cell::Cell::get) {
        // Poison is only ever latched when a budget is configured.
        premise_step_budget()
    } else {
        None
    }
}

/// The per-LINE **peak** premise-search step count (max reached across the line's
/// attempts since the last [`reset_translate_steps`]). Instrumentation only —
/// read by the calibration test to size [`PREMISE_STEP_BUDGET_DEFAULT`]. Never
/// influences a verdict.
#[must_use]
#[cfg(test)]
pub(crate) fn premise_steps_peak() -> u64 {
    PREMISE_STEPS_PEAK.with(std::cell::Cell::get)
}

/// Consume one unit of the per-LINE translation budget. Returns the exhausted
/// budget when the counter passes it (the caller returns
/// [`TranslateError::BudgetExceeded`]); `None` while within budget or when no
/// budget is configured (zero-cost default path).
pub(crate) fn bump_translate_steps() -> Option<u64> {
    let budget = translate_node_budget()?;
    TRANSLATE_STEPS.with(|c| {
        let n = c.get() + 1;
        c.set(n);
        if n > budget {
            Some(budget)
        } else {
            None
        }
    })
}

/// Consume one unit of the budget from **inside a proof-term substitution**.
/// Returns `true` while it is OK to keep recursing; returns `false` (and latches
/// [`SUBST_POISON`]) once the per-line budget is exhausted, so the substitution
/// helpers unwind cheaply instead of finishing a multi-hour quadratic clone. A
/// no-op returning `true` when no budget is configured (the zero-cost default).
pub(crate) fn subst_step_ok() -> bool {
    let Some(budget) = translate_node_budget() else {
        return true;
    };
    TRANSLATE_STEPS.with(|c| {
        let n = c.get() + 1;
        c.set(n);
        if n > budget {
            SUBST_POISON.with(|p| p.set(true));
            false
        } else {
            true
        }
    })
}

/// `Some(budget)` when a proof-term substitution exhausted the per-line budget
/// this line (see [`subst_step_ok`]); `None` otherwise. Checked by
/// [`Ctx::translate_redex`] after a β-step to reject the line as
/// [`TranslateError::BudgetExceeded`].
pub(crate) fn subst_poison_budget() -> Option<u64> {
    if SUBST_POISON.with(std::cell::Cell::get) {
        // Poison is only ever latched when a budget is configured.
        translate_node_budget()
    } else {
        None
    }
}

/// Object-level HOL types embed at `Sort 1` (clean `Type`); `Eq`/`Eq.refl` over
/// them take this universe level.
pub(crate) fn obj_level() -> Level {
    Level::succ(Level::zero())
}

/// A closure entry: an already-verified clean theorem's kernel name and its
/// (closed) clean type. The type is needed so a later `PThm` reference can
/// reconstruct the **implicit** leading *type* instantiations (clean `∀(T:Type)`
/// binders) that an Isabelle Pure proof term never records in its application
/// spine. See [`Ctx::apply_thm`].
#[derive(Clone, Debug, serde::Serialize, serde::Deserialize)]
pub struct ClosureEntry {
    /// Kernel declaration name (`isabelle.s<serial>`).
    pub name: String,
    /// The verified theorem's closed clean type (its Pi-telescope).
    pub ty: Expr,
    /// The **embedding keys** of the leading object-`Type` binders of [`Self::ty`],
    /// in binder order (outermost first). Each key is the same string
    /// [`Ctx::embed_type`] uses to register a type param — `n` for a `TFree { n }`,
    /// `"{n}.{i}"` for a `TVar { n, i }`. A fully-typed (`zproof`) `PThm` reference
    /// carries explicit `tyinst` entries keyed by `(n, i)`; matching that key to a
    /// position here lets [`Ctx::apply_thm_explicit`] specialize the referenced
    /// theorem's type **directly** (exactly) instead of reconstructing it from the
    /// term spine. Empty for legacy entries (built without recording the params),
    /// in which case the implicit reconstruction path is used unchanged.
    pub type_param_keys: Vec<String>,
    /// The **embedding keys** of the schematic-term-variable binders of
    /// [`Self::ty`] — the `∀(x:T)` binders that immediately follow the leading
    /// `∀(T:Type)` type binders (the quantification order is type params, then
    /// term params, then hypotheses; see `translate_theorem`). Each key is the
    /// term-variable name [`Ctx::term_param`] registers under. A fully-typed
    /// `PThm` reference carries an explicit `tminst` table keyed by `(n, i)` (its
    /// key is the var base name `n`); matching that key to a position here lets the
    /// explicit path fill the term binder DIRECTLY from `tminst`, rather than from
    /// the spine (a bare schematic instantiation supplies its term arguments via
    /// `tminst`, not via the proof spine). Empty for legacy entries.
    pub term_param_keys: Vec<String>,
}

impl ClosureEntry {
    /// A legacy closure entry carrying only the kernel name and closed type, with
    /// no recorded type/term-param keys (so the explicit-instantiation
    /// specialization is not attempted and the implicit reconstruction path runs
    /// unchanged). Used by tests and any caller that does not surface the
    /// discovered params.
    #[must_use]
    pub fn legacy(name: String, ty: Expr) -> Self {
        ClosureEntry {
            name,
            ty,
            type_param_keys: Vec::new(),
            term_param_keys: Vec::new(),
        }
    }
}

/// The closure mapping: `PThm` serial → its verified clean declaration.
pub type Closure = BTreeMap<i64, ClosureEntry>;

/// The `const:` param key for an overloaded/opaque HOL constant `n` at embedded
/// type `ty`, keyed by name **AND** a structural discriminator of `ty`.
///
/// Two occurrences of the SAME constant embed to the SAME shared param IFF their
/// embedded types are structurally identical. This stops one polymorphic constant
/// used at two type instantiations inside a SINGLE theorem (e.g. `Relation.Field`
/// at `α` *and* `β` inside `bij_betw f (Field r) (Field r')`, or the set-lattice
/// `sup`/`Domain`/`Range` ops woven inside `polyinst.Field` at two carriers) from
/// aliasing onto ONE ill-typed param — the recurring two-`Field` poly-inst
/// collision that kernel-rejected the cardinal-arithmetic / wellorder-embedding
/// / cardinal-order families. Within a single instantiation the two embedded
/// types coincide, so every pre-existing single-instantiation reflexivity is
/// byte-preserved (the disc is identical → the same key → the same param).
///
/// The bare constant name is recovered by [`const_key_name`] (the hash is a
/// fixed-width hex suffix after the last `#`, which qualified HOL const names
/// never contain).
pub(crate) fn const_param_key(n: &str, ty: &Expr) -> String {
    use std::hash::{Hash, Hasher};
    let mut h = std::collections::hash_map::DefaultHasher::new();
    ty.hash(&mut h);
    format!("const:{n}#{:016x}", h.finish())
}

/// Recover the bare HOL constant name from a `const:` param key produced by
/// [`const_param_key`] (`const:<n>#<hash>`) — or a legacy bare `const:<n>` key
/// (no `#`). Returns `None` for a non-`const:` key.
pub(crate) fn const_key_name(key: &str) -> Option<&str> {
    key.strip_prefix("const:")
        .map(|rest| rest.rsplit_once('#').map_or(rest, |(name, _)| name))
}

/// Stable `FVarId` for a quantified parameter, namespaced so type and term
/// params never collide.
pub(crate) fn param_fvar(kind: u8, name: &str) -> FVarId {
    // FNV-1a over (kind, name) — deterministic, collision-resistant enough for
    // the per-theorem parameter set.
    let mut h: u64 = 0xcbf2_9ce4_8422_2325;
    h ^= u64::from(kind);
    h = h.wrapping_mul(0x100_0000_01b3);
    for b in name.bytes() {
        h ^= u64::from(b);
        h = h.wrapping_mul(0x100_0000_01b3);
    }
    FVarId::new(h)
}

/// A quantified parameter discovered in the statement/proof.
#[derive(Clone, Debug)]
pub(crate) struct Param {
    pub(crate) fvar: FVarId,
    /// Embedded clean type of the binder (`Type` for a type param, else the
    /// embedded HOL type).
    pub(crate) ty: Expr,
}

/// Translation context: discovered parameters in first-seen order.
#[derive(Default)]
pub(crate) struct Ctx {
    pub(crate) type_params: Vec<(String, Param)>,
    pub(crate) term_params: Vec<(String, Param)>,
    /// Free (undischarged) Pure hypotheses, quantified as `∀ (h : Hprop)` so the
    /// theorem stays closed. Keyed by the embedded hypothesis proposition.
    pub(crate) hyp_params: Vec<(String, Param)>,
    /// Ordered queue of the statement's **leading binders** — the outermost
    /// `Pure.imp` premises (`A ⟹ …`, recovering a raw-proof-body
    /// `AbsP { h: None }`'s discharged hypothesis) and `Pure.all`/`⋀` universal
    /// binders (`⋀x:T. …`, recovering an `Abst { ty: None }`'s bound-variable
    /// *type* that the raw export omits). The statement
    /// `⋀x:T. A₁ ⟹ A₂ ⟹ … ⟹ C` is introduced outermost-first, so the i-th
    /// enclosing proof binder corresponds to the i-th leading binder; we pop from
    /// the front as each outermost `AbsP`/`Abst` is translated. Populated in
    /// [`translate_theorem`] before the proof is walked. The kernel re-checks the
    /// result, so a wrong recovery is rejected (never miscounted).
    pub(crate) premise_queue: std::collections::VecDeque<LeadingBinder>,
    /// Whether we are still on the proof's **outermost leading binder spine** —
    /// the contiguous chain of bare `AbsP`/`Abst` binders at the very top that
    /// mirror the statement's leading-binder chain. Only these consume the
    /// [`Self::premise_queue`]; any binder reached *inside* an application, a
    /// redex argument, or a bare proof argument recovers its omitted type locally
    /// instead (otherwise the single shared queue would desync). Reset to `false`
    /// the moment translation descends into a non-leading position.
    pub(crate) leading_active: bool,
    /// Structured type classes registered so far (`c_class` name → info). When
    /// `embed_term` meets a class-membership application `c_class (TYPE('a))` for
    /// a class present here, it produces the **real membership proposition**
    /// `c_class α ops` (the registered def-const applied to the type and the
    /// class operations) instead of the vacuous `True`. Base sorts (absent here)
    /// stay `True`. Cloned in from the driver's [`ClassRegistry`] per theorem.
    pub(crate) class_registry: ClassRegistry,
    /// Whether to embed a structured class's `OFCLASS('a, c_class)` premise as the
    /// **real membership proposition** `c_class α ops` (`true`) or as the vacuous
    /// `True` (`false`, the default). The driver translates each theorem in two
    /// passes: first with `False` (the historical erasure — most theorems do not
    /// touch the class axioms and verify with it), and only if that kernel-rejects
    /// does it retry with `True` (the faithful membership, which the structured
    /// `c_class.super`/`.axioms`/`.add.assoc`-style projections need). This makes
    /// the membership model strictly *additive*: no theorem the erasure verified is
    /// lost, and the genuinely axiom-using ones are recovered.
    pub(crate) class_membership: bool,
    /// Whether the `OFCLASS('a, c_class)` sort premises embed to `Nonempty α`
    /// (`true`) instead of the vacuous `True` (`false`, the default). This is the
    /// [`ClassMembership::NonemptyErase`] faithfulness-restoring erasure: it runs
    /// ONLY on the dedicated trailing escalation modes (strictly after every
    /// historical mode kernel-rejected), so the stored statement of every
    /// previously-verified line stays byte-identical and the mode can only ADD
    /// verifications. It is mutually exclusive with [`Self::class_membership`]
    /// (`Real`): under `NonemptyErase` structured classes also collapse to the
    /// `Nonempty α` carrier rather than their full membership proposition — the
    /// weakest faithful witness, which is all the vacuous-quantifier / miniscoping
    /// leaves need. The kernel re-checks every term, so a wrong witness is rejected
    /// — never miscounted. Cf. [`Self::class_membership`].
    pub(crate) nonempty_erase: bool,
    /// Overloaded class methods registered so far (`c_class.method` name → info).
    /// When `embed_term` meets an overloaded method constant present here it
    /// produces the **dictionary def-const application** `method_def α impl ops`
    /// (which δ-unfolds to `impl ops`) instead of a fresh opaque `const:` param, so
    /// the method's `…_dict` axiom verifies reflexively. Cloned in from the
    /// driver's [`MethodRegistry`] per theorem. The kernel re-checks every term, so
    /// a wrong dictionary model is rejected — never miscounted.
    pub(crate) method_registry: MethodRegistry,
    /// Whether to **unfold** a registered overloaded method to its dictionary
    /// def-const (`true`) or keep the historical opaque `const:` param (`false`,
    /// the default). The driver translates each theorem first WITHOUT method
    /// unfolding (`false` — the exact historical embedding, so every theorem that
    /// verified before still does), and only if that kernel-rejects does it retry
    /// WITH unfolding (`true`, which the `…_dict`-axiom-using nodes need). This
    /// keeps the dictionary model strictly *additive*: no previously-verified
    /// theorem is lost (the method def-const changes how `c_class.method` embeds
    /// everywhere, which can break nodes that used it opaquely — so it is applied
    /// only as a fallback). Cf. [`Self::class_membership`].
    pub(crate) method_unfold: bool,
    /// Monomorphic ground-type instance operations registered so far, keyed by
    /// `(method-name, ground-type-key)`. When `embed_term` meets an overloaded
    /// method constant at a ground type present here it produces the registered
    /// instance-op def-const (which δ-unfolds to the embedded body of the
    /// operation's `…_def` axiom), so the recursive-arithmetic `…_def` axioms
    /// (`plus_nat_def`, `One_nat_def`, …) verify reflexively and every nat/num
    /// use-site stays consistent. Cloned in from the driver's
    /// [`InstanceOpRegistry`] per theorem.
    pub(crate) instance_op_registry: InstanceOpRegistry,
    /// Whether to **unfold** a registered ground-type instance operation to its
    /// def-const (`true`) or keep the historical opaque `const:` param (`false`,
    /// the default). The driver translates each theorem in escalating passes,
    /// enabling this only on a later pass (so an opaque-pass success is never
    /// displaced — strictly additive, exactly like [`Self::method_unfold`]).
    pub(crate) instance_unfold: bool,
    /// Plain polymorphic list-datatype functions registered so far (function
    /// constant name → info). When `embed_term` meets a registered list function
    /// it produces the def-const applied to the use-site element type
    /// (`@isabelle.listfn.<c> T`, which δ-unfolds to the embedded body), so the
    /// recursive list-function `…_def` axioms (`append_def`, `rev_def`, `map_def`,
    /// …) verify reflexively and every list use-site stays consistent. Cloned in
    /// from the driver's [`ListFnRegistry`] per theorem. Gated by
    /// [`Self::instance_unfold`] (same escalating-pass discipline) so it is
    /// strictly additive — an opaque-pass success is never displaced.
    pub(crate) list_fn_registry: ListFnRegistry,
    /// Polymorphic instance operations registered so far (`c` constant name →
    /// info). When `embed_term` meets a registered polymorphic instance op it
    /// produces the def-const applied to the use-site object type and each class
    /// operation (`@isabelle.polyinst.<c> α op₁ … opₘ`, which δ-unfolds to the
    /// embedded body), so the `_def` axiom verifies reflexively and every use-site
    /// stays consistent. Cloned in from the driver's [`PolyInstRegistry`] per
    /// theorem. Gated by [`Self::instance_unfold`] so it is strictly additive.
    pub(crate) poly_inst_registry: PolyInstRegistry,
    /// Whether the theorem being translated carries a **fully-typed (`zproof`)**
    /// recorded proof — detected by any `Thm`/`Axm` reference carrying a
    /// non-empty explicit `tyinst`/`tminst` table ([`proof_has_inst_tables`]),
    /// which the legacy export never produces. Gates the zproof-only recoveries
    /// (currently the implicit sort-hypothesis `AbsP` elision) so the legacy
    /// translation paths stay byte-identical (the round-6 gate protocol).
    pub(crate) zproof_mode: bool,
    /// The statement's leading `⟹` premise TERMS (the `Hyp` entries of
    /// [`Self::premise_queue`] at translation start), kept un-consumed for the
    /// implicit sort-hypothesis elision test: an `AbsP` hypothesis that occurs
    /// ANYWHERE in this list is SPELLED by the statement and must keep its
    /// lambda, even when the proof has already left the leading spine (a root
    /// redex clears [`Self::leading_active`], so the queue front alone cannot
    /// decide spelled-ness there).
    pub(crate) stmt_premises: Vec<IsaTerm>,
    /// Whether **box-internal-free → statement-schematic param aliasing** is
    /// active (see [`Self::term_param_free`] / [`Self::type_param_free`]).
    /// `translate_theorem` enables it ONLY while the recorded PROOF VALUE is
    /// translated: the statement (and every stored-type override) embeds with it
    /// OFF, so the stored theorem type is byte-identical to the historical
    /// embedding and a wrong aliasing can only make the VALUE kernel-reject —
    /// never change what is stated.
    pub(crate) alias_frees: bool,
    /// Whether the **namespace-crossed root lane**
    /// ([`Ctx::try_root_sort_absp_expecting`]) and the membership-witness
    /// re-spelling `PBound` arm are active. `false` (the default) keeps every
    /// historical translation path byte-identical; the driver enables it ONLY
    /// on the dedicated trailing escalation modes ([`RootLane::On`]), which run
    /// strictly AFTER every historical mode kernel-rejected — so the lane can
    /// only ADD verifications, never displace one (the binder-order round's
    /// measured `<c>_class.axioms` regression when the lane pre-empted a
    /// previously-verifying plain translation within a shared mode).
    pub(crate) root_lane: bool,
    /// Whether this pass SKIPS the recorded proof and runs only the
    /// statement-level fallback arms ([`RootLane::StmtFallback`] — the
    /// trailing escalation modes that reproduce the historical
    /// unresolved-reference fallback behaviour).
    pub(crate) stmt_fallback: bool,
    /// Whether **recursive expectation propagation over the equational-tower
    /// fragment** ([`RootLane::BidirEqTower`]) is active. `false` (the default)
    /// keeps every historical translation path byte-identical; the driver
    /// enables it ONLY on the dedicated trailing escalation modes
    /// ([`RootLane::BidirEqTower`]), which run strictly AFTER every historical
    /// mode (and the other trailing lanes) kernel-rejected — so it can only ADD
    /// verifications, never displace one.
    ///
    /// When set, the proof ROOT of an equational-tower shape
    /// ([`eq_tower_applicable`]) is translated bidirectionally against the
    /// embedded statement ([`Ctx::translate_proof_expecting`]) — the statement
    /// expectation then propagates recursively down through every interior
    /// `equal_elim`/`transitive`/`symmetric`/`combination`/`reflexive`/`AbsP`/
    /// `Abst`/`AppT`/`AppP` node, pinning each operand by its EXPECTED TYPE
    /// rather than by the recorded (crossed-namespace) instantiation table (the
    /// free-vs-schematic operand-desync root defect the reject census decoded).
    /// It also unlocks the `bidir_tower`-gated `equal_elim`-under-expectation
    /// arm in [`Ctx::translate_proof_expecting`].
    pub(crate) bidir_tower: bool,
    /// Whether the **proof-β-redex discharge-chain** sub-lane's higher-order
    /// (Miller-pattern) interior operand solve is active (bidir stage 3).
    /// `false` (the default) everywhere — including the equational-tower lane
    /// ([`Ctx::bidir_tower`]), so the stage-1 `+5`/`+84` eq-tower gains stay
    /// BYTE-IDENTICAL. The driver's root routing sets it `true` for the
    /// duration of the SINGLE redex-lane call
    /// ([`thm_spine_root_applicable`] branch in `translate_theorem`) only, so
    /// the Miller solve is reachable exclusively from that sub-lane's interior
    /// `subst`/`ssubst`-family `Thm` legs.
    ///
    /// When set, [`Ctx::apply_thm_expecting_solved`] runs a
    /// premise-driven + Miller-pattern operand solve
    /// ([`Ctx::redex_premise_solve`]) for a leg whose bare conclusion is
    /// **flex-headed** (`?P ?t …` — an unsolved predicate sentinel applied to
    /// arguments, the shape the strictly first-order `unify_sentinels` cannot
    /// recover); every rigid-conclusion leg stays byte-identical even under
    /// this flag. The kernel re-checks the assembled application, so a wrong
    /// HO solve is rejected — never miscounted.
    pub(crate) bidir_redex: bool,

    /// Count of stage-3 Miller predicate solves performed in the CURRENT root's
    /// redex-lane translation (reset to `0` alongside each `bidir_redex = true`).
    /// [`Ctx::redex_premise_solve`] declines once this reaches
    /// `MILLER_MAX_SOLVES_PER_ROOT`, so a DEEP discharge chain (many interior
    /// `subst` legs) produces at most that many Miller-solved legs — the rest
    /// fall back to the phantom-param path, which the kernel type-errors EARLY.
    /// This bounds the pathological case where an "almost-right" many-leg root
    /// candidate is expensive for the kernel to reduce/refute (measured:
    /// multi-CPU-minute roots on the reject tail), while leaving the genuine
    /// SHORT discharge-chain flips (few legs) untouched. Kernel-re-checked, so a
    /// wrong bound only declines a solve — never miscounts.
    pub(crate) redex_miller_solves: usize,
}

/// Whether the namespace-crossed root expectation lane (and its
/// membership-witness re-spelling) is active for a translation pass. See
/// [`Ctx::root_lane`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RootLane {
    /// Historical translation paths only (byte-identical to the pre-lane
    /// pipeline).
    Off,
    /// Root lane + membership-witness re-spelling enabled (the trailing
    /// escalation modes).
    On,
    /// **Statement-fallback** pass: skip the recorded proof entirely and run
    /// only the statement-level fallback arms (`prove_from_premises`, the
    /// definitional-reflexivity short-circuit) — the exact path the
    /// historical pipeline took when a recorded proof FAILED to translate.
    /// Appended as the LAST escalation modes: a node whose reference to a
    /// lane-recovered dependency now translates-but-kernel-rejects (at HEAD
    /// the unresolved reference errored and the fallback verified — the
    /// measured `old.sum.case`/`old.prod.case`/`HOL.Let_folded` former-KV
    /// regression) still ends at the same fallback derivation, so resolving
    /// a new dependency can only ADD verifications. Kernel-re-checked like
    /// every arm.
    StmtFallback,
    /// **Recursive expectation propagation over the equational-tower fragment**
    /// (bidir stage 1): translate the recorded proof ROOT bidirectionally
    /// against the embedded statement so the expectation propagates recursively
    /// down every interior `equal_elim`/`transitive`/`symmetric`/`combination`/
    /// `reflexive`/`AbsP`/`Abst`/`AppT`/`AppP` node — pinning each operand by its
    /// EXPECTED TYPE instead of by the recorded (crossed-namespace) instantiation
    /// table. Enabled only for structural candidates ([`eq_tower_applicable`]),
    /// and appended as the LAST trailing modes: it runs strictly after every
    /// historical mode and the `On`/`StmtFallback` lanes kernel-rejected, so it
    /// can only ADD verifications. The assembled term is kernel-re-checked
    /// against the stored statement, so a wrong recovery is rejected — never
    /// miscounted. See [`Ctx::bidir_tower`].
    BidirEqTower,
}

/// Whether a theorem's `OFCLASS` premises embed to the real membership
/// proposition or the vacuous `True`. See [`Ctx::class_membership`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ClassMembership {
    /// `OFCLASS('a, c_class)` → `True` (historical erasure).
    Erase,
    /// `OFCLASS('a, c_class)` → `c_class α ops` for registered structured classes.
    Real,
    /// `OFCLASS('a, c_class)` → `Nonempty α` (the **faithfulness-restoring** erasure).
    ///
    /// The historical [`Erase`](Self::Erase) spelling drops HOL's universal
    /// type-nonemptiness guarantee: every HOL type is inhabited by axiom, and the
    /// bare `OFCLASS('a, type)` "is-a-type" witness is exactly that guarantee. Erasing
    /// it to `True` **strengthens** the stored statement — it deletes a premise the
    /// conclusion genuinely uses — which makes the vacuous-quantifier simp laws
    /// (`(∀x. P) = P`, `(∃x. P) = P`) and the `∧`-miniscoping conjuncts of `all_simps`
    /// *false as embedded* over a possibly-empty Clean sort (the root of the 63%
    /// `simp_thms` reject ceiling — see `docs/analysis/zproof-conj-bundles.md`).
    ///
    /// This mode restores the premise as `Nonempty α` (the weakest faithful carrier:
    /// every HOL sort membership entails nonemptiness, `type_class` being the
    /// weakest), from which `Classical.choice` mints the quantifier witness. It runs
    /// as a **trailing escalation mode** (strictly after every historical mode), so
    /// the stored statement of every previously-verified line stays byte-identical and
    /// this mode can only ADD verifications. The kernel re-checks the assembled proof
    /// against the `Nonempty`-spelled statement, so a wrong discharge rejects — never
    /// miscounts. Consumers that reference a dependency accepted under this spelling
    /// carry (or discharge) the same `Nonempty α` premise themselves. See
    /// [`Ctx::nonempty_erase`].
    NonemptyErase,
}

/// Whether a registered overloaded class method embeds to its dictionary
/// def-const (unfolding) or to the historical opaque `const:` param. See
/// [`Ctx::method_unfold`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MethodEmbed {
    /// `c_class.method` → opaque `const:c_class.method` param (historical).
    Opaque,
    /// `c_class.method` → `method_def α impl ops` (δ-unfolds to its dictionary
    /// form), making the method's `…_dict` axiom reflexive.
    DictUnfold,
}

/// Whether a registered monomorphic ground-type instance operation (and the nat
/// base constructors) embed to their def-const / clean constructor (unfolding) or
/// to the historical opaque `const:` param. See [`Ctx::instance_unfold`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum InstanceEmbed {
    /// `c_class.method@ground` → opaque `const:c_class.method` param (historical).
    Opaque,
    /// `c_class.method@ground` → its instance def-const (`isabelle.inst.<c>@<k>`),
    /// δ-unfolding to the operation's body, making the recursive-arithmetic
    /// `…_def` axiom reflexive and every nat/num use-site consistent.
    Unfold,
}

/// One leading binder of a statement (see [`Ctx::premise_queue`]): either a
/// `Pure.imp` premise term (consumed by an `AbsP { h: None }`) or the
/// bound-variable type of a `Pure.all`/`⋀` universal binder (consumed by an
/// `Abst { ty: None }`).
#[derive(Clone, Debug)]
pub(crate) enum LeadingBinder {
    /// A `Pure.imp` premise (`A ⟹ …`).
    Hyp(IsaTerm),
    /// A `Pure.all (λx:T. …)` / `⋀x:T.` bound-variable type.
    AllTy(IsaType),
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::env::is_foundational_axiom;
    use clean_kernel::Environment;

    /// Real-shaped equational theorem `a = a` (a : abstract type), proved by
    /// reflexivity — exercised end-to-end through clean's kernel.
    const AEQA: &str = r#"{"name":"Demo.a_eq_a","prop":{"k":"App","f":{"k":"Const","n":"HOL.Trueprop","t":{"k":"Type","n":"fun","a":[{"k":"Type","n":"HOL.bool","a":[]},{"k":"Type","n":"prop","a":[]}]}},"a":{"k":"App","f":{"k":"App","f":{"k":"Const","n":"HOL.eq","t":{"k":"Type","n":"fun","a":[{"k":"TFree","n":"'a"},{"k":"Type","n":"fun","a":[{"k":"TFree","n":"'a"},{"k":"Type","n":"HOL.bool","a":[]}]}]}},"a":{"k":"Free","n":"a","t":{"k":"TFree","n":"'a"}}},"a":{"k":"Free","n":"a","t":{"k":"TFree","n":"'a"}}}},"proof":{"k":"appt","f":{"k":"axm","name":"HOL.refl"},"a":{"k":"Free","n":"a","t":{"k":"TFree","n":"'a"}}}}"#;

    /// REAL Isabelle output: `(a::'a) ≡ a` proved by `Thm.reflexive`, exported
    /// from a live `record_proofs=2` session via `export_pure_proofs.ML` and
    /// expanded to its `PAxm Pure.reflexive` leaf. This is not synthetic — it is
    /// verbatim what Isabelle emits.
    const REAL_REFL_PURE: &str = r#"{"name":"Demo.refl_pure","prop":{"k":"App","f":{"k":"App","f":{"k":"Const","n":"Pure.eq","t":{"k":"Type","n":"fun","a":[{"k":"TFree","n":"'a"},{"k":"Type","n":"fun","a":[{"k":"TFree","n":"'a"},{"k":"Type","n":"prop","a":[]}]}]}},"a":{"k":"Free","n":"a","t":{"k":"TFree","n":"'a"}}},"a":{"k":"Free","n":"a","t":{"k":"TFree","n":"'a"}}},"proof":{"k":"appt","f":{"k":"axm","name":"Pure.reflexive"},"a":{"k":"Free","n":"a","t":{"k":"TFree","n":"'a"}}}}"#;

    /// REAL Isabelle output: `(a::'a) == b ==> b == a` via `Thm.symmetric`,
    /// exported from a live record_proofs=2 session. Exercises Hyp handling (the
    /// free hypothesis `a == b` is quantified) and the `Pure.symmetric` bootstrap.
    const REAL_SYM_PURE: &str = r#"{"name":"Demo.sym_pure","prop":{"k":"App","f":{"k":"App","f":{"k":"Const","n":"Pure.eq","t":{"k":"Type","n":"fun","a":[{"k":"TFree","n":"'a"},{"k":"Type","n":"fun","a":[{"k":"TFree","n":"'a"},{"k":"Type","n":"prop","a":[]}]}]}},"a":{"k":"Free","n":"b","t":{"k":"TFree","n":"'a"}}},"a":{"k":"Free","n":"a","t":{"k":"TFree","n":"'a"}}},"proof":{"k":"appp","f":{"k":"appt","f":{"k":"appt","f":{"k":"axm","name":"Pure.symmetric"},"a":{"k":"Free","n":"a","t":{"k":"TFree","n":"'a"}}},"a":{"k":"Free","n":"b","t":{"k":"TFree","n":"'a"}}},"a":{"k":"hyp","p":{"k":"App","f":{"k":"App","f":{"k":"Const","n":"Pure.eq","t":{"k":"Type","n":"fun","a":[{"k":"TFree","n":"'a"},{"k":"Type","n":"fun","a":[{"k":"TFree","n":"'a"},{"k":"Type","n":"prop","a":[]}]}]}},"a":{"k":"Free","n":"a","t":{"k":"TFree","n":"'a"}}},"a":{"k":"Free","n":"b","t":{"k":"TFree","n":"'a"}}}}}}"#;

    /// Raw-proof-body shape: `P ⟹ P` whose proof is a null-hypothesis `AbsP`
    /// (`{"k":"absp"}` with no `h`, as the raw export emits) wrapping `PBound 0`.
    /// The discharged hypothesis term is recovered from the statement's leading
    /// `Pure.imp` premise, yielding `fun (h : P) => h : P → P`, which the kernel
    /// re-checks. Exercises the null-hyp `AbsP` premise recovery directly.
    const NULL_ABSP_IMP_SELF: &str = r#"{"name":"Demo.imp_self","prop":{"k":"App","f":{"k":"App","f":{"k":"Const","n":"Pure.imp","t":{"k":"Type","n":"fun","a":[]}},"a":{"k":"App","f":{"k":"Const","n":"HOL.Trueprop","t":{"k":"Type","n":"fun","a":[]}},"a":{"k":"Free","n":"P","t":{"k":"Type","n":"HOL.bool","a":[]}}}},"a":{"k":"App","f":{"k":"Const","n":"HOL.Trueprop","t":{"k":"Type","n":"fun","a":[]}},"a":{"k":"Free","n":"P","t":{"k":"Type","n":"HOL.bool","a":[]}}}},"proof":{"k":"absp","b":{"k":"bound","i":0}}}"#;

    #[test]
    fn kernel_verifies_null_hyp_absp_via_statement_premise() {
        let thm = super::super::isabelle_pure::parse_proven_theorem(NULL_ABSP_IMP_SELF)
            .expect("parse null-hyp absp shape");
        // The parser must record the AbsP with no hypothesis term.
        assert!(
            matches!(&thm.proof, IsaProof::AbsP { h: None, .. }),
            "fixture must be a null-hypothesis AbsP"
        );
        let decl = translate_theorem(
            &thm,
            &BTreeMap::new(),
            &BTreeMap::new(),
            &BTreeMap::new(),
            &BTreeMap::new(),
            &BTreeMap::new(),
            &BTreeMap::new(),
            ClassMembership::Erase,
            MethodEmbed::Opaque,
            InstanceEmbed::Opaque,
        )
        .expect("translate null-hyp AbsP via recovered statement premise");
        let mut env = Environment::with_prelude();
        env.add_decl(decl)
            .expect("kernel must accept fun (h:P) => h : P → P");
        let deps = env
            .axiom_deps(&Name::from_string("Demo.imp_self"))
            .expect("decl present");
        assert!(
            deps.iter().all(is_foundational_axiom),
            "P → P must reduce to foundational axioms, got: {deps:?}"
        );
    }

    #[test]
    fn kernel_verifies_real_isabelle_pure_symmetric_export() {
        let thm = super::super::isabelle_pure::parse_proven_theorem(REAL_SYM_PURE)
            .expect("parse real symmetric export");
        let decl = translate_theorem(
            &thm,
            &BTreeMap::new(),
            &BTreeMap::new(),
            &BTreeMap::new(),
            &BTreeMap::new(),
            &BTreeMap::new(),
            &BTreeMap::new(),
            ClassMembership::Erase,
            MethodEmbed::Opaque,
            InstanceEmbed::Opaque,
        )
        .expect("translate real symmetric");
        let mut env = Environment::with_prelude();
        env.add_decl(decl)
            .expect("clean's kernel must accept the real Isabelle symmetry proof");
        let deps = env
            .axiom_deps(&Name::from_string("Demo.sym_pure"))
            .expect("decl present");
        assert!(
            deps.iter().all(is_foundational_axiom),
            "real Pure.symmetric proof must reduce to foundational axioms, got: {deps:?}"
        );
    }

    #[test]
    fn kernel_verifies_real_isabelle_pure_reflexive_export() {
        let thm = super::super::isabelle_pure::parse_proven_theorem(REAL_REFL_PURE)
            .expect("parse real Isabelle export");
        let decl = translate_theorem(
            &thm,
            &BTreeMap::new(),
            &BTreeMap::new(),
            &BTreeMap::new(),
            &BTreeMap::new(),
            &BTreeMap::new(),
            &BTreeMap::new(),
            ClassMembership::Erase,
            MethodEmbed::Opaque,
            InstanceEmbed::Opaque,
        )
        .expect("translate real proof");

        let mut env = Environment::with_prelude();
        env.add_decl(decl)
            .expect("clean's kernel must accept the real Isabelle reflexivity proof");

        let deps = env
            .axiom_deps(&Name::from_string("Demo.refl_pure"))
            .expect("decl present");
        assert!(
            deps.iter().all(is_foundational_axiom),
            "real Pure.reflexive proof must reduce to the foundational axioms, got: {deps:?}"
        );
    }

    #[test]
    fn translates_and_kernel_verifies_a_eq_a_axiom_free() {
        let thm = super::super::isabelle_pure::parse_proven_theorem(AEQA).expect("parse");
        let decl = translate_theorem(
            &thm,
            &BTreeMap::new(),
            &BTreeMap::new(),
            &BTreeMap::new(),
            &BTreeMap::new(),
            &BTreeMap::new(),
            &BTreeMap::new(),
            ClassMembership::Erase,
            MethodEmbed::Opaque,
            InstanceEmbed::Opaque,
        )
        .expect("translate");

        // The kernel must accept the proof: value : type.
        let mut env = Environment::with_prelude();
        env.add_decl(decl).expect("kernel must accept a = a proof");

        // And its axiom closure must be ⊆ the three foundational axioms (here:
        // empty — Eq.refl is a constructor).
        let deps = env
            .axiom_deps(&Name::from_string("Demo.a_eq_a"))
            .expect("decl present in env");
        assert!(
            deps.iter().all(is_foundational_axiom),
            "a = a must reduce to the foundational axioms, got: {deps:?}"
        );
    }

    /// `if_literal_branch` selects the THEN branch for a literal `HOL.True`
    /// condition, the ELSE branch for a literal `HOL.False`, and `None` for an
    /// abstract condition — the faithful `if_True`/`if_False` denotation.
    #[test]
    fn if_literal_branch_selects_the_named_branch() {
        let dummy = IsaType::Type {
            n: "dummy".into(),
            a: vec![],
        };
        let cst = |n: &str| IsaTerm::Const {
            n: n.into(),
            t: dummy.clone(),
        };
        let app = |f: IsaTerm, a: IsaTerm| IsaTerm::App {
            f: Box::new(f),
            a: Box::new(a),
        };
        let else_branch = cst("ELSE");

        // `if_literal_branch` takes the partial spine `f = ((head $ cond) $ then)`
        // and the outer else operand. Build `f` for a given head/condition.
        let spine = |head: IsaTerm, cond: IsaTerm| app(app(head, cond), cst("THEN"));

        // if True → THEN
        let f_true = spine(cst("HOL.If"), cst("HOL.True"));
        match if_literal_branch(&f_true, &else_branch) {
            Some(IsaTerm::Const { n, .. }) => assert_eq!(n, "THEN"),
            other => panic!("if True must pick THEN, got {other:?}"),
        }

        // if False → ELSE
        let f_false = spine(cst("HOL.If"), cst("HOL.False"));
        match if_literal_branch(&f_false, &else_branch) {
            Some(IsaTerm::Const { n, .. }) => assert_eq!(n, "ELSE"),
            other => panic!("if False must pick ELSE, got {other:?}"),
        }

        // if <abstract Free condition> → None (routes through the def-const).
        let abstract_cond = IsaTerm::Free {
            n: "c".into(),
            t: dummy.clone(),
        };
        let f_abstract = spine(cst("HOL.If"), abstract_cond);
        assert!(
            if_literal_branch(&f_abstract, &else_branch).is_none(),
            "abstract condition must not collapse to a branch"
        );

        // A non-`HOL.If` head → None.
        let f_other = spine(cst("Other.const"), cst("HOL.True"));
        assert!(
            if_literal_branch(&f_other, &else_branch).is_none(),
            "non-HOL.If head must not be treated as an if"
        );
    }

    /// A polymorphic reflexivity `?x ≡ ?x` (the closure dependency a fully-typed
    /// reference specializes). Proof: the `Pure.reflexive` axiom applied to `?x`.
    const POLY_REFL: &str = r#"{"name":"isabelle.s200","serial":200,"prop":{"k":"App","f":{"k":"App","f":{"k":"Const","n":"Pure.eq","t":{"k":"Type","n":"fun","a":[{"k":"TVar","n":"'a","i":0},{"k":"Type","n":"fun","a":[{"k":"TVar","n":"'a","i":0},{"k":"Type","n":"prop","a":[]}]}]}},"a":{"k":"Var","n":"x","i":0,"t":{"k":"TVar","n":"'a","i":0}}},"a":{"k":"Var","n":"x","i":0,"t":{"k":"TVar","n":"'a","i":0}}},"proof":{"k":"appt","f":{"k":"axm","name":"Pure.reflexive"},"a":{"k":"Var","n":"x","i":0,"t":{"k":"TVar","n":"'a","i":0}}}}"#;

    /// The fully-typed explicit-instantiation path ([`Ctx::apply_thm_explicit`]):
    /// a `PThm` reference carrying `tyinst`/`tminst` specializes the referenced
    /// theorem DIRECTLY. We translate the polymorphic dependency `∀(T)(x:T), x ≡ x`,
    /// record its closure entry with the leading-binder keys the verifier records,
    /// then drive the explicit path with a `nat`/`b` instantiation and an empty
    /// spine (a bare schematic reference). The produced proof must be the **applied
    /// dependency constant** `@isabelle.s200 Nat b` — proving the explicit tables
    /// (not the term spine) supplied both the type and the term argument — and
    /// clean's kernel must accept it (`@Eq Nat b b` after the dep is registered).
    ///
    /// Driving `apply_thm_explicit` directly (rather than the whole-theorem path)
    /// avoids the statement-level reflexivity short-circuit that would otherwise
    /// prove a `b ≡ b` *statement* without ever consulting the dependency.
    #[test]
    fn explicit_tyinst_tminst_specializes_dependency_directly() {
        use super::super::isabelle_pure::{IsaTermInst, IsaType, IsaTypeInst};
        use clean_kernel::expr::ExprKind;

        let dep = super::super::isabelle_pure::parse_proven_theorem(POLY_REFL).expect("parse dep");
        let (dep_decl, meta) = translate_theorem_with_meta(
            &dep,
            &Closure::new(),
            &BTreeMap::new(),
            &BTreeMap::new(),
            &BTreeMap::new(),
            &BTreeMap::new(),
            &BTreeMap::new(),
            ClassMembership::Erase,
            MethodEmbed::Opaque,
            InstanceEmbed::Opaque,
        )
        .expect("translate polymorphic dependency");
        // The dependency exposes a leading `Type` binder (schematic `'a`, index 0)
        // and a term binder (schematic `x`, index 0) — the keys the explicit path
        // matches `tyinst`/`tminst` against. Both schematic vars register under the
        // `"{n}.{i}"` key (see `embed_type`/`embed_term`).
        assert_eq!(meta.type_param_keys, vec!["'a.0".to_string()]);
        assert_eq!(meta.term_param_keys, vec!["x.0".to_string()]);

        let Declaration::Theorem {
            type_: dep_ty,
            value: dep_val,
            ..
        } = dep_decl
        else {
            panic!("dependency is a theorem");
        };
        // Register the dependency in the kernel under its closure name.
        let mut env = Environment::with_prelude();
        env.add_decl(Declaration::Theorem {
            name: Name::from_string("isabelle.s200"),
            level_params: Vec::new(),
            type_: dep_ty.clone(),
            value: dep_val,
        })
        .expect("kernel accepts the polymorphic dependency");

        // Build the closure entry exactly as the verifier does.
        let mut closure = Closure::new();
        closure.insert(
            200,
            ClosureEntry {
                name: "isabelle.s200".to_string(),
                ty: dep_ty,
                type_param_keys: meta.type_param_keys,
                term_param_keys: meta.term_param_keys,
            },
        );
        let entry = closure.get(&200).expect("dep entry").clone();

        // The explicit instantiation tables: `'a := nat`, `x := (b::nat)`.
        let nat = IsaType::Type {
            n: "Nat.nat".into(),
            a: vec![],
        };
        let b = IsaTerm::Free {
            n: "b".into(),
            t: nat.clone(),
        };
        let tyinst = vec![IsaTypeInst {
            n: "'a".into(),
            i: 0,
            ty: nat,
        }];
        let tminst = vec![IsaTermInst {
            n: "x".into(),
            i: 0,
            t: b,
        }];

        // Drive the explicit path with an EMPTY spine (a bare schematic reference):
        // the type and term arguments must come from the tables, not the spine.
        let mut ctx = Ctx::default();
        let mut binders: Vec<Binder> = Vec::new();
        let value = ctx
            .apply_thm_explicit(&entry, &tyinst, &tminst, &[], &closure, &mut binders)
            .expect("explicit path runs")
            .expect("explicit path handles the fully-typed reference");

        // The result must be the dependency constant applied to the explicit type
        // and term args (`@isabelle.s200 Nat b`) — proving the tables supplied both.
        let mut head = value.clone();
        let mut nargs = 0usize;
        while let ExprKind::App(f, _) = head.kind() {
            head = (**f).clone();
            nargs += 1;
        }
        assert!(
            matches!(head.kind(), ExprKind::Const(n, _) if *n == Name::from_string("isabelle.s200")),
            "explicit path must apply the dependency constant, got head {head:?}"
        );
        assert_eq!(nargs, 2, "exactly the type arg + the term arg are applied");

        // The kernel must accept the specialized reference as a proof of `b ≡ b`
        // (`@Eq Nat b b`), quantified over the free `b`.
        let b_fvar = param_fvar(1, "b");
        let nat_ty = Expr::const_str("Nat");
        let b_e = Expr::fvar(b_fvar);
        let eq_bb = Expr::apps(
            Expr::const_str_levels("Eq", vec![obj_level()]),
            [nat_ty.clone(), b_e.clone(), b_e],
        );
        let ty = Expr::pi(
            BinderInfo::Default,
            nat_ty.clone(),
            eq_bb.abstract_fvar(b_fvar),
        );
        let proof = Expr::lam(BinderInfo::Default, nat_ty, value.abstract_fvar(b_fvar));
        env.add_decl(Declaration::Theorem {
            name: Name::from_string("Demo.uses_explicit"),
            level_params: Vec::new(),
            type_: ty,
            value: proof,
        })
        .expect("kernel accepts the explicitly-specialized reference: ∀(b:Nat), b ≡ b");
    }

    /// Register every def-const the point-free defs depend on (`True`/`conj` plus
    /// the six point-free constants themselves), returning a prelude env.
    fn pointfree_env() -> Environment {
        let mut env = Environment::with_prelude();
        for decl in connective_definition_decls() {
            env.add_decl(decl).expect("connective def-const");
        }
        for decl in pointfree_definition_decls() {
            env.add_decl(decl).expect("point-free def-const");
        }
        env
    }

    /// Translate a reconstructed point-free `…_def_raw` equation through the SAME
    /// escalating passes the verifier uses (`verify_one`): try each mode, register
    /// the produced decl in a fresh point-free env, and return the FIRST decl clean's
    /// kernel accepts (the final `Unfold` pass is what makes the def-const-backed
    /// constants reflexive). Returns the accepted `(type, value)` pair.
    fn translate_pointfree(thm: &IsaProvenTheorem) -> (Expr, Expr) {
        let modes = [
            (
                ClassMembership::Erase,
                MethodEmbed::Opaque,
                InstanceEmbed::Opaque,
            ),
            (
                ClassMembership::Real,
                MethodEmbed::DictUnfold,
                InstanceEmbed::Unfold,
            ),
        ];
        let mut last: Option<String> = None;
        for (m, me, ie) in modes {
            let decl = match translate_theorem(
                thm,
                &BTreeMap::new(),
                &BTreeMap::new(),
                &BTreeMap::new(),
                &BTreeMap::new(),
                &BTreeMap::new(),
                &BTreeMap::new(),
                m,
                me,
                ie,
            ) {
                Ok(d) => d,
                Err(e) => {
                    last = Some(format!("{e:?}"));
                    continue;
                }
            };
            let Declaration::Theorem { type_, value, .. } = &decl else {
                continue;
            };
            let mut env = pointfree_env();
            let probe = Declaration::Theorem {
                name: Name::from_string("Demo.pf_probe"),
                level_params: Vec::new(),
                type_: type_.clone(),
                value: value.clone(),
            };
            match env.add_decl(probe) {
                Ok(()) => return (type_.clone(), value.clone()),
                Err(e) => last = Some(format!("kernel-reject: {e:?}")),
            }
        }
        panic!("point-free def translation failed: {last:?}");
    }

    /// End-to-end: each reconstructed point-free `…_def_raw` equation
    /// (`raw_def_prop`, the shape both the theorem-level and leaf paths embed)
    /// translates to a clean proof clean's kernel accepts with a **foundational-only**
    /// axiom closure — the faithful `C ≡ (λargs. body)`, never a `body = body`
    /// tautology. Covers the def-const-reflexive constants and the `All` funext
    /// bridge over an abstract object type `'a`.
    #[test]
    fn pointfree_def_raw_equations_kernel_verify_foundational() {
        use super::super::isabelle_pure::{IsaProof, IsaProvenTheorem, IsaType, IsaTypeInst};

        let alpha = IsaType::TVar {
            n: "'a".to_string(),
            i: 0,
        };
        let beta = IsaType::TVar {
            n: "'b".to_string(),
            i: 0,
        };
        // Every point-free constant (`All` = funext bridge; the rest = def-const
        // reflexive). `raw_def_prop` reconstructs exactly the raw axiom equation; the
        // proof is the constant's own `…_def_raw` axm leaf (a non-hole placeholder —
        // the point-free arm proves the statement directly, ignoring the recorded
        // proof, so the leaf is never translated here).
        for name in [
            "HOL.All",
            "HOL.Ex",
            "HOL.Uniq",
            "HOL.Ex1",
            "HOL.Let",
            "HOL.induct_forall",
            "HOL.induct_equal",
            "HOL.NO_MATCH",
        ] {
            let prop =
                raw_def_prop(name, &alpha, &beta).unwrap_or_else(|| panic!("reconstruct {name}"));
            let thm = IsaProvenTheorem {
                name: format!("Demo.pf_{}", name.replace('.', "_")),
                serial: 0,
                prop,
                proof: IsaProof::Axm {
                    name: format!("{name}_def_raw"),
                    tyinst: vec![IsaTypeInst {
                        n: "'a".to_string(),
                        i: 0,
                        ty: alpha.clone(),
                    }],
                    tminst: Vec::new(),
                },
            };
            let (ty, value) = translate_pointfree(&thm);
            // FAITHFULNESS: the def-const-backed constants (`Uniq`/`Ex1`/`Let`/
            // `induct_forall`/`induct_equal`/`NO_MATCH`) store `@Eq T (def-const …)
            // (embedded body)` — structurally DISTINCT operands (the def-const
            // application vs its unfolded body), never a reflexive `B = B`; `HOL.All`
            // stores the distinct `λP. ∀x. P x` vs `λP. P = λx.True`. `HOL.Ex` is the
            // one exception: bare `HOL.Ex` embeds INLINE to `ex_encoding` (the
            // established `ex_def_predicate` semantics — `HOL.Ex` has no distinct def
            // symbol), so its LHS and the embedded body coincide; that reflexive form
            // is the project's accepted embedding of `Ex_def`, not a tautology arm.
            if name != "HOL.Ex" {
                assert!(
                    eq_operands_distinct(&ty),
                    "{name}: stored equation must have distinct operands (no B=B tautology): {ty:?}"
                );
            }
            let decl_name = Name::from_string(&format!("Demo.pf_{}", name.replace('.', "_")));
            let mut env = pointfree_env();
            env.add_decl(Declaration::Theorem {
                name: decl_name.clone(),
                level_params: Vec::new(),
                type_: ty.clone(),
                value,
            })
            .unwrap_or_else(|e| panic!("{name}: kernel must accept the point-free proof: {e:?}"));
            let deps = env
                .axiom_deps(&decl_name)
                .unwrap_or_else(|| panic!("{name}: decl present"));
            assert!(
                deps.iter().all(is_foundational_axiom),
                "{name}: proof must reduce to foundational axioms, got: {deps:?}"
            );
        }
    }

    /// The leaf path ([`Ctx::prove_pointfree_def_raw_leaf`], driven through
    /// `bootstrap_axiom`) yields the SAME faithful, kernel-accepted proof: build a
    /// consumer whose proof is the bare `HOL.Uniq_def_raw` `axm` leaf (tyinst `'a`)
    /// and check it verifies against the reconstructed equation type.
    #[test]
    fn pointfree_def_raw_leaf_reference_kernel_verifies() {
        use super::super::isabelle_pure::{IsaProof, IsaProvenTheorem, IsaType, IsaTypeInst};

        let alpha = IsaType::TVar {
            n: "'a".to_string(),
            i: 0,
        };
        // Statement: the reconstructed `HOL.Uniq ≡ λP. ∀x y. P x → P y → x = y`.
        let prop = raw_def_prop("HOL.Uniq", &alpha, &alpha).expect("reconstruct Uniq");
        // Proof: the bare `HOL.Uniq_def_raw` axm leaf carrying `'a` in `tyinst`.
        let proof = IsaProof::Axm {
            name: "HOL.Uniq_def_raw".to_string(),
            tyinst: vec![IsaTypeInst {
                n: "'a".to_string(),
                i: 0,
                ty: alpha.clone(),
            }],
            tminst: Vec::new(),
        };
        let thm = IsaProvenTheorem {
            name: "Demo.uniq_leaf".to_string(),
            serial: 0,
            prop,
            proof,
        };
        let (ty, value) = translate_pointfree(&thm);
        assert!(
            eq_operands_distinct(&ty),
            "leaf Uniq equation must have distinct operands: {ty:?}"
        );
        let decl_name = Name::from_string("Demo.uniq_leaf");
        let mut env = pointfree_env();
        env.add_decl(Declaration::Theorem {
            name: decl_name.clone(),
            level_params: Vec::new(),
            type_: ty.clone(),
            value,
        })
        .expect("kernel must accept the leaf-reconstructed Uniq_def_raw proof");
        let deps = env.axiom_deps(&decl_name).expect("decl present");
        assert!(
            deps.iter().all(is_foundational_axiom),
            "leaf Uniq_def_raw proof must be foundational, got: {deps:?}"
        );
    }

    /// Whether a `Pi`-telescoped `@Eq α lhs rhs` conclusion has structurally
    /// distinct `lhs`/`rhs` operands (a faithful equation, not a `B=B` tautology).
    fn eq_operands_distinct(ty: &Expr) -> bool {
        use clean_kernel::expr::ExprKind;
        let mut concl = ty.clone();
        while let ExprKind::Pi(_, _, cod) = concl.kind() {
            concl = (**cod).clone();
        }
        // concl = @Eq α lhs rhs = App(App(App(Eq, α), lhs), rhs)
        let ExprKind::App(eq_a_lhs, rhs) = concl.kind() else {
            return false;
        };
        let ExprKind::App(_eq_a, lhs) = eq_a_lhs.kind() else {
            return false;
        };
        format!("{lhs:?}") != format!("{rhs:?}")
    }
}
