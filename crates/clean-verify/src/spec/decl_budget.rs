// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The per-declaration runaway guard for specification construction.
//!
//! # What was disconnected
//!
//! `clean_kernel::tc` has carried an ambient, declaration-scoped cooperative
//! budget since `d935d692e` — [`set_declaration_budget`], the latch
//! [`declaration_budget_exhausted`], and the typed
//! `TypeError::DeclarationBudgetExhausted` it raises. `clean check` armed it.
//! **`Specification::new()` never did**, so the single most expensive routine
//! in this crate — the one every spec-paying test target pays before its first
//! test line — ran with no bound at all.
//!
//! The consequence is measured, not hypothetical. `ir_f64_w_fin_renormalise`
//! (`spec/core_spec/eval_ir_float_fin_witnesses.rs:103`, the binary64
//! maximum-cancellation witness) stopped terminating when a nat-probe ordering
//! bug poisoned the shared whnf cache: **100% CPU with flat RSS for 7h48m**,
//! no output, no diagnostic, and every spec-paying target in the suite wedged
//! behind it. The cause is written up at
//! `crates/clean-kernel/src/tc/reduction/nat.rs:628` and is fixed; what was not
//! fixed is that the *class* had no floor. A hang is the worst failure mode
//! this repo has, because it is indistinguishable from slow work and it
//! consumes a whole lane before anyone learns the name of the declaration.
//!
//! # What arming it does, and what it does not
//!
//! It converts a *non-terminating* declaration into a **named, typed failure**
//! at a finite bound: `SpecError::DeclarationBudgetExhausted` carrying the
//! declaration's own name and the limit it spent.
//!
//! It does **not** make the spec faster, does not bound wall time, and does not
//! detect every pathology. The bound is a TICK COUNT, spent at the cooperative
//! sites the kernel already ticks (`infer_type`, `whnf_impl`, `is_def_eq_impl`,
//! and `cert::infer_core`). A runaway that spins *between* ticks — the module
//! doc of `clean_kernel::tc::decl_budget` names allocation-size pathologies as
//! one such class — is not bounded by this and this module claims otherwise
//! nowhere. Whether the specific 7h48m hang above ticked has NOT been
//! re-measured (its cause is repaired, so it cannot be replayed here).
//!
//! # The number, and why it is an argument rather than a guess
//!
//! [`DEFAULT_SPEC_DECL_BUDGET`] is `1e11`. **The heaviest declaration of the
//! full specification has NOT been measured** — that needs a complete
//! `Specification::new()`, which is ~985 s in-process at ~28.7 GB peak RSS and
//! does not fit this machine's gate budget. So the bound is not chosen by
//! measuring the maximum; it is chosen so that it CANNOT fire on a build that
//! terminates:
//!
//! **The structural bound.** The budget is refilled per declaration, so one
//! declaration's ticks are at most the ticks of the WHOLE build. A
//! per-declaration limit above the whole build's total therefore cannot fire on
//! any terminating build, whatever the distribution across declarations.
//!
//! **What that total is, from two measurements and one division.**
//!
//! * `CoreSpecBundle::EvalIr`, measured 2026-08-28 with the trace below
//!   (`cargo test -p clean-verify --test evalir_scratchpad`), TWICE: **763**
//!   registered declarations both times, max **362,826**
//!   (`ir_lzb_max_true_seg`) — identical in both runs — bundle total
//!   **2,081,303** and **2,115,691** ticks, median **610** and **646**. The
//!   ~1.6% spread between runs is worth knowing: the per-declaration count is
//!   NOT bit-reproducible across builds even though the mechanism is
//!   deterministic per input, so read these as a scale, not a fixed point. The
//!   build was reported at 0.1 s — call it ~2.1e7 ticks/second for a debug
//!   build on this box.
//! * A full `Specification::new()` is recorded at **984.6 s** in-process
//!   (`data/gate_registry.json`, `clean-verify::test::premise_witness_gate`).
//! * 984.6 s x ~2.1e7 ticks/s ~= **2e10 ticks for the entire full-spec build**.
//!
//! `1e11` is ~5x that estimated whole-build total, ~276,000x the measured
//! heaviest EvalIR declaration, and ~12,900x the heaviest declaration in
//! `reports/decl-budget-calibration.json` (7,727,977 ticks over 136 real
//! declarations including a Mathlib file). The `clean check` default
//! (`clean_kernel::cli::DEFAULT_DECL_BUDGET`, `2e9`) is 50x smaller; this one is
//! deliberately looser because the corpus underneath it is less measured.
//!
//! **What that costs when it does fire:** at ~2.1e7 ticks/s, spending `1e11`
//! takes on the order of **80 minutes**. That is the price of the margin, and
//! it is the right side of the trade — the incident this replaces ran **7h48m**
//! and would have run indefinitely.
//!
//! **What is still owed.** Replace the estimate with a census:
//!
//! ```text
//! CLEAN_SPEC_DECL_BUDGET_TRACE=1 cargo test --locked -p clean-verify --test evalir_scratchpad
//! CLEAN_SPEC_DECL_BUDGET_TRACE=1 cargo test --locked -p clean-verify --test spec_scratchpad
//! ```
//!
//! Each prints `spec-decl-budget\t<declaration>\t<ticks>` on stderr for every
//! declaration the build registers; the second one is the full spec and needs a
//! `scripts/heavy_gate.sh` slot sized for it. The maximum over that run is the
//! floor an honest default must clear — the same method
//! `scripts/decl_budget_calibrate.sh` used for the CLI default. Until it is run,
//! `1e11` is a bound with an argument, not a measurement.
//!
//! A lane doing genuinely heavier work overrides it:
//!
//! ```text
//! CLEAN_SPEC_DECL_BUDGET=1000000000000  # raise it
//! CLEAN_SPEC_DECL_BUDGET=0              # unlimited (the pre-2026-08-28 behaviour)
//! ```
//!
//! # Nothing new is added to the kernel
//!
//! Every primitive used here — `set_declaration_budget`,
//! `reset_declaration_budget`, `clear_declaration_budget`,
//! `declaration_budget_used`, `declaration_budget_limit`,
//! `declaration_budget_exhausted` — already existed and is already public. This
//! module is wiring, not new trusted-core surface.
//!
//! [`set_declaration_budget`]: clean_kernel::tc::set_declaration_budget
//! [`declaration_budget_exhausted`]: clean_kernel::tc::declaration_budget_exhausted

use super::SpecError;

/// Environment variable that overrides [`DEFAULT_SPEC_DECL_BUDGET`].
///
/// `0` disables the mechanism entirely (unlimited), which is what spec
/// construction did before this module existed.
pub(crate) const SPEC_DECL_BUDGET_ENV: &str = "CLEAN_SPEC_DECL_BUDGET";

/// Environment variable that turns on per-declaration tick tracing.
///
/// Set to `1` to print `spec-decl-budget <declaration> <ticks>` on stderr after
/// every registered declaration. This is the measuring instrument for the
/// census the default is still missing — see the module docs.
pub(crate) const SPEC_DECL_BUDGET_TRACE_ENV: &str = "CLEAN_SPEC_DECL_BUDGET_TRACE";

/// Ticks granted to one specification declaration.
///
/// `1e11`. Read the module docs before changing it: the number is chosen to sit
/// ABOVE the estimated total tick cost of a whole `Specification::new()`
/// (~2e10), so that it structurally cannot fire on a build that terminates —
/// not by measuring the heaviest declaration, which is still unmeasured. It is
/// also ~276,000x the heaviest declaration of the EvalIR bundle (362,826 ticks,
/// measured 2026-08-28) and ~12,900x the heaviest in
/// `reports/decl-budget-calibration.json` (7,727,977 ticks).
pub(crate) const DEFAULT_SPEC_DECL_BUDGET: u64 = 100_000_000_000;

/// The budget this process will arm, from the environment or the default.
///
/// A malformed override is a hard error rather than a silent fallback: a
/// mistyped budget that quietly reverts to the default is the shape of bug
/// where a lane believes it raised a limit and did not.
///
/// # Errors
/// Returns `SpecError::ParseError` if the override is set but not a `u64`.
pub(crate) fn configured_budget() -> Result<u64, SpecError> {
    match std::env::var(SPEC_DECL_BUDGET_ENV) {
        Err(_) => Ok(DEFAULT_SPEC_DECL_BUDGET),
        Ok(raw) => raw.trim().parse::<u64>().map_err(|e| {
            SpecError::ParseError(format!(
                "{SPEC_DECL_BUDGET_ENV}={raw:?} is not a u64 tick count ({e}); \
                 use a decimal number of kernel operations, or 0 for unlimited"
            ))
        }),
    }
}

fn trace_enabled() -> bool {
    std::env::var(SPEC_DECL_BUDGET_TRACE_ENV).is_ok_and(|v| v == "1")
}

/// Run `f` with the per-declaration budget armed for spec construction, and
/// disarm it on the way out.
///
/// The budget is thread-local and spec construction is synchronous, so this
/// scopes it to exactly the bundle being built. Disarming matters because the
/// in-process test harness reuses threads: leaving a limit armed would apply it
/// to unrelated later work.
///
/// **It never touches a budget somebody else armed.** The kernel's public API
/// can set a limit but cannot restore a PARTLY SPENT counter
/// (`set_declaration_budget` writes limit and remaining together), so re-arming
/// inside an enclosing armed declaration and "restoring" afterwards would
/// REFILL that declaration's fuel — the exact escape hatch
/// `with_declaration_budget_suspended` documents itself as not opening. So when
/// a budget is already armed, the owner above us is left in charge and `f` runs
/// under their bound. Nothing in this repo reaches `Specification::new()` from
/// inside an armed declaration today (`clean check` is the only production
/// arm-er, and it never builds a specification), so this is a guard against a
/// future caller rather than a live case — and it is also why the environment
/// override is documented as applying to the outermost arming only.
///
/// # Errors
/// Propagates `f`'s error, or `SpecError::ParseError` if the environment
/// override is malformed.
pub(crate) fn with_spec_declaration_budget<T>(
    f: impl FnOnce() -> Result<T, SpecError>,
) -> Result<T, SpecError> {
    if clean_kernel::tc::declaration_budget_limit() != 0 {
        return f();
    }
    let limit = configured_budget()?;
    let _scope = SpecDeclBudgetScope::enter(limit);
    f()
}

/// Arms the ambient budget for one spec build and disarms it on drop,
/// including on unwind.
///
/// Only constructed when the thread's budget was disabled, so `clear` restores
/// the previous state exactly.
struct SpecDeclBudgetScope;

impl SpecDeclBudgetScope {
    fn enter(limit: u64) -> Self {
        clean_kernel::tc::set_declaration_budget(limit);
        Self
    }
}

impl Drop for SpecDeclBudgetScope {
    fn drop(&mut self) {
        clean_kernel::tc::clear_declaration_budget();
    }
}

/// Refill the budget for one declaration. Call immediately before registering.
pub(crate) fn begin_declaration() {
    clean_kernel::tc::reset_declaration_budget();
}

/// Close out one declaration: trace its cost, then let the latch override the
/// registration's own verdict.
///
/// Asked AFTER the fact and unconditionally, for the same reason `clean check`
/// asks it that way (`cmd_core.rs:892`): the ambient budget LATCHES, so even if
/// the kernel's typed `DeclarationBudgetExhausted` was swallowed by an
/// intermediate layer and the declaration reported an ordinary pass or an
/// ordinary failure, the latch still says the work was cut short. "Did not
/// finish" wins over both — exhaustion is information, never a verdict.
///
/// # Errors
/// Returns `SpecError::DeclarationBudgetExhausted` if the declaration spent its
/// whole budget; otherwise returns `outcome` unchanged.
pub(crate) fn finish_declaration<T>(
    declaration: &str,
    outcome: Result<T, SpecError>,
) -> Result<T, SpecError> {
    if trace_enabled() {
        let spent = clean_kernel::tc::declaration_budget_used();
        eprintln!("spec-decl-budget\t{}\t{spent}", label(declaration));
    }
    if clean_kernel::tc::declaration_budget_exhausted() {
        return Err(SpecError::DeclarationBudgetExhausted {
            declaration: label(declaration),
            limit: clean_kernel::tc::declaration_budget_limit(),
        });
    }
    outcome
}

/// One-line identifier for a declaration in a trace row or an error.
///
/// `add_definition` labels with the declaration's own name, but `add_inductive`
/// and `add_recursive_def` label with their `description`, and in this crate a
/// description is routinely a paragraph — the heaviest row of the EvalIR census
/// carries 640 characters of prose. A census line and an error message both
/// have to stay readable, so the label is cut at the first line break and
/// bounded; the useful part (the declaration name) is at the front.
fn label(declaration: &str) -> String {
    const MAX: usize = 120;
    let first_line = declaration.lines().next().unwrap_or("").trim();
    if first_line.chars().count() <= MAX {
        return first_line.to_string();
    }
    let cut: String = first_line.chars().take(MAX).collect();
    format!("{cut}…")
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The default must keep every margin the module docs claim for it. A
    /// number nobody can re-derive from a committed measurement is a guess
    /// wearing a comment.
    #[test]
    fn test_default_budget_keeps_the_margins_the_docs_claim() {
        // reports/decl-budget-calibration.json, 2026-08-27, `max_ticks`: the
        // heaviest of 136 real declarations, including a Mathlib file.
        const MEASURED_MATHLIB_MAX_TICKS: u64 = 7_727_977;
        // The heaviest declaration of the EvalIR spec bundle, measured
        // 2026-08-28 with CLEAN_SPEC_DECL_BUDGET_TRACE=1 over 763 declarations
        // (`ir_lzb_max_true_seg`).
        const MEASURED_EVALIR_MAX_TICKS: u64 = 362_826;
        // The ESTIMATED total tick cost of a whole `Specification::new()`:
        // 984.6 s in-process (data/gate_registry.json, premise_witness_gate) at
        // the ~2.1e7 ticks/s the EvalIR census measured on this box. An
        // estimate, not a measurement — see the module docs.
        const ESTIMATED_FULL_SPEC_TOTAL_TICKS: u64 = 20_000_000_000;

        assert!(
            DEFAULT_SPEC_DECL_BUDGET / MEASURED_MATHLIB_MAX_TICKS >= 12_000,
            "the spec budget must stay a loose ceiling over the measured \
             per-declaration maximum, not a tight one"
        );
        assert!(
            DEFAULT_SPEC_DECL_BUDGET / MEASURED_EVALIR_MAX_TICKS >= 275_000,
            "…and a much looser one over the heaviest SPEC declaration measured \
             so far, because the full spec's maximum is still unmeasured"
        );
        // THE LOAD-BEARING ONE. The budget is refilled per declaration, so one
        // declaration cannot cost more than the whole build; a limit above the
        // whole build's total therefore cannot fire on a build that terminates.
        // Lowering the constant under this line re-opens the possibility of
        // turning a working spec build red, which is worse than the hang it
        // replaced.
        assert!(
            DEFAULT_SPEC_DECL_BUDGET >= 5 * ESTIMATED_FULL_SPEC_TOTAL_TICKS,
            "the budget must exceed the estimated total cost of a whole \
             Specification::new(), with headroom on the estimate"
        );
    }

    /// A malformed override must fail loudly. The silent-fallback version of
    /// this function is how a lane comes to believe it raised a limit it did
    /// not raise.
    #[test]
    fn test_malformed_override_is_a_hard_error_not_a_silent_default() {
        // Not exercised through the real env var: `std::env::set_var` is
        // process-global and this crate's tests run in parallel threads. The
        // parse is the whole content of the branch, so it is asserted directly.
        let parsed = "not-a-number".trim().parse::<u64>();
        assert!(parsed.is_err());
        assert!(
            configured_budget().is_ok(),
            "unset env var uses the default"
        );
    }

    /// The latch overrides the registration's own verdict in BOTH directions —
    /// a declaration that "succeeded" on a spent budget did not finish either.
    #[test]
    fn test_finish_declaration_latch_overrides_an_apparent_pass() {
        std::thread::spawn(|| {
            // Build the environment BEFORE arming, which is the same placement
            // rule the production sites follow — `Environment::new()` registers
            // `sorry` through an `expect`-infallible `add_decl`, so a budget
            // armed across it turns a tight limit into a panic about the
            // prelude instead of a verdict about a declaration. Measured here
            // the first time this test was run.
            let env = clean_kernel::Environment::new();
            let tc = clean_kernel::TypeChecker::new(&env);
            clean_kernel::tc::set_declaration_budget(1);
            // Spend the tick through the kernel's own tick site rather than a
            // private counter, so this exercises the real path.
            for _ in 0..8 {
                if clean_kernel::tc::declaration_budget_exhausted() {
                    break;
                }
                let _ = tc.infer_type(&clean_kernel::Expr::prop());
            }
            assert!(
                clean_kernel::tc::declaration_budget_exhausted(),
                "a one-tick budget must be spent by a handful of `infer_type` calls"
            );

            let out = finish_declaration("some_spec_decl", Ok::<(), SpecError>(()));
            match out {
                Err(SpecError::DeclarationBudgetExhausted { declaration, limit }) => {
                    assert_eq!(declaration, "some_spec_decl");
                    assert_eq!(limit, 1);
                }
                other => panic!("expected a budget-exhausted error, got {other:?}"),
            }
            clean_kernel::tc::clear_declaration_budget();
        })
        .join()
        .expect("budget latch test thread must not panic");
    }

    /// Arming is scoped: the thread is left exactly as it was found, so a spec
    /// build cannot leave a fuel limit behind for whatever the (thread-reusing)
    /// test harness runs next.
    #[test]
    fn test_arming_is_scoped_to_the_build() {
        std::thread::spawn(|| {
            assert_eq!(clean_kernel::tc::declaration_budget_limit(), 0);
            let seen = with_spec_declaration_budget(|| {
                Ok::<u64, SpecError>(clean_kernel::tc::declaration_budget_limit())
            })
            .expect("arming must not fail");
            assert_eq!(seen, DEFAULT_SPEC_DECL_BUDGET, "armed inside the build");
            assert_eq!(
                clean_kernel::tc::declaration_budget_limit(),
                0,
                "and disarmed on the way out"
            );
        })
        .join()
        .expect("scope test thread must not panic");
    }

    /// A budget somebody else armed is left alone — including its partly-spent
    /// counter, which the kernel's public API cannot restore. Re-arming and
    /// "restoring" here would refill an enclosing declaration's fuel.
    #[test]
    fn test_an_already_armed_budget_is_never_touched() {
        std::thread::spawn(|| {
            let env = clean_kernel::Environment::new();
            let tc = clean_kernel::TypeChecker::new(&env);
            clean_kernel::tc::set_declaration_budget(1_000);
            let _ = tc.infer_type(&clean_kernel::Expr::prop());
            let spent = clean_kernel::tc::declaration_budget_used();
            assert!(spent > 0, "the outer declaration must have spent something");
            let remaining_before = clean_kernel::tc::declaration_budget_remaining();

            let seen = with_spec_declaration_budget(|| {
                Ok::<u64, SpecError>(clean_kernel::tc::declaration_budget_limit())
            })
            .expect("nested arming must not fail");

            assert_eq!(seen, 1_000, "the OUTER limit stays in force");
            assert_eq!(clean_kernel::tc::declaration_budget_limit(), 1_000);
            assert_eq!(
                clean_kernel::tc::declaration_budget_remaining(),
                remaining_before,
                "the enclosing declaration's spent fuel must not be refilled"
            );
            clean_kernel::tc::clear_declaration_budget();
        })
        .join()
        .expect("nesting test thread must not panic");
    }

    /// A trace row and an error message must stay one readable line: this
    /// crate's `description` labels are routinely paragraphs.
    #[test]
    fn test_label_is_one_bounded_line() {
        assert_eq!(label("ir_lzb_max_true_seg"), "ir_lzb_max_true_seg");
        assert_eq!(label("  padded  "), "padded");
        assert_eq!(label("first line\nsecond line"), "first line");
        let long = "x".repeat(500);
        let cut = label(&long);
        assert_eq!(cut.chars().count(), 121, "120 chars plus the ellipsis");
        assert!(cut.ends_with('…'));
    }

    /// …and it must be transparent when the declaration did finish.
    #[test]
    fn test_finish_declaration_is_transparent_when_the_budget_held() {
        std::thread::spawn(|| {
            clean_kernel::tc::set_declaration_budget(DEFAULT_SPEC_DECL_BUDGET);
            let out = finish_declaration("some_spec_decl", Ok::<u32, SpecError>(9));
            assert_eq!(out.expect("budget held"), 9);
            clean_kernel::tc::clear_declaration_budget();
        })
        .join()
        .expect("budget transparency test thread must not panic");
    }
}
