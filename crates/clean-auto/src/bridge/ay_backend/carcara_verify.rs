// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Feature-gated Carcara proof verification adapter.
//!
//! The adapter parses under `Config::clean_dialect()`, Clean's Alethe dialect
//! (`third-party/carcara/DOWNSTREAM.md` § Dialect), then runs its refusal-only
//! guards (`ashr`, `pb_widths`) and the vendored checker.

use super::proof_backend::VerifyError;

#[cfg(feature = "carcara-verify")]
mod ashr;
#[cfg(feature = "carcara-verify")]
mod bv_literals;
#[cfg(feature = "carcara-verify")]
mod diagnostics;
#[cfg(feature = "carcara-verify")]
mod pb_widths;

#[cfg(all(test, feature = "carcara-verify"))]
mod bv2nat_tests;
#[cfg(all(test, feature = "carcara-verify"))]
mod parser_width_tests;
#[cfg(all(test, feature = "carcara-verify"))]
mod zero_extend_dialect_tests;

#[cfg(all(test, feature = "carcara-verify"))]
mod bv_offset_dialect_tests;

#[cfg(all(test, feature = "carcara-verify"))]
mod array_const_select_tests;
#[cfg(all(test, feature = "carcara-verify"))]
mod bv_offset_spines_tests;
#[cfg(all(test, feature = "carcara-verify"))]
mod bv_reconstruct_tests;

/// Normalize `la_generic` steps that are missing required `:args` coefficients
/// by degrading them to `hole` steps.
///
/// Without Farkas coefficients, Carcara cannot verify `la_generic` steps and
/// returns a hard error. This converts the error into a holey-proof result so
/// callers get `Ok(false)` instead of `Err(CarcaraError)`.
///
/// Part of #2701: ay's QF_LIA Alethe export omits `:args` on `la_generic`.
#[cfg(feature = "carcara-verify")]
fn normalize_la_generic_missing_args(proof: &str) -> String {
    let mut result = String::with_capacity(proof.len());
    for (i, line) in proof.split('\n').enumerate() {
        if i > 0 {
            result.push('\n');
        }
        if line.contains(":rule la_generic") && !line.contains(":args") {
            result.push_str(&line.replace(":rule la_generic", ":rule hole"));
        } else {
            result.push_str(line);
        }
    }
    result
}

/// Verify an Alethe proof using Carcara
///
/// Requires the `carcara-verify` feature to be enabled.
///
/// Applies `la_generic` normalization before checking: steps missing required
/// `:args` coefficients are degraded to `hole` to avoid hard Carcara errors
/// (Part of #2701). The problem and proof are then parsed together under
/// `Config::clean_dialect()` (`third-party/carcara/DOWNSTREAM.md` § Dialect).
///
/// # Arguments
///
/// * `problem` - SMT-LIB2 problem string (declarations and assertions)
/// * `proof` - Alethe proof string
///
/// # Returns
///
/// * `Ok(true)` - Proof fully verified (no holes)
/// * `Ok(false)` - Proof is holey (contains unverified `hole`/`trust` steps)
/// * `Err(...)` - Verification error (parse error, etc.)
///
/// The check runs on a thread of its own, with a stack of [`CHECKER_STACK_BYTES`]. It has no
/// deadline: a caller checking certificates it does not trust gives one to
/// [`verify_alethe_proof_until`]. Without the `carcara-verify` feature no checker is linked, and
/// it returns [`VerifyError::CarcaraNotEnabled`].
pub fn verify_alethe_proof(problem: &str, proof: &str) -> Result<bool, VerifyError> {
    verify_alethe_proof_until(problem, proof, None)
}

/// [`verify_alethe_proof`], refused once `deadline` passes.
///
/// The vendored checker's resource budget bounds what one step builds, not how long a proof takes:
/// a proof can repeat an affordable step, and some comparisons are bounded by time alone
/// (`third-party/carcara/DOWNSTREAM.md`, "The checker stops at a deadline"). With a deadline the
/// parser polls it as it reads (and its capture checks as they go), the checker reads the clock
/// before and after every command, and its comparisons as they go, and the adapter before each
/// reading of the problem and after parsing it; a check stopped by the deadline returns
/// [`VerifyError::CarcaraDeadline`], and a reading it stopped is not retried.
pub fn verify_alethe_proof_until(
    problem: &str,
    proof: &str,
    deadline: Option<std::time::Instant>,
) -> Result<bool, VerifyError> {
    check_on_its_own_thread(problem, proof, deadline)
}

#[cfg(feature = "carcara-verify")]
fn check_on_its_own_thread(
    problem: &str,
    proof: &str,
    deadline: Option<std::time::Instant>,
) -> Result<bool, VerifyError> {
    let _slot = CHECKER_SLOTS.take(deadline)?;
    std::thread::scope(|scope| {
        let checker = std::thread::Builder::new()
            .name("carcara-check".to_owned())
            .stack_size(CHECKER_STACK_BYTES)
            .spawn_scoped(scope, || verify_on_this_thread(problem, proof, deadline))
            .map_err(|error| {
                VerifyError::CarcaraError(format!(
                    "could not start the checker's thread: {}",
                    error.kind()
                ))
            })?;
        checker
            .join()
            .unwrap_or_else(|panic| std::panic::resume_unwind(panic))
    })
}

/// The stack of the thread [`verify_alethe_proof`] checks on: 1 GiB, of which a check commits only
/// the pages it touches.
///
/// The vendored parser and checker recurse once per level of the terms they read and walk. On the
/// caller's thread (8 MiB on a process's main thread, 2 MiB on a worker) a term nested a few
/// thousand deep, written out or built through a chain of definitions, overflowed the stack, which
/// ends the process: a 19 KB certificate did it. The parser now refuses terms and sorts written
/// more than `carcara::parser::MAX_WRITTEN_NESTING` (16,384) deep, at about 2.3 KiB of stack per
/// level in a release build, and terms or sorts more than `MAX_TERM_DEPTH` (262,144) deep, which
/// the rules walk at up to about 1.4 KiB per level: about 37 MiB and 365 MiB. An unoptimized build
/// takes about five times as much per level. See third-party/carcara/DOWNSTREAM.md, "Terms nest at
/// most 2^18 deep".
///
/// Each check running reserves this much address space for its stack, and one of its steps may
/// use up to about 600 MB (the vendored checker's resource budget), so checks run concurrently
/// multiply both: a batch on N threads, or a server's concurrent requests, would reserve N GiB,
/// and on a host that does not overcommit (Linux `vm.overcommit_memory = 2`) a reservation that
/// cannot be made refuses its certificate. At most [`CheckerSlots::limit`] checks run at once in a
/// process; the rest wait their turn, until their deadline if they have one.
#[cfg(feature = "carcara-verify")]
pub const CHECKER_STACK_BYTES: usize = 1 << 30;

/// The checks [`verify_alethe_proof_until`] lets run at once, one per available core
/// (`std::thread::available_parallelism`): the checker is single-threaded and CPU-bound, so more
/// would not finish sooner, and each holds a stack reservation and a step's memory (see
/// [`CHECKER_STACK_BYTES`]).
#[cfg(feature = "carcara-verify")]
static CHECKER_SLOTS: CheckerSlots = CheckerSlots::new(None);

/// A counting gate: at most `limit` holders at once, the others waiting, until their deadline if
/// they have one.
#[cfg(feature = "carcara-verify")]
struct CheckerSlots {
    limit: Option<usize>,
    running: std::sync::Mutex<usize>,
    freed: std::sync::Condvar,
}

/// A held place in [`CheckerSlots`], given back when dropped.
#[cfg(feature = "carcara-verify")]
struct CheckerSlot<'s>(&'s CheckerSlots);

#[cfg(feature = "carcara-verify")]
impl CheckerSlots {
    /// `limit` places, or one per available core for `None`.
    const fn new(limit: Option<usize>) -> Self {
        Self {
            limit,
            running: std::sync::Mutex::new(0),
            freed: std::sync::Condvar::new(),
        }
    }

    fn limit(&self) -> usize {
        self.limit.unwrap_or_else(|| {
            std::thread::available_parallelism().map_or(4, std::num::NonZeroUsize::get)
        })
    }

    /// Waits for a place, refusing once `deadline` passes.
    fn take(&self, deadline: Option<std::time::Instant>) -> Result<CheckerSlot<'_>, VerifyError> {
        let limit = self.limit();
        let mut running = self
            .running
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        while *running >= limit {
            running = match deadline {
                None => self
                    .freed
                    .wait(running)
                    .unwrap_or_else(std::sync::PoisonError::into_inner),
                Some(deadline) => {
                    let now = std::time::Instant::now();
                    if now >= deadline {
                        // A place given back as this wait timed out may have woken only this
                        // waiter: pass the wake-up on.
                        self.freed.notify_one();
                        return Err(diagnostics::deadline_passed(
                            "waiting for another check to end",
                        ));
                    }
                    self.freed
                        .wait_timeout(running, deadline - now)
                        .unwrap_or_else(std::sync::PoisonError::into_inner)
                        .0
                }
            };
        }
        *running += 1;
        Ok(CheckerSlot(self))
    }
}

#[cfg(feature = "carcara-verify")]
impl Drop for CheckerSlot<'_> {
    fn drop(&mut self) {
        let mut running = self
            .0
            .running
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner);
        *running -= 1;
        self.0.freed.notify_one();
    }
}

#[cfg(feature = "carcara-verify")]
fn verify_on_this_thread(
    problem: &str,
    proof: &str,
    deadline: Option<std::time::Instant>,
) -> Result<bool, VerifyError> {
    let problem = bv_literals::normalize(problem)?;
    let proof = bv_literals::normalize(proof)?;
    let normalized_proof = normalize_la_generic_missing_args(&proof);
    pb_widths::check_until(&problem, &normalized_proof, deadline)
}

/// Stub for when Carcara feature is not enabled
#[cfg(not(feature = "carcara-verify"))]
fn check_on_its_own_thread(
    _problem: &str,
    _proof: &str,
    _deadline: Option<std::time::Instant>,
) -> Result<bool, VerifyError> {
    Err(VerifyError::CarcaraNotEnabled)
}

#[cfg(test)]
#[cfg(feature = "carcara-verify")]
mod tests {
    use super::{normalize_la_generic_missing_args, verify_alethe_proof};

    fn uf_contradiction_problem() -> &'static str {
        "(set-logic QF_UF)\n(declare-const p Bool)\n(assert p)\n(assert (not p))\n(check-sat)\n"
    }

    fn uf_contradiction_proof(rule: &str) -> String {
        format!(
            "(assume t0 p)\n(assume t1 (not p))\n(step t2 (cl) :rule {rule} :premises (t1 t0))\n"
        )
    }

    #[test]
    fn test_la_generic_without_args_replaced_with_hole() {
        let proof = "(assume h1 (> x 0))\n\
                     (assume h2 (< x 0))\n\
                     (step t1 (cl (not (> x 0)) (not (< x 0))) :rule la_generic)";
        let normalized = normalize_la_generic_missing_args(proof);
        assert!(
            normalized.contains(":rule hole"),
            "la_generic without :args should be replaced with hole"
        );
        assert!(
            !normalized.contains("la_generic"),
            "la_generic without :args should not remain after normalization"
        );
    }

    #[test]
    fn test_la_generic_with_args_preserved() {
        let proof = "(step t1 (cl (not (> x 0)) (not (< x 0))) :rule la_generic :args (1 1))";
        let normalized = normalize_la_generic_missing_args(proof);
        assert!(
            normalized.contains(":rule la_generic"),
            "la_generic WITH :args should be preserved"
        );
        assert!(
            !normalized.contains(":rule hole"),
            "la_generic WITH :args should not be replaced with hole"
        );
    }

    #[test]
    fn test_other_rules_untouched() {
        let proof = "(step t1 (cl (= a b)) :rule eq_transitive :premises (h1 h2))";
        let normalized = normalize_la_generic_missing_args(proof);
        assert_eq!(
            normalized, proof,
            "non-la_generic rules should be untouched"
        );
    }

    #[test]
    fn test_la_generic_with_premises_but_no_args_replaced() {
        let proof = "(step t1 (cl (not (> x 0)) (not (< x 0))) :rule la_generic :premises (h1 h2))";
        let normalized = normalize_la_generic_missing_args(proof);
        assert!(
            normalized.contains(":rule hole"),
            "la_generic with :premises but no :args should be replaced with hole"
        );
    }

    #[test]
    fn test_verify_alethe_proof_returns_true_for_fully_verified_proof() {
        let valid = verify_alethe_proof(
            uf_contradiction_problem(),
            &uf_contradiction_proof("resolution"),
        )
        .expect("complete UF contradiction proof should verify");
        assert!(valid, "complete proof should report valid=true");
    }

    #[test]
    fn test_verify_alethe_proof_returns_false_for_holey_proof() {
        let valid =
            verify_alethe_proof(uf_contradiction_problem(), &uf_contradiction_proof("hole"))
                .expect("holey proof should return Ok(false), not a transport error");
        assert!(!valid, "holey proof should report valid=false");
    }

    /// At most `limit` checks hold a place at once: one past it waits, and is refused when its
    /// deadline passes first; a place given back lets a waiting check in.
    #[test]
    fn checks_past_the_limit_wait_their_turn() {
        use super::{CheckerSlots, VerifyError};
        use std::time::{Duration, Instant};

        let slots = CheckerSlots::new(Some(2));
        let first = slots.take(None).expect("a place is free");
        let _second = slots
            .take(Some(Instant::now() + Duration::from_secs(3600)))
            .unwrap();
        assert!(matches!(
            slots.take(Some(Instant::now())),
            Err(VerifyError::CarcaraDeadline(message)) if message.contains("waiting")
        ));
        std::thread::scope(|scope| {
            let waiting = scope.spawn(|| slots.take(None).map(drop).is_ok());
            drop(first);
            assert!(waiting.join().unwrap());
        });
        assert!(slots.take(None).is_ok());
    }

    /// A check given a deadline stops at it. `refl` over two chains of conjunctions of two
    /// quantifiers over the level below, named apart, where level `i`'s two quantifiers bind
    /// `x(i-1)` at different indices and the leaves read every `xi`, is alpha-equivalence over
    /// every path with that path's bindings, `2^40` comparisons 40 deep, which no step budget
    /// bounds and no cached answer can share (see `third-party/carcara/DOWNSTREAM.md`, "The checker
    /// stops at a deadline"): it is refused at the deadline (and not retried with the definitions
    /// expanded), and the same proof 4 deep is accepted within a distant one. A deadline already
    /// passed refuses before parsing.
    #[test]
    fn a_check_stops_at_its_deadline() {
        use super::{verify_alethe_proof_until, VerifyError};
        use std::time::{Duration, Instant};

        let problem = |depth: usize| {
            let declarations: String = (0..=depth)
                .map(|i| format!("(declare-const x{i} Int)"))
                .collect();
            format!("(set-logic ALL)(declare-const p Bool){declarations}(assert p)(assert (not p))")
        };
        // The levels are defined in the proof, where the binders they are used under capture the
        // names `xi` their definitions read (a problem's definitions may not be captured).
        let proof = |depth: usize| {
            let leaves: String = (0..=depth).map(|i| format!(" (= x{i} 0)")).collect();
            let mut proof = format!(
                "(define-fun a0 () Bool (and{leaves}))(define-fun b0 () Bool (and{leaves}))"
            );
            for i in 1..=depth {
                let j = i - 1;
                proof += &format!(
                    "(define-fun a{i} () Bool \
                       (and (forall ((x{j} Int)) a{j}) (forall ((y Int) (x{j} Int)) a{j})))\
                     (define-fun b{i} () Bool \
                       (and (forall ((x{j} Int)) b{j}) (forall ((w Int) (x{j} Int)) b{j})))"
                );
            }
            proof
                + &format!(
                    "(step t1 (cl (= (forall ((x{depth} Int)) a{depth}) \
                                 (forall ((x{depth} Int)) b{depth}))) :rule refl)\
                 (assume h1 p)(assume h2 (not p))(step t2 (cl) :rule resolution :premises (h1 h2))"
                )
        };
        let soon = Instant::now() + Duration::from_millis(200);
        match verify_alethe_proof_until(&problem(40), &proof(40), Some(soon)) {
            Err(VerifyError::CarcaraDeadline(message)) => {
                assert!(message.contains("step 't1' with rule 'refl'"), "{message}");
                assert!(
                    message.contains("the check ran past its deadline"),
                    "{message}"
                );
            }
            other => panic!("expected a refusal at the deadline, got {other:?}"),
        }
        assert!(Instant::now() < soon + Duration::from_secs(60));

        let distant = Some(Instant::now() + Duration::from_secs(3600));
        assert!(matches!(
            verify_alethe_proof_until(&problem(4), &proof(4), distant),
            Ok(true)
        ));
        assert!(matches!(
            verify_alethe_proof_until(&problem(4), &proof(4), Some(Instant::now())),
            Err(VerifyError::CarcaraDeadline(message)) if message.contains("before parsing")
        ));
    }

    /// A parse given a deadline stops at it (`third-party/carcara/DOWNSTREAM.md`, "The checker
    /// stops at a deadline"). A problem of 8,000 nested quantifiers, each mentioning a global 50
    /// times, is 1.1 MB that takes about 4 s to read in a release build, and some ten times as long
    /// unoptimized (the parser looks each global up through every scope, upstream's symbol table):
    /// with a deadline of 0.2 s it is refused by the parser, not read whole, and not read again
    /// with its `define-fun` expanded.
    #[test]
    fn a_parse_stops_at_its_deadline() {
        use super::{verify_alethe_proof_until, VerifyError};
        use std::time::{Duration, Instant};

        let depth = 8_000;
        let mentions = vec!["q"; 50].join(" ");
        let mut problem =
            "(set-logic ALL)(declare-const p Bool)(define-fun q () Bool p)".to_owned();
        problem += "(assert ";
        for j in 0..depth {
            problem += &format!("(exists ((u{j} Bool)) (and u{j} {mentions} ");
        }
        problem += "true";
        problem += &"))".repeat(depth);
        problem += ")(assert p)(assert (not p))";
        let proof =
            "(assume h1 p)(assume h2 (not p))(step t1 (cl) :rule resolution :premises (h1 h2))";
        let start = Instant::now();
        match verify_alethe_proof_until(&problem, proof, Some(start + Duration::from_millis(200))) {
            Err(VerifyError::CarcaraDeadline(message)) => {
                assert!(
                    message.contains("the parse ran past its deadline"),
                    "{message}"
                );
                assert!(!message.contains("define-fun expanded"), "{message}");
            }
            other => panic!("expected a refusal at the deadline, got {other:?}"),
        }
        assert!(start.elapsed() < Duration::from_secs(60));
    }
}

#[cfg(all(test, feature = "carcara-verify"))]
mod array_tests;

#[cfg(all(test, feature = "carcara-verify"))]
mod ay_corpus_tests;

#[cfg(all(test, feature = "carcara-verify"))]
mod builtin_spelling_tests;

#[cfg(all(test, feature = "carcara-verify"))]
mod drup_chain_tests;

#[cfg(all(test, feature = "carcara-verify"))]
mod malformed_step_tests;

#[cfg(all(test, feature = "carcara-verify"))]
mod soundness_tests;
