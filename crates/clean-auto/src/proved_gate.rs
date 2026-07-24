// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Public **[PROVED]-grade** entry point for the Trust M-POS output gate.
//!
//! The Trust `trust-cg-bridge` proven-output gate lowers an output-preservation
//! obligation into the `BvExpr` fragment, asks `ay` to EXPORT a zero-trust
//! bit-blast refutation ([`BvBlastProof`]), and only then wants to promote the
//! obligation to the **[PROVED]** grade. Promotion must NOT rest on `ay`'s own
//! `proof.validate()` — that keeps `ay` inside the [PROVED] trusted base. This
//! module routes the exported refutation through the **clean CIC kernel**: the
//! kernel re-checks `checkRefutes <clauses> <refutation> = Bool.true` by LINEAR
//! ι-reduction and applies the PROVED `checkRefutes_sound` Theorem to obtain a
//! genuine `Unsat <clauses>` term. The [PROVED] grade is awarded ONLY when the
//! kernel itself accepts the certificate AND the discharging Theorem carries
//! ZERO domain-specific axioms (closure ⊆ FOUNDATIONAL).
//!
//! If the kernel re-check fails — a forged/corrupted refutation reduces to
//! `Bool.false` (or gets stuck), so the `Eq.refl`-to-`true` certificate is
//! rejected by `check_type` — this returns [`GateRecheck::Rejected`] and the
//! gate falls back to the weaker [VALIDATED] grade. The discrimination is made
//! by the KERNEL, not by `ay`.
//!
//! This is the in-process, acyclic wiring: `clean-auto` has no production
//! dependency on any `trust-*` crate (the `trust-ir`/`trust-cg-*` edges are
//! dev-dependencies only), so a Trust crate may depend on `clean-auto` without
//! a cycle.

use ay_proof::bv_blast_export::BvBlastProof;
use clean_kernel::name::Name;
use clean_kernel::{ConstantKind, Environment};

use crate::bridge::ay_backend::proof_reconstruct::bv_blast_reflection::{
    certify_unsat3_by_reflection, check_refutes3_sound_name, ReflectionError,
};

/// Outcome of routing an exported [`BvBlastProof`] through the clean CIC kernel
/// re-check for the Trust M-POS **[PROVED]** grade.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum GateRecheck {
    /// The clean kernel re-checked the refutation to `Unsat <clauses>` and the
    /// discharging `checkRefutes_sound` Theorem carries ZERO domain axioms
    /// (closure ⊆ FOUNDATIONAL). The obligation is genuinely **[PROVED]** by the
    /// kernel; `ay` is not in the trusted base for this grade.
    KernelAccepted {
        /// Number of CNF clauses the kernel encoded + reduced over.
        num_clauses: usize,
        /// Number of resolution steps the kernel reduced over.
        num_steps: usize,
    },
    /// The clean kernel did NOT accept the refutation (it did not reduce to
    /// `Bool.true`, or the soundness bridge was not a zero-axiom Theorem). The
    /// gate must fall back to [VALIDATED] — it MUST NOT award [PROVED]. The
    /// rejection is made by the kernel `check_type`, not by `ay`.
    Rejected {
        /// Human-readable reason (kernel rejection / non-empty axiom closure).
        reason: String,
    },
    /// The clean kernel awarded the **[PROVED]** grade by O(1) STRUCTURED
    /// INSTANTIATION of a pre-PROVED, zero-domain-axiom theorem at a recognized
    /// canonical bit-vector shape — NOT by per-instance SAT reflection. This is
    /// the rung-3 step-2 path ([`instantiate_bv_theorem`]): the discharging term
    /// is a single theorem application `(thm arg…)` whose type the kernel
    /// `check_type`s against the obligation, INDEPENDENT of any refutation step
    /// count. Awarded ONLY when BOTH the application kernel-type-checks against
    /// the expected conclusion AND the instantiated theorem's transitive
    /// axiom closure is EMPTY (⊆ FOUNDATIONAL). This variant is DORMANT: it is
    /// produced by [`instantiate_bv_theorem`] (with its own kernel-checked tests)
    /// and is NOT yet wired into the live `verify_output.rs` default path — wiring
    /// it (and changing any default-[PROVED] op count) is rung-3 step 3.
    Instantiated {
        /// The pre-PROVED theorem that was instantiated (e.g. `Clean.BV4.bvAdd_comm`).
        theorem: String,
    },
}

impl GateRecheck {
    /// `true` iff the clean kernel awarded the **[PROVED]** grade (by reflection).
    #[must_use]
    pub fn is_kernel_accepted(&self) -> bool {
        matches!(self, GateRecheck::KernelAccepted { .. })
    }

    /// `true` iff the **[PROVED]** grade was awarded by O(1) structured
    /// instantiation (the rung-3 step-2 path).
    #[must_use]
    pub fn is_instantiated(&self) -> bool {
        matches!(self, GateRecheck::Instantiated { .. })
    }
}

/// **Rung-3 step 2 — the O(1) structured-instantiation [PROVED] path (DORMANT).**
///
/// Direct-tree consumption (the resolved design fork): rather than re-prove an
/// obligation by per-instance SAT reflection (O(proof-size)), instantiate a
/// pre-PROVED, zero-domain-axiom kernel theorem at the recognized canonical shape
/// in O(1). The discharging term is a single application `(thm args…)`; the
/// kernel `check_type`s it against the obligation's `expected_conclusion`, and the
/// theorem's axiom closure must be EMPTY. This consumes KERNEL `Expr` objects
/// directly (clean-auto depends only on `clean-kernel`, never the parser/elab), so
/// the canonical shape is a `clean-kernel`-registered bit-vector term tree
/// (`bitvec_compute` BV{N} — the SAME ripple-carry shape the gate blast lowers
/// to), and `theorem` is a registered BV theorem.
///
/// Returns:
/// * [`GateRecheck::Instantiated`] iff `Expr::apps(Const(theorem), args)`
///   kernel-`check_type`s against `expected_conclusion` AND `theorem`'s
///   transitive axiom closure is empty (⊆ FOUNDATIONAL) AND `theorem` is a PROVED
///   `Theorem` constant;
/// * [`GateRecheck::Rejected`] otherwise — a RETARGETED `expected_conclusion`
///   (one the instantiated term does not have), a CORRUPTED / non-existent
///   `theorem`, a NON-CANONICAL shape, or a non-empty axiom closure. The kernel
///   `check_type` makes the discrimination; a wrong shape NEVER yields a grade.
///
/// This is fail-closed and ADDITIVE: it is not called by the live gate yet.
#[must_use]
pub fn instantiate_bv_theorem(
    env: &Environment,
    theorem: &str,
    args: &[clean_kernel::Expr],
    expected_conclusion: &clean_kernel::Expr,
) -> GateRecheck {
    use clean_kernel::{Expr, TypeChecker};

    let thm_name = Name::from_string(theorem);
    // (1) The named constant must exist and be a PROVED Theorem (not an Axiom,
    // not a Definition) — a [PROVED] grade may only rest on a proved theorem.
    let Some(info) = env.get_const(&thm_name) else {
        return GateRecheck::Rejected {
            reason: format!("instantiation theorem `{theorem}` not registered in env"),
        };
    };
    if !matches!(info.kind, ConstantKind::Theorem) {
        return GateRecheck::Rejected {
            reason: format!("`{theorem}` is not a PROVED Theorem (kind {:?})", info.kind),
        };
    }

    // (2) ZERO DOMAIN AXIOMS — the [PROVED] grade requires the instantiated
    // theorem's transitive axiom closure to be EMPTY (⊆ FOUNDATIONAL).
    match env.axiom_deps(&thm_name) {
        Some(domain) if domain.is_empty() => {}
        Some(domain) => {
            return GateRecheck::Rejected {
                reason: format!(
                    "`{theorem}` carries {} domain axiom(s): {:?}",
                    domain.len(),
                    domain.iter().map(ToString::to_string).collect::<Vec<_>>()
                ),
            };
        }
        None => {
            return GateRecheck::Rejected {
                reason: format!("axiom_deps unavailable for `{theorem}`"),
            };
        }
    }

    // (3) THE O(1) INSTANTIATION + KERNEL CHECK. Build `(thm args…)` and
    // `check_type` it against the obligation. A retargeted/non-canonical
    // `expected_conclusion` (one this application does NOT have) is REJECTED by
    // the kernel here — the discrimination is the kernel's, not ours.
    let app = Expr::apps(Expr::const_(thm_name, vec![]), args.iter().cloned());
    let tc = TypeChecker::with_mode(env, env.mode());
    match tc.check_type(&app, expected_conclusion) {
        Ok(()) => GateRecheck::Instantiated {
            theorem: theorem.to_string(),
        },
        Err(e) => GateRecheck::Rejected {
            reason: format!(
                "kernel rejected the instantiation `({theorem} …)` against the obligation: {e:?}"
            ),
        },
    }
}

/// Re-check an `ay`-exported [`BvBlastProof`] with the **clean CIC kernel** and
/// decide the Trust M-POS **[PROVED]** grade.
///
/// Returns [`GateRecheck::KernelAccepted`] ONLY when BOTH hold:
///   1. [`certify_unsat_by_reflection`] succeeds — the kernel reduced
///      `checkRefutes <clauses> <refutation>` to `Bool.true` (LINEAR ι-reduction
///      over the proof data) and the assembled
///      `checkRefutes_sound <clauses> <refutation> (Eq.refl …)` term
///      kernel-type-checks to `Unsat <clauses>`; AND
///   2. the discharging `checkRefutes_sound` constant is a PROVED `Theorem`
///      whose transitive axiom closure is EMPTY (⊆ FOUNDATIONAL) — i.e. zero
///      domain-specific axioms, the definition of the [PROVED] grade.
///
/// Otherwise returns [`GateRecheck::Rejected`]. A forged/corrupted refutation
/// reduces to `Bool.false` (or sticks), so its `Eq.refl`-to-`true` certificate
/// is rejected by the kernel `check_type` — the gate then falls back to
/// [VALIDATED]. This is the fail-closed discrimination that removes `ay` from
/// the [PROVED] trusted base: even a refutation that passes `ay`'s own
/// `validate()` is awarded [PROVED] only if the clean kernel independently
/// re-checks it.
///
/// `env` must have had [`Environment::init_resolution_soundness`] run (so the
/// `checkRefutes_sound` Theorem is registered). The deep ι-reduction needs a
/// large stack; callers should run this on a big-stack thread
/// (see [`kernel_recheck_proved_grade_big_stack`]).
#[must_use]
pub fn kernel_recheck_proved_grade(env: &Environment, proof: &BvBlastProof) -> GateRecheck {
    // (1) THE KERNEL RE-CHECK. `certify_unsat3_by_reflection` reduces the
    // SUB-QUADRATIC trie checker `checkRefutes3 (initialTrie cs) (listLen cs)
    // steps` over the proof data and type-checks the `checkRefutes3_sound`
    // application. The trie checker is the proven (closure ⊆ FOUNDATIONAL)
    // mechanism designed for the live-gate proof scale (1522 clauses / 11228
    // steps); the O(steps²) `checkRefutes_sound` path OOMs (>100 GB) on that
    // shape. A forged refutation reduces to `Bool.false` and is rejected HERE
    // by the kernel.
    match certify_unsat3_by_reflection(env, proof) {
        Ok((unsat_term, _unsat_goal)) => {
            // Defence-in-depth: the discharging term must actually apply the
            // PROVED soundness bridge (not some other constant).
            if !format!("{unsat_term:?}").contains("checkRefutes3_sound") {
                return GateRecheck::Rejected {
                    reason: "kernel-accepted term does not apply checkRefutes3_sound".to_string(),
                };
            }
            // (2) ZERO DOMAIN AXIOMS — the [PROVED] grade requires the soundness
            // bridge to be a Theorem with an EMPTY domain-axiom closure.
            let sound = Name::from_string(check_refutes3_sound_name());
            let Some(info) = env.get_const(&sound) else {
                return GateRecheck::Rejected {
                    reason: "checkRefutes_sound not registered in env".to_string(),
                };
            };
            if !matches!(info.kind, ConstantKind::Theorem) {
                return GateRecheck::Rejected {
                    reason: "checkRefutes_sound is not a PROVED Theorem".to_string(),
                };
            }
            match env.axiom_deps(&sound) {
                Some(domain) if domain.is_empty() => GateRecheck::KernelAccepted {
                    num_clauses: proof.clauses.len(),
                    num_steps: proof.refutation.steps.len(),
                },
                Some(domain) => GateRecheck::Rejected {
                    reason: format!(
                        "checkRefutes3_sound carries {} domain axiom(s): {:?}",
                        domain.len(),
                        domain.iter().map(ToString::to_string).collect::<Vec<_>>()
                    ),
                },
                None => GateRecheck::Rejected {
                    reason: "axiom_deps unavailable for checkRefutes3_sound".to_string(),
                },
            }
        }
        Err(ReflectionError::InvalidProof(m)) => GateRecheck::Rejected {
            reason: format!("producer validate() failed before kernel re-check: {m}"),
        },
        Err(ReflectionError::CertificateRejected(m)) => GateRecheck::Rejected {
            reason: format!("clean kernel rejected reflection certificate: {m}"),
        },
    }
}

/// Stack size for the kernel re-check thread. The trie checker's ι-reduction
/// over the live-gate proof (11228 steps) is deep and overflows the 2 MiB
/// default stack; 256 MiB is the bound the always-on clean live re-check uses
/// for the same 11228-step trie reduction (see `tests_bv_blast_reflection.rs`
/// `live_kernel_reflect_and_assert_empty_domain`). The earlier 2 GiB value was
/// masking the wrong-checker (O(steps²) `checkRefutes_sound`) blowup — which a
/// bigger stack cannot fix — not a genuine depth requirement of the trie path.
pub const RECHECK_STACK_BYTES: usize = 256 * 1024 * 1024;

/// Run [`kernel_recheck_proved_grade`] on a fresh big-stack thread with a
/// prelude environment that has `init_resolution_soundness` applied.
///
/// This is the turn-key entry point for the Trust gate: it owns the kernel
/// environment setup and the big stack so the caller (`trust-cg-bridge`) does
/// not need to depend on `clean-kernel` directly. Returns
/// [`GateRecheck::Rejected`] if the environment cannot be initialised.
#[must_use]
pub fn kernel_recheck_proved_grade_big_stack(proof: &BvBlastProof) -> GateRecheck {
    let proof = proof.clone();
    let handle = std::thread::Builder::new()
        .stack_size(RECHECK_STACK_BYTES)
        .name("trust-mpos-kernel-recheck".to_string())
        .spawn(move || {
            let mut env = Environment::with_prelude();
            if let Err(e) = env.init_resolution_soundness() {
                return GateRecheck::Rejected {
                    reason: format!("init_resolution_soundness failed: {e:?}"),
                };
            }
            kernel_recheck_proved_grade(&env, &proof)
        });
    match handle {
        Ok(h) => match h.join() {
            Ok(outcome) => outcome,
            Err(_) => GateRecheck::Rejected {
                reason: "kernel re-check thread panicked".to_string(),
            },
        },
        Err(e) => GateRecheck::Rejected {
            reason: format!("failed to spawn kernel re-check thread: {e}"),
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bridge::ay_backend::proof_reconstruct::bv_blast_reflection::{
        certify_unsat3_by_reflection, encode_proof_clauses, proof_step_tuples, ReflectionError,
    };
    use ay_proof::bv_blast_export::Lit;
    use ay_proof::bv_blast_solver::{export_bv_blast_proof_expr, BvExpr};
    use clean_kernel::resolution_check::check_refutes3_initialtrie_app;
    use clean_kernel::{Expr, TypeChecker};

    /// A genuine, solver-backed gate-shaped add-leaf obligation at width 4 whose
    /// refutation the clean kernel accepts. Mirrors the live gate's lowering.
    fn real_gate_add_proof() -> BvBlastProof {
        // machine_out := (a + b) ; ir := (a + b) — an UNCONDITIONAL identity in
        // the BvExpr add-leaf fragment, so `not(lhs == rhs)` is UNSAT and ay
        // exports a real refutation.
        let a = BvExpr::leaf("a", 4);
        let b = BvExpr::leaf("b", 4);
        let lhs = BvExpr::Add(Box::new(a.clone()), Box::new(b.clone()));
        let rhs = BvExpr::Add(Box::new(a), Box::new(b));
        export_bv_blast_proof_expr(&lhs, &rhs).expect("real add-leaf obligation must export")
    }

    #[test]
    fn proved_gate_kernel_accepts_real_add_leaf() {
        let outcome = kernel_recheck_proved_grade_big_stack(&real_gate_add_proof());
        assert!(
            outcome.is_kernel_accepted(),
            "real add-leaf refutation must be KERNEL-accepted to [PROVED]; got {outcome:?}"
        );
    }

    /// ANTI-VACUITY (LOAD-BEARING): corrupt a recorded resolvent so the CLEAN
    /// KERNEL re-check fails. The corruption is detected by the kernel reducing
    /// `checkRefutes` to `Bool.false` (rejecting the `Eq.refl` certificate via
    /// `check_type`) — NOT merely by `ay`'s `validate()`. We assert (a) the
    /// kernel-level `certify_unsat_by_reflection` rejects, and (b) the
    /// gate-grade decision is `Rejected` (no [PROVED]).
    #[test]
    fn proved_gate_kernel_rejects_corrupted_refutation() {
        std::thread::Builder::new()
            .stack_size(RECHECK_STACK_BYTES)
            .spawn(|| {
                let mut env = Environment::with_prelude();
                env.init_resolution_soundness()
                    .expect("init_resolution_soundness");

                let mut proof = real_gate_add_proof();
                // Sanity: the pristine proof is kernel-accepted via the trie checker.
                assert!(
                    certify_unsat3_by_reflection(&env, &proof).is_ok(),
                    "pristine refutation must kernel-check before tampering"
                );

                // TAMPER: replace a mid-chain recorded resolvent with a spurious
                // clause over an out-of-range var id. The recorded clause no
                // longer set-equals the recomputed resolvent, so the kernel
                // `checkRefutes` reduction yields `Bool.false` and the `Eq.refl`
                // certificate is rejected by `check_type` — the KERNEL refuses it.
                let mid = proof.refutation.steps.len() / 2;
                let bogus_var = proof.vars.roles.len() as u32 + 100;
                proof.refutation.steps[mid].clause = vec![Lit {
                    var: bogus_var,
                    neg: false,
                }];

                // (a) THE KERNEL ITSELF (not ay's validate) rejects the tampered
                // data. We bypass `proof.validate()` entirely and reduce the
                // SUB-QUADRATIC trie checker
                // `checkRefutes3 (initialTrie cs) (listLen cs) steps` directly:
                // the kernel WHNF yields `Bool.false`, so an `Eq.refl`-to-`true`
                // certificate is impossible. This proves the discrimination is the
                // KERNEL's, not the producer's.
                let clauses = encode_proof_clauses(&proof);
                let app = check_refutes3_initialtrie_app(clauses, &proof_step_tuples(&proof));
                let tc = TypeChecker::with_mode(&env, env.mode());
                let nf = tc.whnf(&app);
                assert_eq!(
                    nf,
                    Expr::const_str("Bool.false"),
                    "tampered refutation must reduce to Bool.false in the KERNEL \
                     (kernel rejects it, independent of ay's validate); got {nf:?}"
                );

                // (a') The full re-check API also rejects it.
                let rejected = certify_unsat3_by_reflection(&env, &proof);
                assert!(
                    matches!(
                        rejected,
                        Err(ReflectionError::InvalidProof(_) | ReflectionError::CertificateRejected(_))
                    ),
                    "tampered refutation must be rejected by the clean kernel re-check; got {rejected:?}"
                );

                // (b) The gate-grade decision refuses [PROVED].
                let outcome = kernel_recheck_proved_grade(&env, &proof);
                assert!(
                    !outcome.is_kernel_accepted(),
                    "corrupted refutation must NOT be awarded [PROVED]; got {outcome:?}"
                );
            })
            .expect("spawn big-stack thread")
            .join()
            .expect("anti-vacuity thread must not panic");
    }

    // ── RUNG-3 STEP 2: the O(1) structured-instantiation [PROVED] path ──────────
    //
    // These exercise `instantiate_bv_theorem` directly against the
    // `clean-kernel`-registered `bitvec_compute` BV4 layer — kernel `Expr`
    // objects reachable from clean-auto (which depends only on clean-kernel, not
    // the parser/elab). They prove the mechanism is real (a genuine theorem
    // application kernel-type-checks in O(1)) AND fail-closed (a retargeted /
    // corrupted / non-canonical shape is REJECTED, never a false grade).

    use clean_kernel::bitvec_compute::{bv_eq, names as bvn};
    use clean_kernel::Level;

    /// Env with the `bitvec_compute` BV4 layer (carrier, ripple-carry adder, and
    /// the empty-axiom theorems `bvAdd_comm` / `bvAdd_zero` / `bvSub_self`).
    fn bv_env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_bv_compute().expect("init_bv_compute");
        env
    }

    /// `Clean.BV4.mk b0 b1 b2 b3` from four Bool exprs.
    fn bv_mk(b: [Expr; 4]) -> Expr {
        Expr::apps(
            Expr::const_str(bvn::BV_MK),
            [b[0].clone(), b[1].clone(), b[2].clone(), b[3].clone()],
        )
    }
    fn bv_lit(value: u8) -> Expr {
        let bit = |k: u8| {
            if (value >> k) & 1 == 1 {
                Expr::const_str("Bool.true")
            } else {
                Expr::const_str("Bool.false")
            }
        };
        bv_mk([bit(0), bit(1), bit(2), bit(3)])
    }
    fn bv_add(x: Expr, y: Expr) -> Expr {
        Expr::apps(Expr::const_str(bvn::BV_ADD), [x, y])
    }

    /// POSITIVE CONTROL: instantiate the PROVED `bvAdd_comm` at concrete BV4
    /// operands. The O(1) application `(bvAdd_comm a b)` has type
    /// `bvEq (bvAdd a b) (bvAdd b a)`; the kernel `check_type`s it and the
    /// theorem's axiom closure is empty -> Instantiated.
    #[test]
    fn instantiated_path_accepts_real_bv_add_comm() {
        let env = bv_env();
        let a = bv_lit(0b0101);
        let b = bv_lit(0b0011);
        // expected conclusion: bvEq (bvAdd a b) (bvAdd b a)
        let concl = bv_eq(bv_add(a.clone(), b.clone()), bv_add(b.clone(), a.clone()));
        let outcome = instantiate_bv_theorem(&env, bvn::BV_ADD_COMM, &[a, b], &concl);
        assert!(
            outcome.is_instantiated(),
            "a genuine bvAdd_comm instantiation must be Instantiated [PROVED]; got {outcome:?}"
        );
    }

    /// POSITIVE CONTROL (SYMBOLIC — not a ground-reduction coincidence): with
    /// FREE-VARIABLE operands `a, b : BV4` (registered as opaque operands, NOT
    /// dependencies of `bvAdd_comm`), `bvAdd a b` and `bvAdd b a` are NOT
    /// definitionally equal, so the instantiation kernel-checks ONLY because
    /// `bvAdd_comm`'s DECLARED type is exactly `bvEq (bvAdd a b) (bvAdd b a)`.
    /// This proves the acceptance is theorem-dependent (the #27-#29 symbolic
    /// discipline), and the theorem's own axiom closure stays empty.
    #[test]
    fn instantiated_path_accepts_symbolic_bv_add_comm() {
        let mut env = bv_env();
        // opaque symbolic operands a, b : BV4 (test-only; not deps of the theorem)
        for nm in ["sym_a", "sym_b"] {
            env.add_decl(clean_kernel::Declaration::Axiom {
                name: Name::from_string(nm),
                level_params: vec![],
                type_: Expr::const_str(bvn::BV),
            })
            .expect("register symbolic operand");
        }
        let a = Expr::const_str("sym_a");
        let b = Expr::const_str("sym_b");
        let concl = bv_eq(bv_add(a.clone(), b.clone()), bv_add(b.clone(), a.clone()));
        let outcome = instantiate_bv_theorem(&env, bvn::BV_ADD_COMM, &[a, b], &concl);
        assert!(
            outcome.is_instantiated(),
            "symbolic bvAdd_comm instantiation must be Instantiated [PROVED]; got {outcome:?}"
        );
        // And the commuted form is NOT reflexively trivial: a reflexive RHS over
        // the SAME symbolic operands is a DIFFERENT proposition the comm theorem
        // does not have, so it must be Rejected.
        let a2 = Expr::const_str("sym_a");
        let b2 = Expr::const_str("sym_b");
        let reflexive = bv_eq(
            bv_add(a2.clone(), b2.clone()),
            bv_add(a2.clone(), b2.clone()),
        );
        let bad = instantiate_bv_theorem(&env, bvn::BV_ADD_COMM, &[a2, b2], &reflexive);
        assert!(
            matches!(bad, GateRecheck::Rejected { .. }),
            "over SYMBOLIC operands, the reflexive conclusion is a different prop and \
             must be Rejected (proving acceptance was not ground-reduction); got {bad:?}"
        );
    }

    /// NEGATIVE CONTROL 1 (RETARGET): instantiate `bvAdd_comm` but claim a
    /// GENUINELY DIFFERENT conclusion — `bvEq (bvAdd a b) (bvSub a b)` (sum vs
    /// difference; at a=5,b=3 that is 8 vs 2, not definitionally equal even after
    /// ground reduction). The application's actual type is the commuted-ADD
    /// equality; the kernel check_type REJECTS this retargeted conclusion.
    /// (NOTE: a reflexive `bvEq (bvAdd a b) (bvAdd a b)` would NOT be a valid
    /// retarget control — on GROUND operands commutativity is definitional, so
    /// both sides reduce to the SAME BV4 literal and the kernel would accept it;
    /// the genuine retarget must change the VALUE, which `bvSub` does.)
    #[test]
    fn instantiated_path_rejects_retargeted_conclusion() {
        let env = bv_env();
        let a = bv_lit(0b0101); // 5
        let b = bv_lit(0b0011); // 3
        let bv_sub = |x: Expr, y: Expr| Expr::apps(Expr::const_str(bvn::BV_SUB), [x, y]);
        // WRONG / genuinely different: claim the sum equals the difference.
        let retargeted = bv_eq(bv_add(a.clone(), b.clone()), bv_sub(a.clone(), b.clone()));
        let outcome = instantiate_bv_theorem(&env, bvn::BV_ADD_COMM, &[a, b], &retargeted);
        assert!(
            matches!(outcome, GateRecheck::Rejected { .. }),
            "a retargeted (sum==difference) conclusion must be Rejected; got {outcome:?}"
        );
        assert!(!outcome.is_instantiated());
    }

    /// NEGATIVE CONTROL 2 (CORRUPTED / NON-EXISTENT THEOREM): instantiate a
    /// theorem name that is not registered. No PROVED constant backs it ->
    /// Rejected (never a grade resting on a non-existent theorem).
    #[test]
    fn instantiated_path_rejects_unregistered_theorem() {
        let env = bv_env();
        let a = bv_lit(0b0101);
        let b = bv_lit(0b0011);
        let concl = bv_eq(bv_add(a.clone(), b.clone()), bv_add(b.clone(), a.clone()));
        let outcome = instantiate_bv_theorem(&env, "Clean.BV4.bvAdd_BOGUS", &[a, b], &concl);
        assert!(
            matches!(outcome, GateRecheck::Rejected { .. }),
            "an unregistered theorem must be Rejected; got {outcome:?}"
        );
    }

    /// NEGATIVE CONTROL 3 (NON-CANONICAL / FALSE SHAPE): instantiate `bvAdd_comm`
    /// against a FALSE conclusion `bvEq (bvAdd 1 1) (bvAdd 1 1) -> ... ` no — use a
    /// flatly false ground equality `bvEq (bvAdd 1 1) 1` (1+1 = 2 ≠ 1). The
    /// application does not have this type; the kernel REJECTS it. A false
    /// obligation can never be discharged by instantiation.
    #[test]
    fn instantiated_path_rejects_false_ground_shape() {
        let env = bv_env();
        let one = bv_lit(1);
        // FALSE: bvEq (bvAdd 1 1) 1  (the sum is 2, not 1)
        let false_concl = bv_eq(bv_add(one.clone(), one.clone()), one.clone());
        let outcome =
            instantiate_bv_theorem(&env, bvn::BV_ADD_COMM, &[one.clone(), one], &false_concl);
        assert!(
            matches!(outcome, GateRecheck::Rejected { .. }),
            "a false ground shape must be Rejected; got {outcome:?}"
        );
    }

    /// DISCRIMINATING WITNESS (the signed-vs-unsigned class, expressed at this
    /// layer): the add theorem must NOT discharge a DIFFERENT-operator obligation.
    /// We instantiate `bvAdd_comm` against a `bvSub`-shaped conclusion
    /// `bvEq (bvSub a b) (bvSub b a)` — the wrong operator (and false: sub is not
    /// commutative). Just as a ULT tree must not satisfy an SLT obligation
    /// (#31's signed-vs-unsigned control), an ADD theorem must not satisfy a SUB
    /// obligation. The kernel check_type REJECTS it.
    #[test]
    fn instantiated_path_rejects_wrong_operator_obligation() {
        let env = bv_env();
        let a = bv_lit(0b0101);
        let b = bv_lit(0b0011);
        let bv_sub = |x: Expr, y: Expr| Expr::apps(Expr::const_str(bvn::BV_SUB), [x, y]);
        // WRONG OPERATOR: a SUB-shaped (and non-commutative, hence false) conclusion.
        let sub_concl = bv_eq(bv_sub(a.clone(), b.clone()), bv_sub(b.clone(), a.clone()));
        let outcome = instantiate_bv_theorem(&env, bvn::BV_ADD_COMM, &[a, b], &sub_concl);
        assert!(
            matches!(outcome, GateRecheck::Rejected { .. }),
            "an add theorem must not discharge a sub obligation; got {outcome:?}"
        );
    }

    /// The mechanism uses NO `Level` machinery beyond the prelude; this guards the
    /// import is exercised (and documents the unused-import lint would catch drift).
    #[test]
    fn instantiated_path_level_import_is_live() {
        let _ = Level::zero();
    }

    // ── SUBSTRATE → RUNTIME end-to-end: the Instantiated path now has a REAL
    // machine-vs-IR FIDELITY theorem to instantiate (rung-3 substrate, #33) ──────
    //
    // Until #33 the Instantiated path could only be demonstrated against the
    // ALGEBRAIC identity `bvAdd_comm`. The fidelity substrate registers
    // `bvAdd_eq_ir : (x y) -> bvEq (bvAdd x y) (bvAddIr x y)` — machine adder ≡ IR
    // adder, separately defined then PROVEN equal (empty axiom closure). These
    // tests prove the #32 path now instantiates a genuine output-preservation
    // theorem, AND still rejects a retargeted obligation.

    fn fid_env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_bv_fidelity().expect("init_bv_fidelity");
        env
    }
    fn bv_add_ir(x: Expr, y: Expr) -> Expr {
        Expr::apps(Expr::const_str(bvn::BV_ADD_IR), [x, y])
    }

    /// POSITIVE: the Instantiated path discharges a real output-preservation
    /// obligation `bvEq (bvAdd a b) (bvAddIr a b)` by O(1) instantiation of the
    /// PROVED, empty-axiom `bvAdd_eq_ir` at concrete operands.
    #[test]
    fn instantiated_path_discharges_machine_vs_ir_fidelity() {
        let env = fid_env();
        let a = bv_lit(0b0101);
        let b = bv_lit(0b0011);
        let concl = bv_eq(
            bv_add(a.clone(), b.clone()),
            bv_add_ir(a.clone(), b.clone()),
        );
        let outcome = instantiate_bv_theorem(&env, bvn::BV_ADD_EQ_IR, &[a, b], &concl);
        assert!(
            outcome.is_instantiated(),
            "the machine-vs-IR fidelity theorem must discharge the output-preservation \
             obligation by O(1) instantiation; got {outcome:?}"
        );
    }

    /// NEGATIVE: the fidelity theorem must NOT discharge a WRONG obligation — claim
    /// `bvEq (bvAdd a b) (bvAdd a b)` is the machine==machine reflexive shape, but
    /// the theorem's type is machine==IR; over GROUND operands these coincide
    /// definitionally, so to get a genuine retarget we claim the SUM equals the
    /// machine SUB (8 vs 2 at a=5,b=3) — the kernel REJECTS it.
    #[test]
    fn instantiated_path_fidelity_rejects_wrong_obligation() {
        let env = fid_env();
        let a = bv_lit(0b0101);
        let b = bv_lit(0b0011);
        let bv_sub = |x: Expr, y: Expr| Expr::apps(Expr::const_str(bvn::BV_SUB), [x, y]);
        let wrong = bv_eq(bv_add(a.clone(), b.clone()), bv_sub(a.clone(), b.clone()));
        let outcome = instantiate_bv_theorem(&env, bvn::BV_ADD_EQ_IR, &[a, b], &wrong);
        assert!(
            matches!(outcome, GateRecheck::Rejected { .. }),
            "the fidelity theorem must not discharge a sum==difference obligation; got {outcome:?}"
        );
    }

    // ── SCALABLE substrate → runtime: the Instantiated path discharges the
    // INDUCTIVE, PARAMETRIC-WIDTH fidelity theorem at a REAL width (#34) ─────────
    //
    // The #33 BV4 fidelity was fixed-width-4 (a non-representative width whose
    // proof technique does not scale). #34's `Clean.BVI.addRec_eq_ir` is proven by
    // induction over bit-position and is PARAMETRIC in width (covers i8/i16/i32/i64
    // in one theorem). These tests prove the #32 Instantiated path discharges a
    // width-32 (real i32) add obligation by O(1) instantiation of it.

    use clean_kernel::bitvec_inductive::names as bvin;

    fn bvi_env() -> Environment {
        let mut env = Environment::with_prelude();
        env.init_bv_inductive().expect("init_bv_inductive");
        env
    }
    fn list_bool_e() -> Expr {
        Expr::app(
            Expr::const_(
                clean_kernel::name::Name::from_string("List"),
                vec![Level::zero()],
            ),
            Expr::const_str("Bool"),
        )
    }
    fn bvi_lit(value: u64, width: u32) -> Expr {
        let nil = Expr::app(
            Expr::const_(
                clean_kernel::name::Name::from_string("List.nil"),
                vec![Level::zero()],
            ),
            Expr::const_str("Bool"),
        );
        let cons = |h: Expr, t: Expr| {
            Expr::apps(
                Expr::const_(
                    clean_kernel::name::Name::from_string("List.cons"),
                    vec![Level::zero()],
                ),
                [Expr::const_str("Bool"), h, t],
            )
        };
        let mut acc = nil;
        for k in (0..width).rev() {
            let bit = if (value >> k) & 1 == 1 {
                Expr::const_str("Bool.true")
            } else {
                Expr::const_str("Bool.false")
            };
            acc = cons(bit, acc);
        }
        acc
    }
    fn eq_list_e(a: Expr, b: Expr) -> Expr {
        Expr::apps(
            Expr::const_(
                clean_kernel::name::Name::from_string("Eq"),
                vec![Level::succ(Level::zero())],
            ),
            [list_bool_e(), a, b],
        )
    }

    /// POSITIVE (the scalable win): the Instantiated path discharges a WIDTH-32
    /// add obligation `addRecM x y false = addRecIr x y false` by O(1) instantiation
    /// of the inductive, parametric `addRec_eq_ir`.
    #[test]
    fn instantiated_path_discharges_inductive_fidelity_at_width_32() {
        let env = bvi_env();
        let f = Expr::const_str("Bool.false");
        let x = bvi_lit(0xDEAD_BEEF, 32);
        let y = bvi_lit(0x0123_4567, 32);
        let add_m = Expr::apps(
            Expr::const_str(bvin::ADD_REC_M),
            [x.clone(), y.clone(), f.clone()],
        );
        let add_ir = Expr::apps(
            Expr::const_str(bvin::ADD_REC_IR),
            [x.clone(), y.clone(), f.clone()],
        );
        let concl = eq_list_e(add_m, add_ir);
        let outcome = instantiate_bv_theorem(&env, bvin::ADD_REC_EQ_IR, &[x, y, f], &concl);
        assert!(
            outcome.is_instantiated(),
            "the inductive parametric-width fidelity theorem must discharge a width-32 \
             add obligation by O(1) instantiation; got {outcome:?}"
        );
    }

    /// P3 (audit) — SYMBOLIC-operand instantiation-path test: discharge
    /// `addRecM [sb] [sb] false = addRecIr [sb] [sb] false` over an OPAQUE
    /// `sb : Bool`, where a bare `Eq.refl` would NOT close (the two adders are
    /// distinct over a symbolic bit) — so acceptance is THEOREM-dependent, not a
    /// ground-reduction coincidence (the ground width-32 tests above could be
    /// closed by refl). Mirrors `instantiated_path_accepts_symbolic_bv_add_comm`.
    #[test]
    fn instantiated_path_inductive_symbolic_operand_is_theorem_dependent() {
        use clean_kernel::TypeChecker;
        let mut env = bvi_env();
        env.add_decl(clean_kernel::Declaration::Axiom {
            name: clean_kernel::name::Name::from_string("sb_bvi"),
            level_params: vec![],
            type_: Expr::const_str("Bool"),
        })
        .expect("register opaque sb");
        let sb = Expr::const_str("sb_bvi");
        let f = Expr::const_str("Bool.false");
        // xs = ys = [sb] : List Bool
        let one_list = |b: Expr| {
            Expr::apps(
                Expr::const_(
                    clean_kernel::name::Name::from_string("List.cons"),
                    vec![Level::zero()],
                ),
                [
                    Expr::const_str("Bool"),
                    b,
                    Expr::app(
                        Expr::const_(
                            clean_kernel::name::Name::from_string("List.nil"),
                            vec![Level::zero()],
                        ),
                        Expr::const_str("Bool"),
                    ),
                ],
            )
        };
        let xs = one_list(sb.clone());
        let ys = one_list(sb.clone());
        let add_m = Expr::apps(
            Expr::const_str(bvin::ADD_REC_M),
            [xs.clone(), ys.clone(), f.clone()],
        );
        let add_ir = Expr::apps(
            Expr::const_str(bvin::ADD_REC_IR),
            [xs.clone(), ys.clone(), f.clone()],
        );
        let concl = eq_list_e(add_m.clone(), add_ir);
        // POSITIVE: the theorem discharges the symbolic obligation.
        let outcome =
            instantiate_bv_theorem(&env, bvin::ADD_REC_EQ_IR, &[xs, ys, f.clone()], &concl);
        assert!(
            outcome.is_instantiated(),
            "addRec_eq_ir must discharge the SYMBOLIC [sb] add obligation (theorem-dependent); got {outcome:?}"
        );
        // CONTROL: a bare Eq.refl of the machine side does NOT close the symbolic
        // goal (the two adders are distinct over a symbolic bit) — proving the
        // acceptance above was the THEOREM, not ground reduction.
        let tc = TypeChecker::with_mode(&env, env.mode());
        let refl = Expr::apps(
            Expr::const_(
                clean_kernel::name::Name::from_string("Eq.refl"),
                vec![Level::succ(Level::zero())],
            ),
            [list_bool_e(), add_m.clone()],
        );
        let refl_goal = eq_list_e(
            add_m.clone(),
            Expr::apps(
                Expr::const_str(bvin::ADD_REC_IR),
                [one_list(sb.clone()), one_list(sb), f],
            ),
        );
        assert!(
            tc.check_type(&refl, &refl_goal).is_err(),
            "the SYMBOLIC addRecM=addRecIr goal must NOT close by Eq.refl (else acceptance \
             would be ground-reduction, not theorem-dependent)"
        );
    }

    /// NEGATIVE: instantiating the inductive theorem against a WRONG conclusion
    /// (claim the machine sum equals the all-zero literal) is Rejected by the kernel.
    #[test]
    fn instantiated_path_inductive_rejects_wrong_conclusion() {
        let env = bvi_env();
        let f = Expr::const_str("Bool.false");
        let x = bvi_lit(1, 8);
        let y = bvi_lit(1, 8);
        let add_m = Expr::apps(
            Expr::const_str(bvin::ADD_REC_M),
            [x.clone(), y.clone(), f.clone()],
        );
        let wrong = bvi_lit(0, 8); // 1+1=2, not 0
        let concl = eq_list_e(add_m, wrong);
        let outcome = instantiate_bv_theorem(&env, bvin::ADD_REC_EQ_IR, &[x, y, f], &concl);
        assert!(
            matches!(outcome, GateRecheck::Rejected { .. }),
            "a wrong conclusion (sum == 0) must be Rejected; got {outcome:?}"
        );
    }
}
