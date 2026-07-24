// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! S4 — the multi-variable FINITE-FRAGMENT kernel-closed reconstruction
//! (blueprint `/docs/design-notes/2026-07-18-r5-temporal-lane-blueprint.md`,
//! slice S4: "the keystone both designs omitted").
//!
//! [`register_ty_cert_safety_finite`] lifts the `sole_var` 1-variable limit of
//! [`crate::ty_cert`]: it re-encodes a MULTI-VARIABLE bounded machine from a
//! `ty.cert/v1` certificate's own `spec_src` (source fidelity), explores its
//! cfg-bounded state space exhaustively under dual Int/Nat semantics, and
//! registers a fully kernel-closed product:
//!
//! 1. `<thm>_check : Bool` — a reflection checker enumerating the reachable
//!    state space, verifying init⊆J, J-closed-under-Next, and J⇒Safety;
//! 2. `<thm>_check_eq_true : <thm>_check = true := Eq.refl true` — the `rfl`
//!    leg (the kernel EVALUATES the checker; this is where enumeration
//!    tractability is paid and measured);
//! 3. `<thm>_sound : <thm>_check = true → ∀ b, Runs Init Next b → Sat b (□
//!    Safety)` — the soundness lemma (keystone instantiation with J = the
//!    reachable-state disjunction);
//! 4. `<thm>` — the final bare conclusion, type α-equal to
//!    [`crate::ty_cert::conclusion_ty`] recomputed independently.
//!
//! All four are real kernel-checked `Declaration`s: no axiom, no `sorry`,
//! `ProofQuality::Constructive`. The `_assumed`-style Pi-bound obligations
//! never appear — and the final type carries NO leading hypothesis Pis, which
//! is exactly what the Certified gate's α-exact type comparison keys on.
//!
//! ## Fail-closed discipline
//!
//! * Reachable invariant violation → [`FiniteError::Falsified`] with an
//!   in-process, step-replayed counterexample trace (no stdout parsing).
//! * Oversize enumeration → [`FiniteError::StateSpaceBoundExceeded`] (named
//!   reason, cap [`MAX_ENUM_STATES`]).
//! * Int/Nat truncation divergence anywhere the proof will look →
//!   [`FiniteError::TruncationDivergence`].
//! * Name collision on ANY of the four product names → error, never a silent
//!   skip (the ty_cert.rs:678/:755 squat vector, closed).
//! * Blessed `TLAsem.*` / `TLAfin.*` vocabulary already present with a
//!   DIFFERENT definition → [`FiniteError::VocabularySquatted`].

pub mod encode;
pub mod machine;
pub mod parse;

use std::time::Instant;

use clean_kernel::env::{ConstantKind, Declaration, Environment, ProofQuality};
use clean_kernel::expr::{BinderInfo, Expr};
use clean_kernel::level::Level;
use clean_kernel::name::Name;

pub use encode::{encode_finite, FiniteEncoded, MAX_PACKED_STATE};
pub use machine::{Explored, FiniteMachine};

use crate::semantics::{self, B};
use crate::ty_cert::TyCert;

/// Named cap on the exhaustive enumeration (the state-space bound guard).
pub const MAX_ENUM_STATES: usize = 4096;

/// One replayed counterexample step.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TraceStep {
    /// Action fired (or `<init>`).
    pub action: String,
    /// Resulting state, rendered `var=value, …`.
    pub state: String,
}

/// Errors of the finite lane. Every variant is a FAIL-CLOSED refusal: nothing
/// registers unless the whole chain succeeds.
#[derive(Debug, thiserror::Error)]
pub enum FiniteError {
    /// A variable sort outside `Int`/`Nat`/`[lo..hi -> BOOLEAN]`.
    #[error("unsupported variable sort for {var}: {sort:?}")]
    UnsupportedSort {
        /// Variable name.
        var: String,
        /// The offending sort text.
        sort: String,
    },
    /// A named operator is missing from `spec_src`.
    #[error("operator {0:?} not found in spec_src")]
    OperatorNotFound(String),
    /// Tokenizer/parser failure.
    #[error("parse error: {0}")]
    Parse(String),
    /// Structurally outside the S4 fragment.
    #[error("out of the S4 finite fragment: {0}")]
    Fragment(String),
    /// A negative value cannot be represented in the Nat encoding.
    #[error("negative value outside the Nat fragment (fail closed): {context}")]
    NegativeValue {
        /// Where the negative value arose.
        context: String,
    },
    /// Int semantics and Nat-truncating semantics disagree on a verdict or
    /// value the kernel proof would touch.
    #[error("Int/Nat truncation divergence (fail closed): {context}")]
    TruncationDivergence {
        /// Where the divergence arose.
        context: String,
    },
    /// Function access outside the declared domain.
    #[error("function index out of domain: {fn_var}[{index}]")]
    OutOfDomain {
        /// Function variable.
        fn_var: String,
        /// Offending index.
        index: i64,
    },
    /// The state-space bound guard: refuse oversize enumeration.
    #[error(
        "state-space bound exceeded: visited {visited} states, cap {cap} \
         (refusing oversize enumeration; certify at a small cfg bound and \
         conform at capacity instead)"
    )]
    StateSpaceBoundExceeded {
        /// States visited when the cap tripped.
        visited: usize,
        /// The named cap ([`MAX_ENUM_STATES`]).
        cap: usize,
    },
    /// Mixed-radix packing would overflow the pack cap.
    #[error("packed-state overflow: slot-bound product exceeds the pack cap")]
    PackOverflow,
    /// A reachable state violates an invariant: genuine falsification, with a
    /// step-replayed in-process trace. Nothing certifies.
    #[error(
        "FALSIFIED: reachable state violates invariant {invariant} \
         (replay_validated={replay_validated}); trace: {trace:?}"
    )]
    Falsified {
        /// The violated invariant's name.
        invariant: String,
        /// Replayed trace from the initial state to the violation.
        trace: Vec<TraceStep>,
        /// Whether the trace re-fired step-by-step through the transition
        /// relation (validate-before-publish).
        replay_validated: bool,
    },
    /// A product name is already declared (the squat vector, closed).
    #[error("name collision on {0} (refusing to overwrite or silently skip)")]
    NameCollision(String),
    /// A blessed vocabulary name is bound to a DIFFERENT definition.
    #[error(
        "blessed vocabulary {name} is already declared with a DIFFERENT \
         definition (name-squat): refusing to build on it"
    )]
    VocabularySquatted {
        /// The squatted constant.
        name: String,
    },
    /// The environment lacks required prelude vocabulary.
    #[error(
        "environment is missing prelude vocabulary {missing:?} — build the \
         recheck environment with Environment::with_prelude()"
    )]
    MissingPrelude {
        /// The absent constants.
        missing: Vec<String>,
    },
    /// Kernel/environment error (type-check rejection included).
    #[error("kernel/environment error: {0}")]
    Env(String),
    /// Internal invariant violation (a bug in this crate, never a proof).
    #[error("internal invariant violated: {0}")]
    Internal(String),
}

/// Registration evidence: timings + the post-registration audit.
#[derive(Debug, Clone)]
pub struct RegistrationEvidence {
    /// Wall time to register the checker definition.
    pub check_ms: f64,
    /// Wall time for the `rfl` leg — the kernel's evaluation of the checker.
    pub rfl_ms: f64,
    /// Wall time to check the soundness lemma.
    pub sound_ms: f64,
    /// Wall time to check the final theorem.
    pub thm_ms: f64,
    /// `ProofQuality` of the final theorem (must be `Constructive`).
    pub proof_quality: String,
    /// Axiom closure of the final theorem.
    pub axiom_deps: Vec<String>,
}

/// The success report of the finite product.
#[derive(Debug, Clone)]
pub struct FiniteReport {
    /// Machine name (from the MODULE line).
    pub machine: String,
    /// Names of the four registered declarations.
    pub registered: [String; 4],
    /// Number of reachable states enumerated (the J set).
    pub reachable_states: usize,
    /// Per-slot `(display, bound)` packing manifest.
    pub manifest: Vec<(String, u64)>,
    /// Number of Bool leaves in the checker.
    pub check_leaf_count: usize,
    /// Wall time of the dual-semantics exploration.
    pub explore_ms: f64,
    /// Wall time of the CIC encoding.
    pub encode_ms: f64,
    /// Kernel registration evidence.
    pub evidence: RegistrationEvidence,
    /// Honest approximation notes (the semantic-fidelity meter).
    pub fidelity_notes: Vec<String>,
}

/// THE ENTRY POINT: multi-variable finite-fragment reconstruction.
///
/// Parses + expands the machine from the cert, explores exhaustively
/// (dual-semantics, fail-closed), encodes, and registers the four-declaration
/// kernel-closed product under `thm_name`. See the module docs for the exact
/// artifact shapes.
pub fn register_ty_cert_safety_finite(
    env: &mut Environment,
    thm_name: &str,
    cert: &TyCert,
) -> Result<FiniteReport, FiniteError> {
    let m = FiniteMachine::from_cert(cert)?;
    let t = Instant::now();
    let explored = m.explore()?;
    let explore_ms = t.elapsed().as_secs_f64() * 1e3;
    let t = Instant::now();
    let enc = encode_finite(&m, &explored, thm_name)?;
    let encode_ms = t.elapsed().as_secs_f64() * 1e3;
    let evidence = register_finite_encoded(env, &enc)?;
    Ok(FiniteReport {
        machine: m.name.clone(),
        registered: [
            enc.check_name.clone(),
            enc.rfl_name.clone(),
            enc.sound_name.clone(),
            enc.thm_name.clone(),
        ],
        reachable_states: explored.reachable.len(),
        manifest: enc.manifest.clone(),
        check_leaf_count: enc.check_leaf_count,
        explore_ms,
        encode_ms,
        evidence,
        fidelity_notes: finite_fidelity_notes(&m, &enc),
    })
}

/// Honest per-variable fidelity notes for the finite product.
fn finite_fidelity_notes(m: &FiniteMachine, enc: &FiniteEncoded) -> Vec<String> {
    let mut notes = Vec::new();
    notes.push(format!(
        "State is the mixed-radix packing of {} slot(s) into State := Nat \
         (bounds {:?}); the packing is a bijection onto [0, ΠBᵢ) and every \
         proof instantiation is at packed literals of explored states.",
        enc.manifest.len(),
        enc.manifest
    ));
    for v in &m.vars {
        notes.push(format!(
            "VAR {} is modelled as cfg-bounded Nat slot(s); dual Int/Nat \
             evaluation verified agreement on every guard, update, and \
             invariant the proof touches (divergence fails closed).",
            v.name
        ));
    }
    notes
}

// ── TLAfin shared vocabulary ───────────────────────────────────────────────

fn c(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

/// The three `TLAfin.*` helper definitions the encoder emits:
/// `cond : Bool → Nat → Nat → Nat`, `b2n : Bool → Nat`,
/// `bimpl : Bool → Bool → Bool` — all reducible `Bool.rec` definitions.
fn tlafin_expected() -> Vec<(String, Expr, Expr)> {
    let bool_c = c("Bool");
    let nat_c = c("Nat");
    let bool_rec_1 = Expr::const_(
        Name::from_string("Bool.rec"),
        vec![Level::succ(Level::zero())],
    );
    let motive_nat = Expr::lam(BinderInfo::Default, bool_c.clone(), nat_c.clone());
    let motive_bool = Expr::lam(BinderInfo::Default, bool_c.clone(), bool_c.clone());

    // TLAfin.cond := λ c t e, Bool.rec (λ _, Nat) e t c
    let cond_ty = Expr::arrow(
        bool_c.clone(),
        Expr::arrow(nat_c.clone(), Expr::arrow(nat_c.clone(), nat_c.clone())),
    );
    let cond_val = {
        let mut b = B::new();
        let (c_id, cv) = b.fresh();
        let (t_id, tv) = b.fresh();
        let (e_id, ev) = b.fresh();
        let body = Expr::apps(bool_rec_1.clone(), [motive_nat.clone(), ev, tv, cv]);
        let l = b.lam(e_id, BinderInfo::Default, nat_c.clone(), body);
        let l = b.lam(t_id, BinderInfo::Default, nat_c.clone(), l);
        b.finish(b.lam(c_id, BinderInfo::Default, bool_c.clone(), l))
    };

    // TLAfin.b2n := λ b, Bool.rec (λ _, Nat) 0 1 b
    let b2n_ty = Expr::arrow(bool_c.clone(), nat_c.clone());
    let b2n_val = {
        let mut b = B::new();
        let (x_id, x) = b.fresh();
        let body = Expr::apps(
            bool_rec_1.clone(),
            [motive_nat, Expr::nat_lit(0), Expr::nat_lit(1), x],
        );
        b.finish(b.lam(x_id, BinderInfo::Default, bool_c.clone(), body))
    };

    // TLAfin.bimpl := λ a b, Bool.rec (λ _, Bool) true b a
    let bimpl_ty = Expr::arrow(bool_c.clone(), Expr::arrow(bool_c.clone(), bool_c.clone()));
    let bimpl_val = {
        let mut b = B::new();
        let (a_id, a) = b.fresh();
        let (y_id, y) = b.fresh();
        let body = Expr::apps(bool_rec_1, [motive_bool, c("Bool.true"), y, a]);
        let l = b.lam(y_id, BinderInfo::Default, bool_c.clone(), body);
        b.finish(b.lam(a_id, BinderInfo::Default, bool_c, l))
    };

    vec![
        ("TLAfin.cond".to_string(), cond_ty, cond_val),
        ("TLAfin.b2n".to_string(), b2n_ty, b2n_val),
        ("TLAfin.bimpl".to_string(), bimpl_ty, bimpl_val),
    ]
}

/// Register the `TLAfin.*` trio; if a name already exists it must match the
/// expected definition EXACTLY (type and value), else it is a squat and we
/// refuse — a bogus `TLAfin.cond` would change the meaning of every statement
/// mentioning it.
fn register_tlafin_vocabulary(env: &mut Environment) -> Result<(), FiniteError> {
    for (name, ty, val) in tlafin_expected() {
        let n = Name::from_string(&name);
        match env.get_const(&n) {
            None => env
                .add_decl(Declaration::Definition {
                    name: n,
                    level_params: vec![],
                    type_: ty,
                    value: val,
                    is_reducible: true,
                })
                .map_err(|e| FiniteError::Env(format!("registering {name}: {e:?}")))?,
            Some(info) => {
                let same = info.kind == ConstantKind::Definition
                    && info.type_ == ty
                    && info.value.as_ref() == Some(&val);
                if !same {
                    return Err(FiniteError::VocabularySquatted { name });
                }
            }
        }
    }
    Ok(())
}

/// The blessed `TLAsem.*` names the finite conclusion mentions.
const TLASEM_BLESSED: &[&str] = &[
    "TLAsem.drop",
    "TLAsem.Lift",
    "TLAsem.SemBox",
    "TLAsem.Sat",
    "TLAsem.Runs",
    "TLAsem.InductiveInvariantSound",
];

/// Verify the target env's `TLAsem.*` declarations are EXACTLY the blessed
/// encoding (rebuilt in a scratch env) — closing the def_reducible
/// skip-if-exists squat vector. `pub(crate)` so the 1-variable products
/// ([`crate::ty_cert`]) run the SAME check (they build on the same idempotent
/// TLAsem registration and were exposed to the same squat vector).
pub(crate) fn verify_tlasem_integrity(env: &Environment) -> Result<(), FiniteError> {
    static SCRATCH_TLASEM: std::sync::OnceLock<Environment> = std::sync::OnceLock::new();
    let scratch = SCRATCH_TLASEM.get_or_init(|| {
        let mut scratch = Environment::new();
        semantics::register_inductive_invariant_sound(&mut scratch)
            .expect("registering the blessed TLAsem module on a bare env");
        scratch
    });
    for name in TLASEM_BLESSED {
        let n = Name::from_string(name);
        let expected = scratch
            .get_const(&n)
            .ok_or_else(|| FiniteError::Internal(format!("scratch env lacks {name}")))?;
        let got = env.get_const(&n).ok_or_else(|| {
            FiniteError::Internal(format!("target env lacks {name} after registration"))
        })?;
        let same =
            got.kind == expected.kind && got.type_ == expected.type_ && got.value == expected.value;
        if !same {
            return Err(FiniteError::VocabularySquatted {
                name: (*name).to_string(),
            });
        }
    }
    Ok(())
}

/// Prelude vocabulary the encoder/proofs mention. Presence is required;
/// definitions are integrity-checked against a fresh `with_prelude()` env
/// (defense-in-depth — the sanctioned recheck flow already uses a fresh env).
const PRELUDE_VOCAB: &[&str] = &[
    "Bool",
    "Bool.true",
    "Bool.false",
    "Bool.and",
    "Bool.or",
    "Bool.not",
    "Bool.rec",
    "Bool.noConfusion",
    "Bool.and_eq_true_left",
    "Bool.and_eq_true_right",
    "Nat",
    "Nat.add",
    "Nat.sub",
    "Nat.mul",
    "Nat.div",
    "Nat.mod",
    "Nat.beq",
    "Nat.ble",
    "Eq",
    "Eq.refl",
    "Eq.symm",
    "Eq.subst",
    "And",
    "And.left",
    "And.right",
    "Or",
    "Or.inl",
    "Or.inr",
    "Or.rec",
];

fn verify_prelude_vocabulary(env: &Environment) -> Result<(), FiniteError> {
    let missing: Vec<String> = PRELUDE_VOCAB
        .iter()
        .filter(|n| env.get_const(&Name::from_string(n)).is_none())
        .map(|n| (*n).to_string())
        .collect();
    if !missing.is_empty() {
        return Err(FiniteError::MissingPrelude { missing });
    }
    // The reference prelude is immutable once built; cache it process-wide so
    // repeated registrations do not pay the full prelude construction.
    static REFERENCE_PRELUDE: std::sync::OnceLock<Environment> = std::sync::OnceLock::new();
    let fresh = REFERENCE_PRELUDE.get_or_init(Environment::with_prelude);
    for name in PRELUDE_VOCAB {
        let n = Name::from_string(name);
        let Some(expected) = fresh.get_const(&n) else {
            // Not part of the reference prelude (should not happen); presence
            // was already checked, so accept.
            continue;
        };
        let Some(got) = env.get_const(&n) else {
            continue;
        };
        let same =
            got.kind == expected.kind && got.type_ == expected.type_ && got.value == expected.value;
        if !same {
            return Err(FiniteError::VocabularySquatted {
                name: (*name).to_string(),
            });
        }
    }
    Ok(())
}

/// Register the four encoded declarations. Errors on ANY name collision.
///
/// ATOMIC: every mutation is staged on a clone of `env` and committed only on
/// full success, so a failure at ANY leg (including a kernel rejection of the
/// rfl leg on a tampered checker) leaves the caller's environment untouched —
/// no half-registered products, no poisoned names on retry.
pub fn register_finite_encoded(
    env: &mut Environment,
    enc: &FiniteEncoded,
) -> Result<RegistrationEvidence, FiniteError> {
    let staged = &mut env.clone();

    // The keystone + semantics must be present (idempotent), then verified
    // unsquatted; TLAfin vocabulary likewise.
    semantics::register_inductive_invariant_sound(staged)
        .map_err(|e| FiniteError::Env(format!("registering TLAsem: {e:?}")))?;
    verify_prelude_vocabulary(staged)?;
    register_tlafin_vocabulary(staged)?;
    verify_tlasem_integrity(staged)?;

    for name in [
        &enc.check_name,
        &enc.rfl_name,
        &enc.sound_name,
        &enc.thm_name,
    ] {
        if staged.get_const(&Name::from_string(name)).is_some() {
            return Err(FiniteError::NameCollision(name.clone()));
        }
    }

    let lvl1 = Level::succ(Level::zero());
    let eq_bool_true = |a: Expr| -> Expr {
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![lvl1.clone()]),
            [c("Bool"), a, c("Bool.true")],
        )
    };

    // 1. the checker definition
    let t = Instant::now();
    staged
        .add_decl(Declaration::Definition {
            name: Name::from_string(&enc.check_name),
            level_params: vec![],
            type_: c("Bool"),
            value: enc.check.clone(),
            is_reducible: true,
        })
        .map_err(|e| FiniteError::Env(format!("registering {}: {e:?}", enc.check_name)))?;
    let check_ms = t.elapsed().as_secs_f64() * 1e3;

    // 2. the rfl leg — the kernel EVALUATES the checker here.
    let t = Instant::now();
    staged
        .add_decl(Declaration::Theorem {
            name: Name::from_string(&enc.rfl_name),
            level_params: vec![],
            type_: eq_bool_true(c(&enc.check_name)),
            value: Expr::apps(
                Expr::const_(Name::from_string("Eq.refl"), vec![lvl1.clone()]),
                [c("Bool"), c("Bool.true")],
            ),
        })
        .map_err(|e| FiniteError::Env(format!("rfl leg {}: {e:?}", enc.rfl_name)))?;
    let rfl_ms = t.elapsed().as_secs_f64() * 1e3;

    // 3. the soundness lemma
    let t = Instant::now();
    staged
        .add_decl(Declaration::Theorem {
            name: Name::from_string(&enc.sound_name),
            level_params: vec![],
            type_: enc.sound_type.clone(),
            value: enc.sound_value.clone(),
        })
        .map_err(|e| FiniteError::Env(format!("soundness lemma {}: {e:?}", enc.sound_name)))?;
    let sound_ms = t.elapsed().as_secs_f64() * 1e3;

    // 4. the final bare-conclusion theorem
    let t = Instant::now();
    staged
        .add_decl(Declaration::Theorem {
            name: Name::from_string(&enc.thm_name),
            level_params: vec![],
            type_: enc.conclusion.clone(),
            value: Expr::app(c(&enc.sound_name), c(&enc.rfl_name)),
        })
        .map_err(|e| FiniteError::Env(format!("final theorem {}: {e:?}", enc.thm_name)))?;
    let thm_ms = t.elapsed().as_secs_f64() * 1e3;

    let thm = Name::from_string(&enc.thm_name);
    let quality = staged
        .proof_quality(&thm)
        .ok_or_else(|| FiniteError::Internal("proof_quality of the final theorem".into()))?;
    if quality != ProofQuality::Constructive {
        return Err(FiniteError::Env(format!(
            "final theorem is not Constructive: {quality:?}"
        )));
    }
    let axiom_deps: Vec<String> = staged
        .axiom_deps(&thm)
        .map(|s| s.iter().map(|n| n.to_string()).collect())
        .unwrap_or_default();
    for dep in &axiom_deps {
        if dep.contains("sorry") || dep.contains("Sorry") || dep.contains("trusted") {
            return Err(FiniteError::Env(format!(
                "forbidden axiom dependency in the closure: {dep}"
            )));
        }
    }

    // Full success: commit the staged environment to the caller.
    *env = std::mem::take(staged);
    Ok(RegistrationEvidence {
        check_ms,
        rfl_ms,
        sound_ms,
        thm_ms,
        proof_quality: format!("{quality:?}"),
        axiom_deps,
    })
}
