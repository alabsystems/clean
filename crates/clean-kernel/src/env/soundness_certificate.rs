// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! THE SOUNDNESS CERTIFICATE — one mechanical check that proves Clean sound.
//!
//! See `designs/2026-06-08-soundness-certificate.md` (authoritative). The
//! certificate runs five mechanical claims over the FULL environment and emits a
//! single auditable certificate. It FAILS CLOSED on any violation; GREEN ⟺ the
//! environment is consistent (no closed proof of `False`) RELATIVE to the
//! explicitly-enumerated Trusted Base (the kernel checker + the printed,
//! justified axiom allowlist).
//!
//! | Claim | Statement |
//! |---|---|
//! | **C1 Total re-verification** | every `Theorem`/`Definition` re-type-checks: `infer_type(value)` is `def_eq` to the declared `type_`. Independent of HOW the decl was registered, so it catches any VALUE-BEARING fabrication (Theorem/Definition). `Axiom`-kind decls carry no value and are SKIPPED by C1; a fabricated axiom's TYPE is instead enumerated and golden-pinned by C2 (and refutation-tested by C4/C4'), not re-type-checked here. |
//! | **C2 TCB enumeration** | the FULL set of `Axiom`-kind names IS the trusted axiom base; partitioned (foundational / admitted-domain / other-admitted) and pinned against a checked-in golden so ADDING an axiom is a reviewed, diff-visible event. Zero trust markers among them. |
//! | **C3 No trust markers reachable** | no declaration's transitive `axiom_deps` closure reaches `sorry`/`sorryAx`/`trusted*`. |
//! | **C4 Carrier-generic refutation** | every admitted axiom C4 can EXAMINE (its conclusion reduces to a concrete decidable prop) is non-refutable (no closed junk counterexample). Refutable-among-examined set EMPTY. C4 reports a HONEST coverage split: axioms whose conclusion stays stuck on an abstract/opaque carrier are OPAQUE — counted as `opaque_unexamined` and TRUSTED, NOT CHECKED (not laundered as "checked safe"). `is_sound()` is unchanged (requires `refutable == 0`). |
//! | **C4' Opacity-transparency** | no `Declaration::Opaque`-with-body carrier MASKS a refutable admitted axiom: for each such carrier, making it a transparent reducible `Definition` (same body) and re-running C4 over the axioms that mention it produces ZERO newly-refutable axioms. Catches the `Rat.abs`-class bug where an opaque identity body hid `0 ≤ \|q\|` ≡ `0 ≤ q` (false for `q < 0`) from C4's δ-reduction. |
//! | **C5 Exploit resistance** | the kernel REJECTS the deep-nested `False`-proof corpus (10/10). |
//!
//! The certificate is computed over whatever `Environment` it is called on. The
//! canonical comprehensive overlay env is built by
//! [`Environment::soundness_certificate_env`]; the always-on test and the
//! `clean audit soundness` CLI verb both run over it, so its golden TCB
//! (`data/soundness_tcb.json`) always matches and `is_sound()` is consistent.

use std::collections::BTreeSet;
use std::fmt;

use serde::Serialize;

use super::axiom_audit::{
    is_foundational_axiom, is_trust_marker, ADMITTED_DOMAIN_AXIOMS, FOUNDATIONAL_AXIOMS,
};
use super::carrier_refutation::{
    scan_admitted_axioms, scan_opacity_masked_axioms, CarrierCensus, MaskedAxiom,
};
use super::types::ConstantKind;
use super::Environment;
use crate::name::Name;
use crate::quot::QuotKind;
use crate::tc::TypeChecker;

/// The kernel revision string baked into the certificate header. We use the
/// crate version plus the `#![forbid(unsafe_code)]` posture — the certificate is
/// relative to "this kernel build".
const KERNEL_CRATE: &str = "clean-kernel";
const KERNEL_VERSION: &str = env!("CARGO_PKG_VERSION");

/// The checked-in golden TCB file, embedded at compile time. Comparing the live
/// axiom set against it makes ADDING an axiom a reviewed, diff-visible event.
/// The file lives at the workspace root `data/` (the kernel crate is two levels
/// down: `crates/clean-kernel/src/env/` → `../../../../data`).
const GOLDEN_TCB_JSON: &str = include_str!("../../../../data/soundness_tcb.json");

// ════════════════════════════════ C1 ════════════════════════════════

/// C1 — Total re-verification tally.
#[derive(Clone, Debug, Default, Serialize)]
pub struct C1Reverification {
    /// Number of `Theorem`/`Definition` declarations carrying a value that were
    /// re-checked through the kernel.
    pub checked: usize,
    /// Number that passed (`infer_type(value)` is `def_eq` to `type_`).
    pub passed: usize,
    /// Number that FAILED re-verification.
    pub failed: usize,
    /// Names of the failing declarations (sorted).
    pub failures: Vec<String>,
    /// G2 SYMMETRY: number of `Axiom`-kind (and other value-less) declarations
    /// whose declared TYPE was re-checked for well-formedness via `infer_sort`
    /// (no leaked fvar/mvar, sort inhabited, level-scope closed). This does NOT
    /// refute the axiom's TRUTH — that is C2's golden-pin + C4/C5's job — but it
    /// closes the "axiom-shaped smuggle" hole so C1 is symmetric across kinds: an
    /// `add_decl_unchecked(Axiom{ type_: <ill-formed> })` bypass is now caught.
    pub axiom_types_checked: usize,
    /// Number of axiom types that passed the `infer_sort` well-formedness check.
    pub axiom_types_passed: usize,
    /// Number of axiom types that FAILED the well-formedness check.
    pub axiom_types_failed: usize,
    /// Names of the axioms whose declared type failed well-formedness (sorted).
    pub axiom_type_failures: Vec<String>,
    /// Wall-clock runtime of the re-verification loop, in milliseconds.
    pub runtime_ms: u64,
}

impl C1Reverification {
    #[must_use]
    fn ok(&self) -> bool {
        self.failed == 0
            && self.failures.is_empty()
            && self.axiom_types_failed == 0
            && self.axiom_type_failures.is_empty()
    }
}

// ════════════════════════════════ C2 ════════════════════════════════

/// C2 — TCB enumeration (the FULL axiom base), partitioned + golden-pinned.
#[derive(Clone, Debug, Default, Serialize)]
pub struct C2TcbEnumeration {
    /// Every `Axiom`-kind name in the env (sorted), INCLUDING trust markers —
    /// the full honest enumeration of axiom-kind declarations.
    pub all_axioms: Vec<String>,
    /// The TRUSTED axiom base: every `Axiom`-kind name EXCEPT the trust markers
    /// (sorted). This is what the golden pins and `is_sound` compares.
    pub trusted_axioms: Vec<String>,
    /// Foundational logical-foundation axioms (∈ `FOUNDATIONAL_AXIOMS`).
    pub foundational: Vec<String>,
    /// Admitted domain axioms explicitly catalogued (∈ `ADMITTED_DOMAIN_AXIOMS`).
    pub admitted_domain: Vec<String>,
    /// Other admitted axioms — domain axioms over opaque/faithful carriers, not
    /// in either curated list (expected to be hundreds; honest and enumerated).
    pub other_admitted: Vec<String>,
    /// Trust markers (`sorry`/`sorryAx`/`trusted*`) registered as axiom-kind
    /// declarations. These exist in EVERY env (that is how `sorry` works) but are
    /// NOT part of the trusted base — they are governed by C3 (no declaration may
    /// REACH one). C2 asserts none leaked into the trusted partitions (which
    /// holds by construction). MUST NOT appear in `trusted_axioms`.
    pub trust_markers: Vec<String>,
    /// Builtin quotient primitives (`Quot`, `Quot.mk`, `Quot.lift`, `Quot.ind`):
    /// type-former + constructor + two eliminators with kernel-implemented typing
    /// and reduction rules. NOT axioms (part of the kernel checker); enumerated
    /// here transparently and excluded from `all_axioms`/`trusted_axioms`. Only
    /// `Quot.sound` (a genuine `Prop` axiom) is counted, in the partitions above.
    /// Mirrors Lean's `#print axioms`, which lists `Quot.sound` but never these.
    pub builtin_quot_primitives: Vec<String>,
    /// Whether the live TRUSTED axiom set exactly equals the checked-in golden.
    pub matches_golden: bool,
    /// If the live set diverges from the golden: axioms present live but not in
    /// the golden (newly-introduced, must be reviewed).
    pub added_vs_golden: Vec<String>,
    /// If the live set diverges from the golden: axioms in the golden but no
    /// longer live (removed/eliminated — a TCB shrink, also diff-visible).
    pub removed_vs_golden: Vec<String>,
}

impl C2TcbEnumeration {
    #[must_use]
    fn ok(&self) -> bool {
        // No trust marker may leak into the trusted axiom base, and the live
        // trusted set must exactly equal the reviewed golden. Trust markers
        // EXISTING as declarations is expected and sound (governed by C3).
        let no_trust_in_trusted = self
            .trust_markers
            .iter()
            .all(|m| !self.trusted_axioms.contains(m));
        no_trust_in_trusted && self.matches_golden
    }
}

/// On-disk golden TCB schema (also the regeneration output).
#[derive(Clone, Debug, Serialize, serde::Deserialize)]
pub struct GoldenTcb {
    /// Schema marker.
    pub schema: String,
    /// Total axiom count.
    pub axiom_count: usize,
    /// Count of foundational axioms.
    pub foundational_count: usize,
    /// Count of admitted-domain axioms.
    pub admitted_domain_count: usize,
    /// Count of other-admitted axioms.
    pub other_admitted_count: usize,
    /// The full sorted axiom-name set.
    pub axioms: Vec<String>,
}

const GOLDEN_SCHEMA: &str = "clean-soundness-tcb-v1";

// ════════════════════════════════ C3 ════════════════════════════════

/// C3 — No trust markers reachable in any declaration's axiom closure.
#[derive(Clone, Debug, Default, Serialize)]
pub struct C3TrustMarkers {
    /// Number of declarations whose transitive closure was inspected.
    pub declarations_scanned: usize,
    /// Number whose closure reaches a trust marker (MUST be 0).
    pub reaching_trust_marker: usize,
    /// `(declaration, trust-marker)` pairs found (sorted). MUST be empty.
    pub violations: Vec<String>,
}

impl C3TrustMarkers {
    #[must_use]
    fn ok(&self) -> bool {
        self.reaching_trust_marker == 0 && self.violations.is_empty()
    }
}

// ════════════════════════════════ C4 ════════════════════════════════

/// C4 coverage split — the honesty distinction the reviewer demanded. C4 cannot
/// examine an axiom whose conclusion never reduces to a concrete decidable prop
/// (it is over an opaque/abstract carrier). For those, "not refutable" is
/// VACUOUS, not "checked safe". This struct surfaces that split so the
/// certificate stops laundering trusted-not-checked axioms together with
/// genuinely-examined ones.
///
/// Invariant: `examined + opaque_unexamined == admitted_scanned` and
/// `refutable ⊆ examined` (a refuted axiom was, by definition, examined).
#[derive(Clone, Copy, Debug, Default, Serialize)]
pub struct C4Coverage {
    /// Number of admitted axioms C4 GENUINELY EXAMINED: the conclusion reduced
    /// to a concrete decidable prop under some assignment, so a counterexample
    /// would have been found. This is the *checked* part of the trusted base.
    pub examined: usize,
    /// Number of examined axioms found REFUTABLE (a closed counterexample
    /// exists). MUST be 0 for soundness. `refutable ≤ examined`.
    pub refutable: usize,
    /// Number of admitted axioms OPAQUE to refutation: the conclusion stayed
    /// stuck on an abstract carrier with no closed-decidable form, so C4 could
    /// NOT examine them. For these, "not refutable" is vacuous — they are
    /// TRUSTED, NOT CHECKED. (Honest faith, not laundered as "checked safe".)
    pub opaque_unexamined: usize,
}

/// C4 — Carrier-generic refutation resistance.
#[derive(Clone, Debug, Default, Serialize)]
pub struct C4Refutation {
    /// Number of admitted axioms scanned (every non-foundational, non-trust
    /// `Axiom`-kind constant).
    pub admitted_scanned: usize,
    /// Names of admitted axioms found REFUTABLE (MUST be empty).
    pub refutable: Vec<String>,
    /// Names of admitted axioms C4 genuinely EXAMINED (concrete-carrier
    /// conclusion reduced to a decidable prop, counterexample-free). Sorted.
    pub examined: Vec<String>,
    /// Names of admitted axioms OPAQUE to refutation (abstract carrier, no
    /// closed-decidable form) — TRUSTED, NOT CHECKED. Sorted.
    pub opaque_unexamined: Vec<String>,
    /// The concrete-inductive-carrier census (junk-admitting classification).
    pub carriers: Vec<CarrierCensus>,
}

impl C4Refutation {
    /// C4 PASSES iff no examined axiom is refutable. `is_sound()` semantics are
    /// UNCHANGED — the `opaque_unexamined` count is reported, not hidden, and
    /// never affects the verdict (opaque axioms are governed by T2/faith).
    #[must_use]
    fn ok(&self) -> bool {
        self.refutable.is_empty()
    }

    /// The reported faith/checked coverage split.
    #[must_use]
    fn coverage(&self) -> C4Coverage {
        C4Coverage {
            examined: self.examined.len(),
            refutable: self.refutable.len(),
            opaque_unexamined: self.opaque_unexamined.len(),
        }
    }

    /// Number of carriers classified junk-admitting (for the report).
    #[must_use]
    fn junk_carriers(&self) -> usize {
        self.carriers.iter().filter(|c| c.junk_admitting).count()
    }
}

// ════════════════════════════════ C4' ════════════════════════════════

/// C4' — Opacity-transparency refutation. For every `Declaration::Opaque`
/// carrier that has a body, the certificate makes it a transparent reducible
/// `Definition` (same body) and re-runs the C4 engine over the admitted axioms
/// that mention it. An axiom that becomes refutable ONLY once the carrier
/// unfolds was being MASKED by the carrier's opacity (the `Rat.abs` bug). The
/// masked set MUST be empty.
#[derive(Clone, Debug, Default, Serialize)]
pub struct C4Opacity {
    /// Number of `Opaque`-with-body carriers examined (the risk set).
    pub checked: usize,
    /// Number of admitted axioms unmasked (refutable only once the carrier was
    /// made transparent). MUST be 0.
    pub refutable: usize,
    /// The masked-axiom findings (`axiom` + masking `carrier`). MUST be empty.
    pub masked: Vec<MaskedAxiom>,
}

impl C4Opacity {
    #[must_use]
    fn ok(&self) -> bool {
        self.refutable == 0 && self.masked.is_empty()
    }
}

// ════════════════════════════════ C5 ════════════════════════════════

/// C5 — Exploit resistance (the deep-nested `False`-proof corpus).
#[derive(Clone, Debug, Default, Serialize)]
pub struct C5ExploitResistance {
    /// Number of exploit attacks attempted.
    pub attacks: usize,
    /// Number the kernel correctly REJECTED.
    pub rejected: usize,
    /// Names of attacks the kernel FAILED to reject (MUST be empty).
    pub accepted: Vec<String>,
}

impl C5ExploitResistance {
    #[must_use]
    fn ok(&self) -> bool {
        self.attacks > 0 && self.rejected == self.attacks && self.accepted.is_empty()
    }
}

// ════════════════════════════ trusted base ════════════════════════════

/// The enumerated Trusted Base printed by the certificate.
#[derive(Clone, Debug, Default, Serialize)]
pub struct TrustedBase {
    /// Kernel checker identity.
    pub kernel: String,
    /// `#![forbid(unsafe_code)]` posture.
    pub forbid_unsafe: bool,
    /// Foundational logical-foundation axioms.
    pub foundational_axioms: Vec<String>,
    /// Justified admitted domain axioms (each non-refutable / opaque-carrier).
    pub admitted_axioms: Vec<String>,
    /// Total trusted axiom count (foundational + every admitted axiom).
    pub total_trusted_axioms: usize,
}

// ════════════════════════════ certificate ════════════════════════════

/// THE soundness certificate: the output of the single mechanical check.
#[derive(Clone, Debug, Serialize)]
pub struct SoundnessCertificate {
    /// C1 — total re-verification.
    pub c1: C1Reverification,
    /// C2 — TCB enumeration + golden pin.
    pub c2: C2TcbEnumeration,
    /// C3 — no trust markers reachable.
    pub c3: C3TrustMarkers,
    /// C4 — carrier-generic refutation resistance.
    pub c4: C4Refutation,
    /// C4' — opacity-transparency refutation (no opaque carrier masks a
    /// refutable admitted axiom).
    pub c4_opacity: C4Opacity,
    /// C5 — exploit resistance.
    pub c5: C5ExploitResistance,
    /// The enumerated Trusted Base (everything else is proven).
    pub trusted_base: TrustedBase,
}

impl SoundnessCertificate {
    /// The system is SOUND iff all claims pass: every decl re-verifies (C1),
    /// the live axiom set equals the golden with zero trust markers (C2), no
    /// trust marker is reachable (C3), the refutable-admitted set is empty (C4),
    /// no opaque-with-body carrier masks a refutable admitted axiom (C4'), and
    /// every exploit is rejected (C5).
    #[must_use]
    pub fn is_sound(&self) -> bool {
        self.c1.ok()
            && self.c2.ok()
            && self.c3.ok()
            && self.c4.ok()
            && self.c4_opacity.ok()
            && self.c5.ok()
    }

    /// Serialize to the machine-readable JSON form.
    ///
    /// # Errors
    /// Returns a `serde_json` error only if serialization fails (it cannot for
    /// this all-owned struct).
    pub fn to_json(&self) -> Result<String, serde_json::Error> {
        serde_json::to_string_pretty(self)
    }

    /// Regenerate the golden TCB JSON from the live axiom set of `env`. Used to
    /// (re)create `data/soundness_tcb.json` on first run / after a reviewed
    /// axiom change.
    #[must_use]
    pub fn golden_from_env(env: &Environment) -> String {
        let p = partition_axioms(env);
        let golden = GoldenTcb {
            schema: GOLDEN_SCHEMA.to_owned(),
            axiom_count: p.trusted.len(),
            foundational_count: p.foundational.len(),
            admitted_domain_count: p.admitted_domain.len(),
            other_admitted_count: p.other.len(),
            axioms: p.trusted,
        };
        // Pretty + trailing newline (matches `serde_json::to_string_pretty`
        // convention used by the other `data/*.json` goldens).
        format!(
            "{}\n",
            serde_json::to_string_pretty(&golden).unwrap_or_default()
        )
    }
}

/// The axiom-name partition of an environment.
struct AxiomPartition {
    /// Every genuine `Axiom`-kind name (incl. trust markers), EXCLUDING the
    /// builtin quotient primitives (see `builtin_quot`).
    all: Vec<String>,
    /// The trusted axiom base (every axiom EXCEPT trust markers and builtin
    /// quotient primitives).
    trusted: Vec<String>,
    /// Foundational logical-foundation axioms.
    foundational: Vec<String>,
    /// Admitted domain axioms (∈ `ADMITTED_DOMAIN_AXIOMS`).
    admitted_domain: Vec<String>,
    /// Other admitted axioms (domain axioms over opaque/faithful carriers).
    other: Vec<String>,
    /// Trust markers registered as axiom-kind declarations.
    trust: Vec<String>,
    /// Builtin quotient primitives (`Quot`, `Quot.mk`, `Quot.lift`, `Quot.ind`)
    /// — the type-former, constructor, and two eliminators. These are NOT
    /// asserted axioms: the kernel implements their typing (`quot::quot_*_type`)
    /// AND their reduction rule `Quot.lift f h (Quot.mk r a) ≡ f a`
    /// (`quot::try_quot_{lift,ind}_reduction`), so they belong to THE KERNEL
    /// CHECKER half of the Trusted Base, not the axiom allowlist. Lean's
    /// `#print axioms` never lists them (they are `Declaration.quotDecl`, not
    /// `axiomDecl`); only `Quot.sound` (a pure-`Prop` equality with no
    /// computational content) is a genuine axiom and stays in the partitions
    /// above. `init_quot` mirrors all five into `constants` as `Axiom`-kind
    /// purely for name resolution; the authoritative record is `env.quotients()`,
    /// which is what this bucket reads. Counting the four primitives as axioms
    /// would double-count the kernel (their rules are already trusted as "the
    /// kernel checker"). Enumerated here transparently, never hidden.
    builtin_quot: Vec<String>,
}

/// Partition every `Axiom`-kind name in `env`. Each returned vec is sorted.
fn partition_axioms(env: &Environment) -> AxiomPartition {
    let mut all = BTreeSet::new();
    let mut trusted = BTreeSet::new();
    let mut foundational = BTreeSet::new();
    let mut admitted_domain = BTreeSet::new();
    let mut other = BTreeSet::new();
    let mut trust = BTreeSet::new();
    let mut builtin_quot = BTreeSet::new();

    let admitted_set: BTreeSet<&str> = ADMITTED_DOMAIN_AXIOMS.iter().copied().collect();
    let foundational_set: BTreeSet<&str> = FOUNDATIONAL_AXIOMS.iter().copied().collect();

    for c in env.constants() {
        if c.kind != ConstantKind::Axiom {
            continue;
        }
        let name = c.name.to_string();

        // Builtin quotient primitives (Quot / Quot.mk / Quot.lift / Quot.ind)
        // are type-formers + eliminators with kernel-implemented typing AND
        // reduction rules — part of the kernel checker, not the axiom allowlist.
        // They are mirrored into `constants` as `Axiom`-kind only for name
        // lookup; `env.quotients()` is their authoritative home. Route them to
        // the transparent `builtin_quot` bucket (NOT the trusted axiom base).
        // `Quot.sound` (`QuotKind::Sound`) is a genuine axiom and falls through.
        if let Some(qv) = env.get_quot(&c.name) {
            if qv.kind != QuotKind::Sound {
                builtin_quot.insert(name);
                continue;
            }
        }

        all.insert(name.clone());

        if is_trust_marker(&c.name) {
            trust.insert(name);
            continue;
        }

        // Not a trust marker → part of the trusted axiom base.
        trusted.insert(name.clone());

        // A name may appear in both curated lists (the historical
        // FOUNDATIONAL_AXIOMS retains documentation entries that are excluded
        // from the Constructive gate). The admitted-domain classification is
        // authoritative per `is_foundational_axiom`, which excludes admitted
        // names from the foundational set.
        if admitted_set.contains(name.as_str()) {
            admitted_domain.insert(name);
        } else if is_foundational_axiom(&c.name) || foundational_set.contains(name.as_str()) {
            foundational.insert(name);
        } else {
            other.insert(name);
        }
    }

    AxiomPartition {
        all: all.into_iter().collect(),
        trusted: trusted.into_iter().collect(),
        foundational: foundational.into_iter().collect(),
        admitted_domain: admitted_domain.into_iter().collect(),
        other: other.into_iter().collect(),
        trust: trust.into_iter().collect(),
        builtin_quot: builtin_quot.into_iter().collect(),
    }
}

impl Environment {
    /// Build the canonical comprehensive overlay environment over which the
    /// Soundness Certificate is computed.
    ///
    /// This seeds the FULL set of math/NN-verification overlays — byte-for-byte
    /// the same surfaces `mathverse_shard build-native` seeds via
    /// `clean_mathverse::build_library_native::seed_native_environment` — so the
    /// certificate proves the ENTIRE shipped kernel corpus sound, not a curated
    /// subset. It is DETERMINISTIC and self-contained (no mathverse-crate
    /// dependency), so the always-on kernel test and the `clean audit soundness`
    /// CLI verb run over an identical env and share one golden TCB.
    ///
    /// ## Sorry-freedom (C3)
    ///
    /// Every `init_*` below is sorry-free: the historically `sorryAx`-backed IBP
    /// scaffolding (`NNVerify.w_*`, `NNVerify.ibp_linear_per_component`,
    /// `NNVerify.ibp_tightness_{base,step}`) is now PROVED constructively —
    /// `w_pos_nonneg`/`w_neg_nonpos`/`w_decompose` via the Rat lattice lemmas,
    /// and (off the faithful `ibp_linear_bounds`/`ibp_relu_bounds` Definitions)
    /// `ibp_linear_per_component` (T80 unlock) and `ibp_tightness_{base,step}`
    /// (R-weak unlock). No NNVerify IBP-scaffolding admitted axiom remains. The
    /// downstream theorems that compose them (`ibp_linear_sound`,
    /// `ibp_tightness_bound[_inductive]`) are therefore genuine sorry-free
    /// theorems. C3 of the always-on `test_soundness_certificate` fails closed if
    /// any future overlay edit reintroduces sorry taint here.
    ///
    /// Each `init_*` registrar is idempotent and order-independent. A registrar
    /// failure is a hard error (the env is malformed), surfaced as an `Err`.
    #[cfg(any(test, feature = "math-overlays"))]
    pub fn soundness_certificate_env() -> Result<Environment, super::EnvError> {
        let mut env = Environment::new();

        // Foundational carriers used by the overlays.
        env.init_fin()?;
        env.init_lt()?;
        env.init_rat_ord()?;

        // ── Tier-0 TCB shrink: Nat bitwise primitives as real Definitions ──
        // Discharge the admitted `Nat.testBit`/`land`/`lor`/`xor`/`shiftRight`
        // domain axioms to genuine reducible `Declaration::Definition`s over
        // `Nat.div2` / `Nat.iterDiv2` BEFORE any overlay registers the bare-axiom
        // versions. The overlay registrars guard on `get_const(...).is_none()`, so
        // seeing the real Definition first makes them no-op rather than admit an
        // axiom (mirrors the native-prelude ordering in `mod.rs`). Each is a total
        // primitive-recursive fold whose ground evaluation agrees with the native
        // reducer; verified by the per-registrar def-unfold ground-rfl tests.
        env.register_nat_testbit_def()?; // Nat.testBit, Nat.iterDiv2
        env.register_nat_bitwise_def()?; // Nat.land, Nat.lor, Nat.xor
        env.register_nat_shiftright_def()?; // Nat.shiftRight

        // ── seed_overlays (C006 / interval-arith / IBP-width-zero) ──
        env.init_nn_verify_blockwise_crown_ext()?;
        env.init_nn_verify_interval_arith_proofs()?;
        env.init_nn_verify_interval_containment_proofs()?;
        env.init_nn_verify_rat_interval_proofs()?;
        // `init_nn_verify_ibp_width_zero` transitively pulls in
        // `init_nn_verify_ibp_tightness` → `init_nn_verify_ibp_linear`, which
        // register the (now sorry-free) IBP linear/tightness corpus. Seeding it
        // here is what makes the certificate cover the FULL shipped env.
        env.init_nn_verify_ibp_width_zero()?;
        env.init_nn_verify_rat_ordering()?;
        // Extra always-on coverage surfaces (Fin-sum + Fourier-Boolean) — not in
        // the native seed but sorry-free, exercising the Fin junk carrier.
        env.init_fin_sum()?;
        env.init_fourier_boolean()?;

        // ── Tier-A Rat batch 1 ──
        env.init_nn_verify_tier_a_rat_min_zero()?;
        env.init_nn_verify_tier_a_rat_le_refl_zero()?;
        env.init_nn_verify_tier_a_rat_zero_eq_max()?;
        env.init_nn_verify_tier_a_rat_zero_eq_min()?;
        env.init_nn_verify_tier_a_rat_max_eq_min()?;

        // ── Tier-A Rat batch 2 ──
        env.init_nn_verify_tier_a_rat_min_eq_max()?;
        env.init_nn_verify_tier_a_rat_max_zero_zero_alt()?;
        env.init_nn_verify_tier_a_rat_min_zero_zero_alt()?;
        env.init_nn_verify_tier_a_rat_le_refl_max_zero_zero()?;
        env.init_nn_verify_tier_a_rat_le_refl_min_zero_zero()?;

        // ── Tier-A Rat batch 3 ──
        env.init_nn_verify_tier_a_rat_mul_zero_zero()?;
        env.init_nn_verify_tier_a_rat_mul_one_zero()?;
        env.init_nn_verify_tier_a_rat_mul_zero_one()?;
        env.init_nn_verify_tier_a_rat_add_neg_self_zero()?;
        env.init_nn_verify_tier_a_rat_add_left_neg_zero()?;
        env.init_nn_verify_tier_a_rat_mul_neg_zero_zero()?;
        env.init_nn_verify_tier_a_rat_neg_zero_zero()?;

        // ── tier-A Nat + top-level Nat ordering ──
        env.init_nn_verify_tier_a_nat_ordering()?;
        env.init_nat_top_level_ordering()?;

        // ── Tier-A Rat batch 4 ──
        env.init_nn_verify_tier_a_rat_min_le_max_zero_zero()?;
        env.init_nn_verify_tier_a_rat_max_le_min_zero_zero()?;
        env.init_nn_verify_tier_a_rat_min_min_zero_zero()?;
        env.init_nn_verify_tier_a_rat_max_max_zero_zero()?;
        env.init_nn_verify_tier_a_rat_max_min_zero_zero()?;

        // ── canonical general Rat.min_le_max ──
        env.init_rat_min_le_max()?;

        Ok(env)
    }

    /// Run the five mechanical claims over the FULL environment and emit THE
    /// Soundness Certificate. See the module docs / design doc.
    #[cfg(any(test, feature = "math-overlays"))]
    #[must_use]
    pub fn soundness_certificate(&self) -> SoundnessCertificate {
        let c1 = self.certify_c1_reverification();
        let c2 = self.certify_c2_tcb();
        let c3 = self.certify_c3_trust_markers();
        let c4 = self.certify_c4_refutation();
        let c4_opacity = self.certify_c4_opacity();
        let c5 = certify_c5_exploit_resistance();
        let trusted_base = build_trusted_base(&c2);
        SoundnessCertificate {
            c1,
            c2,
            c3,
            c4,
            c4_opacity,
            c5,
            trusted_base,
        }
    }

    /// C1 — re-type-check every `Theorem`/`Definition` carrying a value:
    /// `check_type(value, type_)` (i.e. `infer_type(value)` is `def_eq` to the
    /// declared `type_`). This re-derives trust for every proof INDEPENDENT of
    /// how it was registered — even a hypothetical `add_decl_unchecked` bypass of
    /// a VALUE-BEARING decl would be caught here.
    ///
    /// G2 SYMMETRY: `Axiom`-kind (and other value-less) decls carry no proof for
    /// C1 to re-derive, but this now ALSO runs `infer_sort` on every such decl's
    /// declared TYPE (well-formedness: no leaked fvar/mvar, sort inhabited,
    /// level-scope closed). That closes the "axiom-shaped smuggle" hole — a
    /// bypassed `Axiom{ type_: <ill-formed> }` is caught here — making C1
    /// symmetric across kinds. It does NOT refute an axiom's TRUTH (a well-formed
    /// `bad : False` still sorts to `Prop`); that is C2's golden-pin + C4/C4''s
    /// job. See Pillar-1 gap G2.
    #[cfg(any(test, feature = "math-overlays"))]
    fn certify_c1_reverification(&self) -> C1Reverification {
        let start = std::time::Instant::now();

        let mut out = C1Reverification::default();
        for c in self.constants() {
            // G2 SYMMETRY: value-less decls (chiefly `Axiom`-kind) carry no proof
            // for C1 to re-derive, but their declared TYPE is still checkable for
            // well-formedness. Before this, C1 `continue`d past every Axiom, so an
            // `add_decl_unchecked(Axiom{ type_: <ill-formed> })` bypass — a leaked
            // fvar/mvar or out-of-scope `Level::Param` in the type — slipped the
            // backstop entirely (it was only C2-golden-pinned + C4/C5-refuted). We
            // now run `infer_sort` on every Axiom's type through a fresh checker.
            // This does NOT (cannot) refute the axiom's TRUTH — a well-formed
            // `bad : False` still `infer_sort`s to `Prop`; that is what C2's
            // golden-pin governs — but it closes the WELL-FORMEDNESS precondition
            // symmetrically across kinds. SOUNDNESS: this only ADDS a check; it can
            // reject an ill-formed smuggle, never accept anything C1 rejected before.
            if !matches!(c.kind, ConstantKind::Theorem | ConstantKind::Definition) {
                if c.value.is_none() {
                    out.axiom_types_checked += 1;
                    let mut tc = TypeChecker::with_mode(self, self.mode());
                    tc.set_heartbeat_limit(0);
                    match tc.infer_sort(&c.type_) {
                        Ok(_) => out.axiom_types_passed += 1,
                        Err(_) => {
                            out.axiom_types_failed += 1;
                            out.axiom_type_failures.push(c.name.to_string());
                        }
                    }
                }
                continue;
            }
            let Some(value) = c.value.as_ref() else {
                continue;
            };
            out.checked += 1;
            // INDEPENDENCE + DETERMINISM: re-verify each decl through a FRESH
            // TypeChecker. Reusing one checker across all ~900 decls accumulates
            // per-instance state (the equiv_manager / fvar bookkeeping) whose
            // outcome can depend on the order decls are visited — and
            // `env.constants()` iterates a `HashMap`, so that order is randomized
            // per process. The result was a non-deterministic C1 false negative:
            // exactly one decl failing, a DIFFERENT one each run (`Rat.abs_mul`,
            // `Int.add_sub_add_right`, …). A per-decl checker makes each
            // re-verification independent — the canonical, order-free audit.
            // Each is re-verified with the heartbeat budget DISABLED (limit 0):
            // the 2M-tick runtime guardrail is not a soundness gate, and every
            // cert-env decl is known-terminating (it type-checked at registration).
            let mut tc = TypeChecker::with_mode(self, self.mode());
            tc.set_heartbeat_limit(0);
            match tc.check_type(value, &c.type_) {
                Ok(()) => out.passed += 1,
                Err(_) => {
                    out.failed += 1;
                    out.failures.push(c.name.to_string());
                }
            }
        }
        out.failures.sort();
        out.axiom_type_failures.sort();
        out.runtime_ms = elapsed_ms(start);
        out
    }

    /// C2 — enumerate the FULL axiom base, partition it, and pin it against the
    /// checked-in golden so adding an axiom is a reviewed, diff-visible event.
    #[cfg(any(test, feature = "math-overlays"))]
    fn certify_c2_tcb(&self) -> C2TcbEnumeration {
        let p = partition_axioms(self);

        // The golden pins the TRUSTED axiom set (trust markers excluded — they
        // are governed by C3, not part of the trusted base).
        let live: BTreeSet<String> = p.trusted.iter().cloned().collect();
        let golden: BTreeSet<String> = serde_json::from_str::<GoldenTcb>(GOLDEN_TCB_JSON)
            .map(|g| g.axioms.into_iter().collect())
            .unwrap_or_default();

        let added_vs_golden: Vec<String> = live.difference(&golden).cloned().collect();
        let removed_vs_golden: Vec<String> = golden.difference(&live).cloned().collect();
        let matches_golden =
            !golden.is_empty() && added_vs_golden.is_empty() && removed_vs_golden.is_empty();

        C2TcbEnumeration {
            all_axioms: p.all,
            trusted_axioms: p.trusted,
            foundational: p.foundational,
            admitted_domain: p.admitted_domain,
            other_admitted: p.other,
            trust_markers: p.trust,
            builtin_quot_primitives: p.builtin_quot,
            matches_golden,
            added_vs_golden,
            removed_vs_golden,
        }
    }

    /// C3 — for every declaration assert its transitive `axiom_deps` closure
    /// contains no trust marker (the BFS short-circuits on trust markers, which
    /// is why a reachable `sorry` lands in the deps set).
    #[cfg(any(test, feature = "math-overlays"))]
    fn certify_c3_trust_markers(&self) -> C3TrustMarkers {
        let mut out = C3TrustMarkers::default();
        for c in self.constants() {
            out.declarations_scanned += 1;
            let Some(deps) = self.trust_marker_deps(&c.name) else {
                continue;
            };
            if deps.is_empty() {
                continue;
            }
            out.reaching_trust_marker += 1;
            let mut markers: Vec<&Name> = deps.iter().collect();
            markers.sort_by_key(|n| n.to_string());
            for m in markers {
                out.violations.push(format!("{} -> {}", c.name, m));
            }
        }
        out.violations.sort();
        out
    }

    /// C4 — run the carrier-generic refutation engine over every admitted axiom.
    #[cfg(any(test, feature = "math-overlays"))]
    fn certify_c4_refutation(&self) -> C4Refutation {
        let scan = scan_admitted_axioms(self);
        C4Refutation {
            admitted_scanned: scan.admitted_scanned,
            refutable: scan.refutable,
            examined: scan.examined,
            opaque_unexamined: scan.opaque_unexamined,
            carriers: scan.carriers,
        }
    }

    /// C4' — run the opacity-transparency refutation pass: for every
    /// `Opaque`-with-body carrier, make it transparent and re-run C4 over the
    /// axioms that mention it, asserting none becomes refutable.
    #[cfg(any(test, feature = "math-overlays"))]
    fn certify_c4_opacity(&self) -> C4Opacity {
        let scan = scan_opacity_masked_axioms(self);
        C4Opacity {
            checked: scan.checked,
            refutable: scan.refutable,
            masked: scan.masked,
        }
    }
}

/// C5 — assert the kernel REJECTS the deep-nested `False`-proof corpus. Mirrors
/// `tc::tests2::soundness_nested_arg`: each attack constructs a minimal env and
/// an ill-typed proof of `False`; the kernel MUST reject it.
#[cfg(any(test, feature = "math-overlays"))]
fn certify_c5_exploit_resistance() -> C5ExploitResistance {
    use super::Declaration;
    use crate::expr::{BinderInfo, Expr};

    let mut out = C5ExploitResistance::default();

    // Build the shared True/False/myid/gff env. `myid : (A:Prop)->A->A`,
    // `gff : False -> False`.
    fn base_env() -> Environment {
        let mut env = Environment::new();
        env.init_true_false()
            .expect("invariant: True/False initialize");
        let prop = Expr::prop();
        let myid_ty = Expr::pi(
            BinderInfo::Implicit,
            prop.clone(),
            Expr::pi(BinderInfo::Default, Expr::bvar(0), Expr::bvar(1)),
        );
        let myid_val = Expr::lam(
            BinderInfo::Implicit,
            prop,
            Expr::lam(BinderInfo::Default, Expr::bvar(0), Expr::bvar(0)),
        );
        env.add_decl(Declaration::Definition {
            name: Name::from_string("myid"),
            level_params: vec![],
            type_: myid_ty,
            value: myid_val,
            is_reducible: true,
        })
        .expect("myid is well-typed");
        let false_const = Expr::const_(Name::from_string("False"), vec![]);
        env.add_decl(Declaration::Definition {
            name: Name::from_string("gff"),
            level_params: vec![],
            type_: Expr::arrow(false_const.clone(), false_const.clone()),
            value: Expr::lam(BinderInfo::Default, false_const, Expr::bvar(0)),
            is_reducible: true,
        })
        .expect("gff is well-typed");
        env
    }

    fn false_const() -> Expr {
        Expr::const_(Name::from_string("False"), vec![])
    }
    fn true_intro() -> Expr {
        Expr::const_(Name::from_string("True.intro"), vec![])
    }
    /// `myid False True.intro` — infers to `False` but is internally ill-typed.
    fn bad_inner_app() -> Expr {
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("myid"), vec![]),
                false_const(),
            ),
            true_intro(),
        )
    }

    // `add_decl`-registration form: a proof-of-`False` registered as a theorem;
    // the kernel MUST reject it. Returns `true` iff rejected.
    fn reject_via_add_decl(name: &str, mut env: Environment, proof: Expr) -> bool {
        env.add_decl(Declaration::Theorem {
            name: Name::from_string(name),
            level_params: vec![],
            type_: false_const(),
            value: proof,
        })
        .is_err()
    }

    // Direct `check_type` form: checking `term : False`; MUST be rejected.
    fn reject_via_check_type(env: &Environment, term: &Expr) -> bool {
        let tc = TypeChecker::new(env);
        tc.check_type(term, &false_const()).is_err()
    }

    let gff = || Expr::const_(Name::from_string("gff"), vec![]);
    let let_false = |val: Expr| {
        let body = Expr::app(gff(), Expr::bvar(0));
        Expr::let_named(Name::from_string("v"), false_const(), val, body, false)
    };

    // (name, was-rejected) for every attack in the deep-nested False corpus.
    let results: Vec<(&str, bool)> = vec![
        // (a) NESTED-APP False (add_decl form): `gff (myid False True.intro)`.
        (
            "exploit_nested_app",
            reject_via_add_decl(
                "exploit_nested_app",
                base_env(),
                Expr::app(gff(), bad_inner_app()),
            ),
        ),
        // (a') NESTED-APP False (direct check_type form).
        (
            "exploit_nested_app_check_type",
            reject_via_check_type(&base_env(), &bad_inner_app()),
        ),
        // (b) LET False: `let v : False := myid False True.intro; gff v`.
        (
            "exploit_let_false",
            reject_via_add_decl("exploit_let_false", base_env(), let_false(bad_inner_app())),
        ),
        // (b') LET False (direct check_type form).
        (
            "exploit_let_false_check_type",
            reject_via_check_type(&base_env(), &let_false(bad_inner_app())),
        ),
        // (c) Direct ill-typed argument: `gff True.intro`.
        (
            "exploit_gff_true_intro",
            reject_via_add_decl(
                "exploit_gff_true_intro",
                base_env(),
                Expr::app(gff(), true_intro()),
            ),
        ),
        // (d) Doubly-nested App False: `gff (gff (myid False True.intro))`.
        (
            "exploit_double_nested_app",
            reject_via_add_decl(
                "exploit_double_nested_app",
                base_env(),
                Expr::app(gff(), Expr::app(gff(), bad_inner_app())),
            ),
        ),
        // (e) `gff (myid True True.intro)` — inner term has type `True`, not `False`.
        (
            "exploit_myid_true",
            reject_via_add_decl("exploit_myid_true", base_env(), {
                let myid_true = Expr::app(
                    Expr::app(
                        Expr::const_(Name::from_string("myid"), vec![]),
                        Expr::const_(Name::from_string("True"), vec![]),
                    ),
                    true_intro(),
                );
                Expr::app(gff(), myid_true)
            }),
        ),
        // (f) Let-bound True.intro annotated as False, then consumed.
        (
            "exploit_let_true_intro_as_false",
            reject_via_add_decl(
                "exploit_let_true_intro_as_false",
                base_env(),
                let_false(true_intro()),
            ),
        ),
        // (g) Bare `True.intro : False` — the simplest masquerade.
        (
            "exploit_bare_true_intro",
            reject_via_add_decl("exploit_bare_true_intro", base_env(), true_intro()),
        ),
        // (h) A lambda of type `False -> True` is NOT a proof of `False`.
        (
            "exploit_lambda_false_to_true",
            reject_via_check_type(
                &base_env(),
                &Expr::lam(BinderInfo::Default, false_const(), true_intro()),
            ),
        ),
    ];

    for (name, rejected) in results {
        out.attacks += 1;
        if rejected {
            out.rejected += 1;
        } else {
            out.accepted.push(name.to_owned());
        }
    }
    out.accepted.sort();
    out
}

/// Build the printed Trusted Base from the C2 enumeration.
fn build_trusted_base(c2: &C2TcbEnumeration) -> TrustedBase {
    let mut admitted = c2.admitted_domain.clone();
    admitted.extend(c2.other_admitted.iter().cloned());
    admitted.sort();
    let total = c2.foundational.len() + admitted.len();
    TrustedBase {
        kernel: format!("{KERNEL_CRATE} @{KERNEL_VERSION}"),
        forbid_unsafe: true,
        foundational_axioms: c2.foundational.clone(),
        admitted_axioms: admitted,
        total_trusted_axioms: total,
    }
}

#[allow(clippy::cast_possible_truncation)]
fn elapsed_ms(start: std::time::Instant) -> u64 {
    start.elapsed().as_millis().min(u128::from(u64::MAX)) as u64
}

// ════════════════════════════ Display (§2) ════════════════════════════

fn check(ok: bool) -> &'static str {
    if ok {
        "\u{2713}"
    } else {
        "\u{2717}"
    }
}

impl fmt::Display for SoundnessCertificate {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(
            f,
            "CLEAN SOUNDNESS CERTIFICATE  (kernel rev {KERNEL_CRATE} @{KERNEL_VERSION})"
        )?;
        writeln!(
            f,
            "  C1 re-verified        : {} / {} declarations type-check  {}  ({} ms)",
            self.c1.passed,
            self.c1.checked,
            check(self.c1.ok()),
            self.c1.runtime_ms,
        )?;
        let rogue = self.c2.added_vs_golden.len();
        writeln!(
            f,
            "  C2 axiom closure      : {rogue} rogue axioms (all {} axioms enumerated; golden {})  {}",
            self.c2.all_axioms.len(),
            if self.c2.matches_golden { "MATCH" } else { "DIVERGED" },
            check(self.c2.ok()),
        )?;
        writeln!(
            f,
            "  C3 trust markers      : {} sorry/sorryAx reachable  {}",
            self.c3.reaching_trust_marker,
            check(self.c3.ok()),
        )?;
        let cov = self.c4.coverage();
        writeln!(
            f,
            "  C4 refutation         : {} / {} refutable among {} concrete-carrier-examined axioms  {}",
            cov.refutable,
            cov.examined,
            cov.examined,
            check(self.c4.ok()),
        )?;
        writeln!(
            f,
            "                          {} axioms are OPAQUE to refutation — TRUSTED, NOT CHECKED",
            cov.opaque_unexamined,
        )?;
        writeln!(
            f,
            "  C4' opacity-transp.   : {} / {} opaque-with-body carriers mask a refutable axiom  {}",
            self.c4_opacity.masked.len(),
            self.c4_opacity.checked,
            check(self.c4_opacity.ok()),
        )?;
        writeln!(
            f,
            "  C5 exploit resistance : {} / {} False-proof attacks rejected  {}",
            self.c5.rejected,
            self.c5.attacks,
            check(self.c5.ok()),
        )?;
        writeln!(f, "  --- TRUSTED BASE (everything else is proven) ---")?;
        writeln!(
            f,
            "  \u{2022} kernel checker: {} @{}, #![forbid(unsafe_code)]",
            KERNEL_CRATE, KERNEL_VERSION,
        )?;
        writeln!(
            f,
            "  \u{2022} foundational axioms ({}): {}",
            self.trusted_base.foundational_axioms.len(),
            join_capped(&self.trusted_base.foundational_axioms, 12),
        )?;
        writeln!(
            f,
            "  \u{2022} builtin quotient primitives ({}, part of the kernel checker — NOT axioms): {}",
            self.c2.builtin_quot_primitives.len(),
            join_capped(&self.c2.builtin_quot_primitives, 12),
        )?;
        // Split the admitted axioms into the two HONEST buckets the reviewer
        // demanded: those C4 actually refutation-checked (concrete carrier,
        // counterexample-free) vs. those taken on FAITH (abstract carrier, C4
        // could not examine them — e.g. the deep BoolAnalysis analytic axioms).
        let examined_set: BTreeSet<&str> = self.c4.examined.iter().map(String::as_str).collect();
        let refutable_set: BTreeSet<&str> = self.c4.refutable.iter().map(String::as_str).collect();
        let concrete: Vec<&String> = self
            .trusted_base
            .admitted_axioms
            .iter()
            .filter(|a| examined_set.contains(a.as_str()) && !refutable_set.contains(a.as_str()))
            .collect();
        let abstract_: Vec<&String> = self
            .trusted_base
            .admitted_axioms
            .iter()
            .filter(|a| !examined_set.contains(a.as_str()))
            .collect();
        writeln!(
            f,
            "  \u{2022} admitted, concrete-carrier (refutation-checked counterexample-free): {}",
            concrete.len(),
        )?;
        for ax in &concrete {
            writeln!(f, "      - {ax}")?;
        }
        writeln!(
            f,
            "  \u{2022} admitted, abstract-carrier (taken on FAITH — e.g. deep BoolAnalysis: parseval/kkl/friedgut/bonami_beckner): {}",
            abstract_.len(),
        )?;
        for ax in &abstract_ {
            writeln!(f, "      - {ax}")?;
        }
        writeln!(
            f,
            "  \u{2022} concrete carriers: {} censused, {} junk-admitting (no examined admitted axiom refutable through them)",
            self.c4.carriers.len(),
            self.c4.junk_carriers(),
        )?;
        let verdict = if self.is_sound() {
            "SOUND relative to the trusted base above."
        } else {
            "NOT SOUND — see failed claim(s) above."
        };
        write!(f, "  VERDICT: {verdict}")
    }
}

// Helper: join a slice, capping at `n` entries with an ellipsis tail.
fn join_capped(items: &[String], n: usize) -> String {
    if items.len() <= n {
        items.join(", ")
    } else {
        format!("{}, … (+{} more)", items[..n].join(", "), items.len() - n)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Regression guard for the soundness-certificate capstone disposition of
    /// the formerly `sorryAx`-backed IBP scaffolding. Pins, over the FULL
    /// certificate env, that:
    ///   - `w_pos_nonneg` / `w_neg_nonpos` / `w_decompose` are PROVEN (genuine
    ///     sorry-free theorems, closure ⊆ the admitted Rat lattice axioms),
    ///   - `ibp_linear_per_component` (T80 unlock) and
    ///     `ibp_tightness_{base,step}` (R-weak unlock) are now PROVEN sorry-free
    ///     `Declaration::Theorem`s off the faithful bound Definitions — no
    ///     NNVerify IBP-scaffolding admitted `Declaration::Axiom` remains,
    ///   - the downstream `ibp_linear_sound` / `ibp_tightness_bound[_inductive]`
    ///     theorems are sorry-free.
    ///
    /// If a future edit reintroduces a `sorryAx` body for any of these, this
    /// test fails closed alongside C3 of `test_soundness_certificate`.
    #[test]
    fn ibp_scaffolding_is_sorry_free() {
        use super::super::axiom_audit::ProofQuality;
        let env = Environment::soundness_certificate_env().expect("build certificate env");
        let tc = TypeChecker::with_mode(&env, env.mode());

        // PROVEN theorems: present, sorry-free, real proof value.
        for n in ["NNVerify.w_pos_nonneg", "NNVerify.w_neg_nonpos"] {
            let q = env.proof_quality(&Name::from_string(n));
            assert!(
                matches!(
                    q,
                    Some(ProofQuality::Constructive | ProofQuality::AxiomDependent { .. })
                ),
                "{n} must be a genuine (non-Unchecked) theorem, got {q:?}"
            );
            let tm = env
                .trust_marker_deps(&Name::from_string(n))
                .expect("present");
            assert!(tm.is_empty(), "{n} must be sorry-free, got {tm:?}");
        }

        // PROVEN: `w_decompose` is now a genuine sorry-free `Declaration::Theorem`
        // (the max/min decomposition identity, proved by a `Bool.rec` split on
        // `Rat.ble Rat.zero (W i j)` discharged with `Rat.zero_add`/`Rat.add_zero`).
        {
            let n = "NNVerify.w_decompose";
            let info = env.get_const(&Name::from_string(n)).expect("present");
            assert_eq!(
                info.kind,
                ConstantKind::Theorem,
                "{n} must now be a Theorem"
            );
            let tm = env
                .trust_marker_deps(&Name::from_string(n))
                .expect("present");
            assert!(tm.is_empty(), "{n} must be sorry-free, got {tm:?}");
        }

        // PROVEN: `ibp_linear_per_component` graduated to a constructive
        // `Declaration::Theorem` (T80 unlock, #3490 follow-up) once the
        // `ibp_linear_bounds` define made its projected conclusion reduce.
        {
            let n = "NNVerify.ibp_linear_per_component";
            let info = env.get_const(&Name::from_string(n)).expect("present");
            assert_eq!(
                info.kind,
                ConstantKind::Theorem,
                "{n} must now be a Theorem"
            );
            let tm = env
                .trust_marker_deps(&Name::from_string(n))
                .expect("present");
            assert!(tm.is_empty(), "{n} must be sorry-free, got {tm:?}");
        }

        // PROVEN: `ibp_tightness_step` graduated to a constructive
        // `Declaration::Theorem` (C008 unlock, R-weak) — the propagated eps-ball
        // stays zero-width through every layer (`ibp_propagate_eq`), so the step
        // LHS collapses to `Rat.zero` via `ibp_width_zero` and the RHS is
        // non-negative (`norm_product_nonneg` / `infinity_norm_nonneg`). Same
        // R-weak honesty caveat as `ibp_tightness_base` (the zero-width collapse
        // leans on the registered `eps_ball` placeholder body); still a genuine
        // sorry-free assembly. `tc` is retained for downstream carrier checks.
        let _ = &tc;
        {
            let n = "NNVerify.ibp_tightness_step";
            let info = env.get_const(&Name::from_string(n)).expect("present");
            assert_eq!(
                info.kind,
                ConstantKind::Theorem,
                "{n} must now be a Theorem"
            );
            let tm = env
                .trust_marker_deps(&Name::from_string(n))
                .expect("present");
            assert!(tm.is_empty(), "{n} must be sorry-free, got {tm:?}");
        }

        // PROVEN: the C008 base case is now a genuine sorry-free
        // `Declaration::Theorem` (#3490 T6 — `eps_ball_width_is_zero` collapses
        // the LHS to 0; `Rat.mul_nonneg` closes `0 ≤ 2·eps·1`).
        {
            let n = "NNVerify.ibp_tightness_base";
            let info = env.get_const(&Name::from_string(n)).expect("present");
            assert_eq!(
                info.kind,
                ConstantKind::Theorem,
                "{n} must now be a Theorem"
            );
            let tm = env
                .trust_marker_deps(&Name::from_string(n))
                .expect("present");
            assert!(tm.is_empty(), "{n} must be sorry-free, got {tm:?}");
        }

        // Downstream theorems composing the above are sorry-free.
        for n in [
            "NNVerify.ibp_linear_sound",
            "NNVerify.ibp_tightness_bound",
            "NNVerify.ibp_tightness_bound_inductive",
        ] {
            let tm = env
                .trust_marker_deps(&Name::from_string(n))
                .expect("present");
            assert!(tm.is_empty(), "{n} must be sorry-free, got {tm:?}");
        }
    }

    /// Regenerate `data/soundness_tcb.json` from the live axiom set when the
    /// env var `REGEN_SOUNDNESS_GOLDEN` is set. A reviewed, deliberate operation
    /// (run after a vetted axiom-base change), it is a no-op in normal test runs.
    ///
    /// REVIEWED-EVENT WORKFLOW. The golden `data/soundness_tcb.json` pins the
    /// Trusted Base; changing it is a change to what Clean trusts, not an
    /// incidental edit. Adding/removing/renaming a trusted axiom turns
    /// `golden_matches_live_axioms` and the local/release soundness gate RED —
    /// the intended diff-visible signal. To re-bless the new TCB:
    ///   1. make the vetted axiom-base change (with its SOUNDNESS justification);
    ///   2. run `REGEN_SOUNDNESS_GOLDEN=1 cargo test -p clean-kernel --lib \
    ///      --features math-overlays regen_golden_tcb_when_requested`;
    ///   3. REVIEW the diff to `data/soundness_tcb.json` in the PR (the added /
    ///      removed axiom names are the point). Never hand-edit the golden.
    ///
    /// See `docs/SOUNDNESS_CERTIFICATE.md` § "Regenerating the golden".
    #[test]
    fn regen_golden_tcb_when_requested() {
        if std::env::var_os("REGEN_SOUNDNESS_GOLDEN").is_none() {
            return;
        }
        let env = Environment::soundness_certificate_env().expect("build certificate env");
        let golden = SoundnessCertificate::golden_from_env(&env);
        // Crate root is `crates/clean-kernel`; the golden lives at the workspace
        // root `data/soundness_tcb.json` (three levels up).
        let path =
            std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../data/soundness_tcb.json");
        std::fs::write(&path, golden).expect("write golden TCB");
        eprintln!("regenerated golden TCB at {}", path.display());
    }

    /// The always-on soundness keystone: the full overlay env's certificate is
    /// GREEN. This is the proof that everything is sound.
    ///
    /// Runs on an explicit 512MB stack: C1 re-verifies every declaration
    /// through the kernel, and the faithful `ibp_linear_bounds` Definition
    /// (W+/W- interval body, 2026-06-11) plus the R-weak `ibp_tightness_step`
    /// proof (nested `Nat.rec` `ibp_propagate_eq` over the `ibp_propagate` fold,
    /// 2026-06-11) deepened the longest def-eq chain. 256MB was intermittently
    /// insufficient (a flaky stack overflow surfaced as a spurious `Rat.ble`
    /// C1 re-verification failure ~1-in-4 runs); 512MB clears it deterministically.
    #[test]
    fn test_soundness_certificate() {
        crate::test_utils::run_with_stack(512 * 1024 * 1024, test_soundness_certificate_inner);
    }

    fn test_soundness_certificate_inner() {
        let env = Environment::soundness_certificate_env().expect("build certificate env");
        let cert = env.soundness_certificate();

        // Print the certificate so a failing run shows exactly which claim broke.
        eprintln!("{cert}");

        assert!(
            cert.c1.ok(),
            "C1 FAILED: {} / {} re-verified, failures: {:?}",
            cert.c1.passed,
            cert.c1.checked,
            cert.c1.failures
        );
        assert!(
            cert.c2.ok(),
            "C2 FAILED: trust_markers={:?}, matches_golden={}, added={:?}, removed={:?}",
            cert.c2.trust_markers,
            cert.c2.matches_golden,
            cert.c2.added_vs_golden,
            cert.c2.removed_vs_golden
        );
        assert!(
            cert.c3.ok(),
            "C3 FAILED: {} declarations reach a trust marker: {:?}",
            cert.c3.reaching_trust_marker,
            cert.c3.violations
        );
        assert!(
            cert.c4.ok(),
            "C4 FAILED: refutable admitted axioms: {:?}",
            cert.c4.refutable
        );
        assert!(
            cert.c4_opacity.ok(),
            "C4' FAILED: {} opaque-with-body carriers mask a refutable axiom: {:?}",
            cert.c4_opacity.masked.len(),
            cert.c4_opacity.masked
        );
        // The C4' pass must actually EXAMINE the opaque-with-body risk set (it is
        // not vacuously green): the certificate env carries opaque carriers
        // (`Nat.add`, the NNVerify cert/zonotope placeholders, …). A zero here
        // would mean the pass is a no-op.
        assert!(
            cert.c4_opacity.checked > 0,
            "C4' must examine at least one opaque-with-body carrier (got {})",
            cert.c4_opacity.checked
        );
        assert!(
            cert.c5.ok(),
            "C5 FAILED: {} / {} attacks rejected, accepted: {:?}",
            cert.c5.rejected,
            cert.c5.attacks,
            cert.c5.accepted
        );
        assert!(cert.is_sound(), "the soundness certificate must be GREEN");
    }

    /// C4' catches the `Rat.abs`-class opacity-masked unsoundness. We plant a
    /// deliberately-opaque IDENTITY carrier `Foo := fun a : Rat => a` plus an
    /// admitted axiom `bad : ∀ q : Rat, 0 ≤ Foo q` whose conclusion is FALSE
    /// once `Foo` unfolds (`0 ≤ q`, false for `q < 0`) but is INVISIBLE to C4
    /// while `Foo` stays opaque (`Foo q` is stuck, so the prop never reduces to a
    /// closed `Int.le`). The opacity-transparency pass MUST flag it as masked —
    /// proving the mechanical check catches the bug-class going forward.
    #[test]
    fn c4_opacity_catches_planted_opaque_masked_axiom() {
        use super::super::carrier_refutation::scan_opacity_masked_axioms;
        use super::super::Declaration;
        use crate::expr::{BinderInfo, Expr};

        // Sound Rat carriers (`Rat`, `Rat.le`, `Rat.mk`, `Rat.zero`, …) — the
        // same surface the C4 engine decides over.
        let mut env = Environment::new();
        env.init_nn_verify_interval_arith_proofs()
            .expect("init interval arith proofs");

        let rat = Expr::const_(Name::from_string("Rat"), vec![]);

        // C4 sees `bad` as NON-refutable while `Foo` is opaque. Sanity-check that
        // BEFORE planting anything the pass finds nothing masked.
        let before = scan_opacity_masked_axioms(&env);
        assert!(
            before.masked.is_empty(),
            "baseline env must have no opacity-masked axioms, got {:?}",
            before.masked
        );

        // Plant the opaque IDENTITY carrier `Foo : Rat → Rat := fun a => a`.
        env.add_decl(Declaration::Opaque {
            name: Name::from_string("Foo"),
            level_params: vec![],
            type_: Expr::arrow(rat.clone(), rat.clone()),
            value: Expr::lam(BinderInfo::Default, rat.clone(), Expr::bvar(0)),
        })
        .expect("Foo : Rat → Rat is well-typed");

        // Plant the admitted axiom `bad : ∀ q : Rat, Rat.le Rat.zero (Foo q)`.
        // It is well-typed (an axiom over a valid Prop), but FALSE once `Foo`
        // unfolds: `Rat.le 0 q` is false at `q = -1`.
        let rat_le = Expr::const_(Name::from_string("Rat.le"), vec![]);
        let rat_zero = Expr::apps(
            Expr::const_(Name::from_string("Rat.mk"), vec![]),
            [
                Expr::app(Expr::const_(Name::from_string("Int.ofNat"), vec![]), {
                    Expr::const_(Name::from_string("Nat.zero"), vec![])
                }),
                Expr::app(
                    Expr::const_(Name::from_string("Nat.succ"), vec![]),
                    Expr::const_(Name::from_string("Nat.zero"), vec![]),
                ),
            ],
        );
        let foo_q = Expr::app(
            Expr::const_(Name::from_string("Foo"), vec![]),
            Expr::bvar(0),
        );
        let bad_body = Expr::apps(rat_le, [rat_zero, foo_q]);
        let bad_ty = Expr::pi(BinderInfo::Default, rat, bad_body);
        env.add_decl(Declaration::Axiom {
            name: Name::from_string("bad"),
            level_params: vec![],
            type_: bad_ty,
        })
        .expect("bad axiom over a valid Prop type-checks");

        // The opacity-transparency pass MUST flag `bad` as masked by `Foo`.
        let after = scan_opacity_masked_axioms(&env);
        assert!(
            after.checked >= 1,
            "the planted opaque `Foo` must be in the examined risk set"
        );
        assert!(
            after
                .masked
                .iter()
                .any(|m| m.axiom == "bad" && m.carrier == "Foo"),
            "C4' must flag `bad` as masked by opaque `Foo`; masked={:?}",
            after.masked
        );
        assert!(
            after.refutable >= 1,
            "C4' refutable count must be ≥ 1 after planting the masked axiom"
        );
    }

    /// C1 catches a fabricated theorem: re-verification is independent of HOW the
    /// decl was registered. We register a well-typed theorem, then (via a
    /// structural bypass) a fabricated one, and assert C1 flags exactly the
    /// fabrication.
    #[test]
    fn c1_catches_fabricated_theorem() {
        use super::super::Declaration;
        use crate::expr::Expr;

        let mut env = Environment::new();
        env.init_true_false().expect("init true/false");

        // A genuine theorem `triv : True := True.intro`.
        env.add_decl(Declaration::Theorem {
            name: Name::from_string("triv"),
            level_params: vec![],
            type_: Expr::const_(Name::from_string("True"), vec![]),
            value: Expr::const_(Name::from_string("True.intro"), vec![]),
        })
        .expect("triv is well-typed");

        // A FABRICATED theorem `bogus : False := True.intro`, smuggled in via the
        // structural (non-kernel-checked) path. C1 must catch it.
        env.add_decl_structural(Declaration::Theorem {
            name: Name::from_string("bogus"),
            level_params: vec![],
            type_: Expr::const_(Name::from_string("False"), vec![]),
            value: Expr::const_(Name::from_string("True.intro"), vec![]),
        })
        .expect("structural add bypasses the kernel check");

        // G2 CASE (a): a WELL-FORMED false axiom `bad_axiom : False` as a
        // Declaration::Axiom, smuggled via the unchecked path. Its TYPE (`False`)
        // is well-formed (sorts to Prop), so the new C1 axiom-type check does NOT
        // and MUST NOT flag it — a false axiom's *truth* is refuted by C2's
        // golden-pin, not by C1. We assert it is NOT in the type-failures (it is
        // C2-pinned) to document the intended division of labour.
        env.add_decl_unchecked(Declaration::Axiom {
            name: Name::from_string("bad_axiom"),
            level_params: vec![],
            type_: Expr::const_(Name::from_string("False"), vec![]),
        });

        // G2 CASE (b): an ILL-FORMED axiom `smuggle : <leaked fvar>` — its declared
        // TYPE contains a free variable with no binder, which `add_decl` would
        // reject at `infer_sort` but the unchecked path admits. Post-G2, C1's
        // symmetric axiom-type check MUST catch this.
        use crate::expr::FVarId;
        env.add_decl_unchecked(Declaration::Axiom {
            name: Name::from_string("smuggle"),
            level_params: vec![],
            type_: Expr::fvar(FVarId::new(0xDEAD_BEEF)),
        });

        let c1 = env.certify_c1_reverification();
        assert!(
            c1.failures.contains(&"bogus".to_string()),
            "C1 must catch the fabricated `bogus : False`, failures: {:?}",
            c1.failures
        );
        assert!(
            !c1.failures.contains(&"triv".to_string()),
            "C1 must NOT flag the genuine `triv : True`"
        );
        // G2 (a): the well-formed false axiom is NOT a type-wellformedness failure
        // (its truth is C2's job, not C1's).
        assert!(
            !c1.axiom_type_failures.contains(&"bad_axiom".to_string()),
            "C1's axiom-type check must NOT flag the well-formed `bad_axiom : False` \
             (its FALSITY is refuted by C2's golden-pin, not by type well-formedness); \
             axiom_type_failures: {:?}",
            c1.axiom_type_failures
        );
        // G2 (b): the ill-formed axiom TYPE (leaked fvar) IS caught symmetrically.
        assert!(
            c1.axiom_type_failures.contains(&"smuggle".to_string()),
            "C1 (post-G2) must catch the ill-formed axiom type `smuggle : <leaked fvar>` \
             via its symmetric `infer_sort` check; axiom_type_failures: {:?}",
            c1.axiom_type_failures
        );
        // The whole certificate leg must be RED given the ill-formed smuggle.
        assert!(
            !c1.ok(),
            "C1 must be RED while an ill-formed axiom type is present"
        );
    }

    /// C5 must be 10/10: every exploit in the deep-nested False corpus rejected.
    #[test]
    fn c5_rejects_all_exploits() {
        let c5 = certify_c5_exploit_resistance();
        assert_eq!(
            c5.rejected, c5.attacks,
            "C5 must reject all {} exploits; accepted: {:?}",
            c5.attacks, c5.accepted
        );
        assert!(
            c5.attacks >= 10,
            "C5 must run at least 10 exploit attacks (got {})",
            c5.attacks
        );
    }

    /// The Display impl prints the §2 certificate shape and a SOUND verdict,
    /// INCLUDING the honest faith/checked split (the C4 examined-vs-opaque line
    /// and the abstract-carrier FAITH bucket in the trusted base).
    ///
    /// Runs on an explicit 512MB stack for the same reason as
    /// `test_soundness_certificate`: building the certificate re-verifies every
    /// declaration through the kernel (C1), and the deepest def-eq chains (now
    /// including the `funext` Quot.lift-ι + function-eta proof) overflow the
    /// 2MB default test stack — a stack overflow there surfaces as a spurious
    /// non-SOUND verdict, not a real soundness failure.
    #[test]
    fn display_prints_sound_verdict() {
        crate::test_utils::run_with_stack(512 * 1024 * 1024, display_prints_sound_verdict_inner);
    }

    fn display_prints_sound_verdict_inner() {
        let env = Environment::soundness_certificate_env().expect("build certificate env");
        let cert = env.soundness_certificate();
        let printed = format!("{cert}");
        assert!(printed.contains("CLEAN SOUNDNESS CERTIFICATE"));
        assert!(printed.contains("C1 re-verified"));
        assert!(printed.contains("C4 refutation"));
        assert!(printed.contains("C4' opacity-transp."));
        assert!(printed.contains("TRUSTED BASE"));
        // The honest split must be visible: C4 reports examined-vs-opaque and the
        // trusted base names the abstract-carrier (FAITH) bucket.
        assert!(
            printed.contains("concrete-carrier-examined"),
            "C4 line must report the examined coverage:\n{printed}"
        );
        assert!(
            printed.contains("OPAQUE to refutation — TRUSTED, NOT CHECKED"),
            "C4 line must report opaque-unexamined as trusted-not-checked:\n{printed}"
        );
        assert!(
            printed.contains("admitted, concrete-carrier (refutation-checked"),
            "trusted base must split out the refutation-checked bucket:\n{printed}"
        );
        assert!(
            printed.contains("admitted, abstract-carrier (taken on FAITH"),
            "trusted base must split out the abstract-carrier FAITH bucket:\n{printed}"
        );
        assert!(
            printed.contains("VERDICT: SOUND"),
            "certificate must print a SOUND verdict:\n{printed}"
        );
    }

    /// The honesty keystone. Pins the faith/checked split:
    ///   (1) over the canonical certificate env, the deep BoolAnalysis
    ///       analytic axioms (parseval / kkl / friedgut / bonami_beckner /
    ///       noise_stability_fourier / influence_fourier + helpers) are
    ///       classified OPAQUE — C4 cannot reduce their abstract-carrier
    ///       conclusions to a concrete decidable prop, so they are TRUSTED, NOT
    ///       CHECKED; the certificate no longer launders them as "checked safe";
    ///   (2) the EXAMINED path is genuinely reachable and not dead code: a planted
    ///       concrete-carrier admitted axiom (`∀ a : Rat, Rat.le a a`) over a copy
    ///       of the cert env classifies EXAMINED (refutation-checked).
    /// `is_sound()` is unaffected throughout (the refutable set stays empty).
    ///
    /// NOTE: in the *current* cert env EVERY admitted axiom is over an abstract
    /// carrier (matrices / vectors with symbolic dimensions / uninterpreted
    /// bound functions), so the genuine `examined` count is 0 — exactly the
    /// vacuity the reviewer flagged. That is the honest state of the world; the
    /// planted axiom in (2) proves the examined classification is live.
    #[test]
    fn c4_coverage_classifies_boolanalysis_opaque_concrete_examined() {
        use super::super::carrier_refutation::{classify_refutation, RefutationOutcome};
        use super::super::Declaration;
        use crate::expr::{BinderInfo, Expr};

        let env = Environment::soundness_certificate_env().expect("build certificate env");
        let cert = env.soundness_certificate();

        let examined: BTreeSet<&str> = cert.c4.examined.iter().map(String::as_str).collect();
        let opaque: BTreeSet<&str> = cert
            .c4
            .opaque_unexamined
            .iter()
            .map(String::as_str)
            .collect();

        // The two buckets partition the scanned set, are disjoint, and refutable
        // is contained in examined (a refuted axiom was examined).
        assert!(
            examined.is_disjoint(&opaque),
            "examined and opaque buckets must be disjoint"
        );
        assert_eq!(
            cert.c4.examined.len() + cert.c4.opaque_unexamined.len(),
            cert.c4.admitted_scanned,
            "examined + opaque_unexamined must equal admitted_scanned"
        );
        for r in &cert.c4.refutable {
            assert!(
                examined.contains(r.as_str()),
                "a refutable axiom must also be examined: {r}"
            );
        }

        // (1) The deep BoolAnalysis analytic axioms land in the OPAQUE/faith
        // bucket: their conclusions are stuck on abstract carriers (uninterpreted
        // Rat-valued Fourier averages / norms) with no closed-decidable form.
        // NOTE: `parseval_identity` / `parseval_identity_helper` are NO LONGER
        // in this list — they were RETIRED (RUNG 4): the helper is now a
        // reducible Definition carrying the genuine unnormalized Parseval
        // equation, and `parseval_identity` is a kernel-CHECKED constructive
        // Theorem (`subsetSum_parseval_core n (pm∘f)`). They are therefore no
        // longer admitted axioms and cannot be classified OPAQUE.
        // NOTE: `fourier_weight_parseval_helper` and `influence_fourier_helper`
        // are likewise NO LONGER in this list — they were TCB-shrunk to reducible
        // `Eq` Definitions carrying their genuine statement bodies (level-weight
        // decomposition `Σ_k W^k[f] = Σ_S f̂(S)²` and the spectral influence
        // formula `Inf_i[f] = Σ_{S∋i} f̂(S)²`).
        // NOTE: `fourier_weight_parseval` is ALSO no longer in this list — it was
        // RETIRED to a kernel-CHECKED constructive `Declaration::Theorem` (the
        // level/subset double sum is swapped via `Fin.sum_swap` and the level
        // index collapsed pointwise by `fourier_level_collapse`, premise `|S| ≤ n`
        // from `Fin.sumNat_le_card` + `indNat_le_one`; empty admitted-axiom
        // closure). The remaining theorem `influence_fourier` still asserts its
        // helper `Eq` as an admitted axiom and stays OPAQUE below.
        // NOTE: `noise_stability_fourier` / `noise_stability_fourier_helper` are
        // likewise NO LONGER in this list — they were RETIRED (noise campaign
        // rung 6): the helper is now a reducible `Eq` Definition carrying the
        // genuine un-normalized ρ-weighted spectral statement over the
        // `noiseDensityW` carrier (`Σ_x Σ_y pm(f x)pm(f y)·noiseDensityW
        // = Σ_S ρ^{|S|}·A(S)²`), and `noise_stability_fourier` is a
        // kernel-CHECKED constructive Theorem (`noise_spectral_core ρ n (pm∘f)`;
        // empty admitted-axiom closure). They are no longer admitted axioms and
        // cannot be classified OPAQUE.
        let deep_boolanalysis: [&str; 0] = [
            // NOTE: `BoolAnalysis.kkl_inequality` / `_helper` are NO LONGER in
            // this list — they were RETIRED (KKL finish): the helper is now a
            // reducible Definition carrying the genuine max-influence KKL
            // statement (`∀ k d, small-influence-regime → ∃ i, (k+1)·Var ≤
            // 2·n·Inf_i`), and `kkl_inequality` is a kernel-CHECKED constructive
            // Theorem (`kkl_exists_max_influence`, the conditional sharp-KKL pinch
            // fed through the general-`n` pigeonhole; empty admitted-axiom
            // closure). They are no longer admitted axioms and cannot be OPAQUE.
            //
            // NOTE: `BoolAnalysis.friedgut_boolean` / `_helper` are NO LONGER in
            // this list either — they were RETIRED (FRIEDGUT TCB 5→3 co-land): the
            // helper is now a reducible `Declaration::Definition` carrying the
            // CORRECTED-budget v3 L2-distance Friedgut body (O'Donnell §9.6,
            // explicit-witness form, junta budget `48·2^e`), and
            // `friedgut_boolean` is a kernel-CHECKED constructive `Theorem` whose
            // proof (`friedgut_boolean_proof`, assembling the four landed
            // case-lemmas) has an EMPTY admitted-axiom closure. They are no longer
            // admitted axioms and cannot be classified OPAQUE — so the canonical
            // foundational base is now EXACTLY the three Lean axioms
            // `{Classical.choice, Quot.sound, propext}` (TCB→3).
            //
            // NOTE: `BoolAnalysis.influence_fourier` was RETIRED — it is now a
            // kernel-CHECKED constructive `Declaration::Theorem` (the full
            // Fourier discrete-derivative assembly in
            // `boolean_analysis_influence_chain.rs`), no longer an admitted axiom,
            // so it is correctly absent from the OPAQUE list.
            // NOTE: `BoolAnalysis.bonami_beckner` / `_helper` / `_conditions` are
            // likewise NO LONGER in this list — they were RETIRED (bonami run 16):
            // `_conditions` is now a reducible Definition carrying the genuine
            // (2,4) regime `(p=2) ∧ (q=4) ∧ (3ρ²≤1)`, `_helper` a reducible
            // Definition carrying the genuine hc24_core operator bound at `pm∘f`
            // (`Σ pow4(noiseFn ρ n (pm∘f)) ≤ 8^n·sq(Σ sq…)`), and `bonami_beckner`
            // a kernel-CHECKED constructive Theorem (`hc24_core ρ n (pm∘f)` fed the
            // noise bound extracted from the conditions; empty admitted-axiom
            // closure). They are no longer admitted axioms and cannot be OPAQUE.
        ];
        for ax in deep_boolanalysis {
            assert!(
                opaque.contains(ax),
                "deep BoolAnalysis axiom `{ax}` must be OPAQUE (taken on faith), \
                 not laundered as examined. opaque={:?}",
                cert.c4.opaque_unexamined
            );
        }

        // (2) The EXAMINED classification is live, not dead code: a planted
        // concrete-carrier admitted axiom over a copy of the cert env classifies
        // EXAMINED. (`∀ a : Rat, Rat.le a a` reduces to a concrete `Int.le`.)
        let mut planted = Environment::soundness_certificate_env().expect("build cert env");
        let rat = Expr::const_(Name::from_string("Rat"), vec![]);
        let refl_ty = Expr::pi(
            BinderInfo::Default,
            rat.clone(),
            Expr::apps(
                Expr::const_(Name::from_string("Rat.le"), vec![]),
                [Expr::bvar(0), Expr::bvar(0)],
            ),
        );
        planted
            .add_decl(Declaration::Axiom {
                name: Name::from_string("planted_concrete_rat_le_refl"),
                level_params: vec![],
                type_: refl_ty.clone(),
            })
            .expect("planted concrete axiom type-checks");
        let tc = TypeChecker::with_mode(&planted, planted.mode());
        assert_eq!(
            classify_refutation(&tc, &refl_ty),
            RefutationOutcome::Examined,
            "a concrete-carrier `Rat.le a a` axiom must classify EXAMINED — the \
             examined path must not be dead"
        );
        let planted_cert = planted.soundness_certificate();
        assert!(
            planted_cert
                .c4
                .examined
                .iter()
                .any(|a| a == "planted_concrete_rat_le_refl"),
            "the planted concrete axiom must appear in C4's examined set"
        );
        // The planted env stays SOUND (the concrete axiom is non-refutable) — the
        // split never changes the verdict.
        assert!(
            planted_cert.c4.ok(),
            "planted concrete axiom is non-refutable"
        );
    }

    /// The certificate serializes to a well-formed JSON object exposing every
    /// claim and the trusted base.
    #[test]
    fn serializes_to_json() {
        let env = Environment::soundness_certificate_env().expect("build certificate env");
        let cert = env.soundness_certificate();
        let json = cert.to_json().expect("serialize certificate to JSON");
        let v: serde_json::Value = serde_json::from_str(&json).expect("parse certificate JSON");
        for key in ["c1", "c2", "c3", "c4", "c4_opacity", "c5", "trusted_base"] {
            assert!(v.get(key).is_some(), "certificate JSON missing key `{key}`");
        }
        assert_eq!(
            v["c4"]["refutable"].as_array().map(Vec::len),
            Some(0),
            "C4 refutable set must serialize as empty"
        );
        assert_eq!(
            v["c4_opacity"]["masked"].as_array().map(Vec::len),
            Some(0),
            "C4' masked set must serialize as empty"
        );
        assert_eq!(
            v["c5"]["rejected"], v["c5"]["attacks"],
            "C5 must serialize rejected == attacks"
        );
    }

    /// The golden TCB embedded in the binary matches the live axiom set of the
    /// canonical env. This is the DURABILITY guarantee: any TCB change — adding,
    /// removing, or renaming a trusted axiom — makes the live set diverge from
    /// the checked-in golden and FAILS this test and the local/release
    /// soundness gate, so growing the Trusted Base cannot happen silently. If it fails,
    /// regenerate `data/soundness_tcb.json` via `golden_from_env` and review the
    /// diff — a reviewed event (see `regen_golden_tcb_when_requested` and
    /// `docs/SOUNDNESS_CERTIFICATE.md`).
    #[test]
    fn golden_matches_live_axioms() {
        let env = Environment::soundness_certificate_env().expect("build certificate env");
        let c2 = env.certify_c2_tcb();
        assert!(
            c2.matches_golden,
            "golden TCB diverged from live axiom set; added={:?} removed={:?}. \
             Regenerate data/soundness_tcb.json via SoundnessCertificate::golden_from_env \
             (a reviewed event).",
            c2.added_vs_golden, c2.removed_vs_golden
        );
    }

    /// The "make it 3" foundational invariant. The four builtin quotient
    /// primitives (`Quot`, `Quot.mk`, `Quot.lift`, `Quot.ind`) are type-formers
    /// and eliminators with kernel-implemented typing + reduction rules — part of
    /// THE KERNEL CHECKER, not the asserted-axiom allowlist. They MUST be
    /// classified as builtin (not axioms): excluded from `all_axioms`,
    /// `trusted_axioms`, and `foundational`, and enumerated transparently in
    /// `builtin_quot_primitives`. Only `Quot.sound` (a pure-`Prop` equality with
    /// no computational content) is a genuine quotient axiom and stays
    /// foundational. This pins the canonical foundational base to EXACTLY the
    /// three Lean axioms `{Classical.choice, Quot.sound, propext}` and fails
    /// closed if a future edit re-counts a quotient primitive as an axiom.
    #[test]
    fn builtin_quot_primitives_are_not_axioms() {
        let env = Environment::soundness_certificate_env().expect("build certificate env");
        let c2 = env.certify_c2_tcb();

        let quot_prims = ["Quot", "Quot.mk", "Quot.lift", "Quot.ind"];
        let builtin: BTreeSet<&str> = c2
            .builtin_quot_primitives
            .iter()
            .map(String::as_str)
            .collect();
        let all: BTreeSet<&str> = c2.all_axioms.iter().map(String::as_str).collect();
        let trusted: BTreeSet<&str> = c2.trusted_axioms.iter().map(String::as_str).collect();
        let foundational: BTreeSet<&str> = c2.foundational.iter().map(String::as_str).collect();

        for p in quot_prims {
            assert!(
                builtin.contains(p),
                "`{p}` must be classified a builtin quotient primitive; builtin={:?}",
                c2.builtin_quot_primitives
            );
            assert!(!all.contains(p), "`{p}` must NOT be an axiom (all_axioms)");
            assert!(!trusted.contains(p), "`{p}` must NOT be a trusted axiom");
            assert!(!foundational.contains(p), "`{p}` must NOT be foundational");
        }

        // `Quot.sound` IS a genuine axiom and stays foundational.
        assert!(
            foundational.contains("Quot.sound"),
            "`Quot.sound` must remain a foundational axiom; foundational={:?}",
            c2.foundational
        );
        assert!(
            !builtin.contains("Quot.sound"),
            "`Quot.sound` is an axiom, not a builtin quotient primitive"
        );

        // The canonical Lean foundational base is EXACTLY these three axioms.
        let expected: BTreeSet<&str> = ["Classical.choice", "Quot.sound", "propext"]
            .into_iter()
            .collect();
        assert_eq!(
            foundational, expected,
            "foundational axioms must be exactly {{Classical.choice, Quot.sound, propext}} \
             (\"make it 3\"); got {:?}",
            c2.foundational
        );
    }
}
