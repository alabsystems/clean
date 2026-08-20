// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Proof evidence and digests: [`ProofEvidence`], [`ProofCertificate`],
//! [`ProofCertificateRef`], the [`ProofDigest`] / [`ProofDigestAlgorithm`]
//! pair and its deterministic digest infrastructure, plus the CleanCic
//! lineage helpers ([`clean_cic_lineage_digest`],
//! [`obligation_has_matching_clean_cic`]).

use super::obligations::{ObligationKind, ProofObligation, ProofObligationSourceIdentity};
use crate::value::{FuncId, ProofId};

/// Kernel re-check directive carried by a [`ProofEvidence::CleanCic`] payload.
///
/// The bare `CleanCic { term, context, lineage }` payload only lets a validator
/// confirm the *lineage binding* (that the certificate is bound to this
/// obligation). It does not, by itself, say *which* theorem establishes the
/// claim, so a validator cannot re-check the proof term.
///
/// When this directive is present, `trust_ir_build::validate` builds the named
/// [`Self::anchor`] environment **in-process** inside the trusted
/// `clean-kernel` CIC type-checker, looks up each theorem in [`Self::theorems`],
/// and runs the validator path registered for that anchor:
///
/// 1. a payload-aware path re-derives the exact obligation statement (for
///    example backend translation validation or SAT-resolution), rather than
///    treating a true but unrelated library theorem as evidence;
/// 2. [`clean_kernel::Environment::audit_certification`] checks the rooted
///    theorem judgment and its complete type/value dependency closure,
///    rejecting trust markers, unsafe/partial or unchecked declarations,
///    noncanonical foundations, missing values, and dependency cycles; and
/// 3. an independent micro re-check must not disagree with the kernel.
///
/// This is the de Bruijn criterion realized in-process: an untrusted producer
/// emits evidence, the validator reconstructs the claim, and the small trusted
/// kernel checks the resulting judgment — no external `lean` binary, PATH, or
/// `#print axioms` parsing. A fixed theorem-library recheck alone is assurance
/// about that library; it cannot mint `Certified` for an arbitrary obligation.
/// Missing or unbound directives are rejected fail-closed.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct CleanCicKernelRecheck {
    /// Canonical source module for this anchor (for example
    /// `"Crownproof.SlackCertZ"`). Obligation-aware validators require the
    /// exact validator-owned anchor↔module pair; this is not a free-form label.
    /// It is also bound into the evidence digest.
    pub module: String,
    /// Fully-qualified kernel theorem names whose proof TERM is re-checked
    /// in-process (e.g. `"NNVerify.farkas_combine_2_le_bound"`). Each must be a
    /// `Declaration::Theorem` in the built [`Self::anchor`] environment, its
    /// proof term and rooted dependency closure must pass the kernel audit. All
    /// must pass, and the validator must independently bind their statement to
    /// the obligation before they carry certification authority.
    pub theorems: Vec<String>,
    /// Identifier for the in-process kernel anchor whose `clean_kernel`
    /// `Environment` is built and re-checked. This replaces the former external
    /// `lean_file` path: the term is constructed and type-checked inside the
    /// trusted kernel, not shelled out to an external compiler. The only
    /// recognized values are the `KERNEL_ANCHOR_*` constants in this module.
    /// Recognition only builds an environment; a separate, anchor-specific
    /// obligation-binding dispatcher is required to mint `Certified`. Unknown
    /// or unbound anchors reject fail-closed.
    pub anchor: String,
    /// Producer-declared non-foundational axiom metadata. This list grants no
    /// authority by itself: an axiom is admissible only when the validator's own
    /// exact `(theorem, axiom)` policy also permits it. Canonical CIC foundations
    /// are recognized by exact declaration kind, universe arity, and statement;
    /// trust markers are never admissible.
    pub allowed_axioms: Vec<String>,
}

/// The in-process kernel anchor identifier for the Mathlib-free constructive
/// Farkas soundness theorems (`NNVerify.farkas_scale` /
/// `NNVerify.farkas_combine_2` / `NNVerify.farkas_combine_2_le_bound`). The
/// re-checker builds this environment via
/// `clean_kernel::Environment::init_nn_verify_farkas_constructive`.
pub const KERNEL_ANCHOR_FARKAS_CONSTRUCTIVE: &str = "nn_verify_farkas_constructive";

/// The in-process kernel anchor identifier for the **give-back refinement**
/// soundness theorem(s) that certify a [`ObligationKind::GiveBackRefinement`](crate::proof::ObligationKind)
/// obligation (the Aeneas-style `&mut` give-back view, re-proved inside Clean).
/// The re-checker builds this environment via
/// `clean_kernel::Environment::init_giveback_refinement`, which admits the
/// give-back lens laws as Mathlib-free, axiom-clean `Declaration::Theorem`s
/// constructed purely by `clean-kernel` declaration builders — so the trusted
/// kernel re-checks the proof TERM in-process, with Aeneas nowhere in the chain.
/// First certified instance: `RustSem.GiveBack.backId_roundTrips` (the identity
/// backward function's round-trip law). Any other anchor string is rejected
/// fail-closed by the re-checker.
pub const KERNEL_ANCHOR_GIVEBACK_REFINEMENT: &str = "rust_giveback_refinement";

/// In-process kernel anchor for the **`u32` wraparound** give-back refinement,
/// built by `clean_kernel::Environment::init_giveback_u32_refinement`. Certifies
/// that the give-back of `*x += 1` faithfully models Rust `u32` overflow:
/// `RustSem.GiveBack.incrBackU32 (u32::MAX) = 0` (true over `u32 mod 2³²`, false
/// over `Nat`). Isolated from [`KERNEL_ANCHOR_GIVEBACK_REFINEMENT`] because it
/// admits `UInt32`/`Fin` (whose kernel setup carries domain axioms); the cited
/// theorem's own closure stays axiom-clean (the per-theorem re-check is what
/// matters). Any other anchor string is rejected fail-closed.
pub const KERNEL_ANCHOR_GIVEBACK_U32: &str = "rust_giveback_u32";

/// In-process kernel anchor for the **aggregate** give-back refinement (a `&mut`
/// into a FIELD of an aggregate), built by
/// `clean_kernel::Environment::init_giveback_aggregate_refinement`. Certifies the
/// genuine Aeneas backward function `aggFstBack p v' = Prod.mk v' p.snd` (whole-
/// aggregate reconstruction with the sibling field framed) via its four lens laws
/// over `Prod Nat Nat` — put-get, get-put (round-trip; structure-eta), frame, and
/// put-put — plus the composed give-back of `p.0 += 1`. Each cited law is axiom-
/// clean (`Eq.refl` over δ + projection-ι + structure-eta). Any other anchor
/// string is rejected fail-closed.
pub const KERNEL_ANCHOR_GIVEBACK_AGGREGATE: &str = "rust_giveback_aggregate";

/// In-process kernel anchor for the **sum-type (enum)** give-back refinement (a
/// `&mut` into a VARIANT PAYLOAD), built by
/// `clean_kernel::Environment::init_giveback_enum_refinement`. Certifies the Aeneas
/// backward function for an `Option<u32>` payload borrow, whose laws are proved by
/// `Option.rec` CASE ANALYSIS (sum types have no eta, so the `∀ o` laws genuinely
/// split per variant): frame-none, set-some, put-put (`∀ o`), round-trip (`∀ o`),
/// and the `*x += 1` map (incr-some). Each cited law is axiom-clean. Any other
/// anchor string is rejected fail-closed.
pub const KERNEL_ANCHOR_GIVEBACK_ENUM: &str = "rust_giveback_enum";

/// In-process kernel anchor for the **recursive** give-back refinement (the
/// `list_nth_mut` tier — a `&mut` into a `List<u32>`), built by
/// `clean_kernel::Environment::init_giveback_list_refinement`. Certifies the
/// give-back over an arbitrarily-deep recursive structure: `listSelf`/`listIncr`
/// (`List.rec`) and the load-bearing round-trip `∀ l, listSelf l = l`, proved by
/// STRUCTURAL INDUCTION (`List.rec` whose cons minor consumes the recursion
/// hypothesis, lifted via `congrArg`) — the capability beyond the non-recursive
/// product/sum cases. Each cited law is axiom-clean. Any other anchor string is
/// rejected fail-closed.
pub const KERNEL_ANCHOR_GIVEBACK_LIST: &str = "rust_giveback_list";

/// In-process kernel anchor for the **disjoint-mutable-borrows** give-back (the
/// `split_at_mut` separation property), built by
/// `clean_kernel::Environment::init_giveback_split_refinement`. Certifies that two
/// simultaneous `&mut`s into disjoint fields of a pair have non-interfering
/// backward functions whose recombination COMMUTES (`split_commute`) — the
/// soundness witness for Rust's aliasing-XOR-mutation. Each cited law is
/// axiom-clean. Any other anchor string is rejected fail-closed.
pub const KERNEL_ANCHOR_GIVEBACK_SPLIT: &str = "rust_giveback_split";

/// In-process kernel anchor for the **control-flow** give-back (the give-back of a
/// conditional mutation `if c { *x = v }`), built by
/// `clean_kernel::Environment::init_giveback_cond_refinement`. Certifies that the
/// backward function branches on the runtime flag — the per-branch laws (taken /
/// framed) and the `∀ c` no-op law proved by `Bool.rec` case analysis. Each cited
/// law is axiom-clean. Any other anchor string is rejected fail-closed.
pub const KERNEL_ANCHOR_GIVEBACK_COND: &str = "rust_giveback_cond";

/// In-process kernel anchor for the **nested** give-back (a `&mut` into a field
/// nested two levels deep — `&mut p.0.0`; the data-nesting analog of a
/// `&mut &mut T` reborrow), built by
/// `clean_kernel::Environment::init_giveback_nested_refinement`. Certifies the
/// two-level reconstruction: put-get (ι×2), frame at each level, and the nested
/// round-trip proved by structure-eta firing at BOTH levels. Each cited law is
/// axiom-clean. Any other anchor string is rejected fail-closed.
pub const KERNEL_ANCHOR_GIVEBACK_NESTED: &str = "rust_giveback_nested";

/// In-process kernel anchor for the **loop** give-back (Aeneas's loop backward
/// functions — `for x in &mut l { *x += 1 }`), built by
/// `clean_kernel::Environment::init_giveback_loop_refinement`. Certifies that the
/// loop's backward function (`map pred`) inverts its forward (`map +1`) over the
/// ENTIRE list — the round-trip `∀ l, loopBack (loopFwd l) = l` proved by `List.rec`
/// structural induction (give-back through iteration, for all lengths at once).
/// Each cited law is axiom-clean. Any other anchor string is rejected fail-closed.
pub const KERNEL_ANCHOR_GIVEBACK_LOOP: &str = "rust_giveback_loop";

/// In-process kernel anchor for the **generic** give-back (`fn f<T>(x: &mut T)`),
/// built by `clean_kernel::Environment::init_giveback_generics_refinement`.
/// Certifies that the value-polymorphic give-back law specializes to concrete `T`
/// (a scalar `Nat`, a `Bool`, and a STRUCT `Prod Nat Nat`) by instantiation — one
/// proof covers every `T` (monomorphization made sound). Each cited law is
/// axiom-clean. Any other anchor string is rejected fail-closed.
pub const KERNEL_ANCHOR_GIVEBACK_GENERICS: &str = "rust_giveback_generics";

/// In-process kernel anchor for the **closure** give-back (an `FnMut` reconstructs
/// its captured environment), built by
/// `clean_kernel::Environment::init_giveback_closure_refinement`. Certifies that a
/// closure's env give-back mutates the `mut` capture, frames the `ref` capture, and
/// (the no-op-call law) reconstructs the whole captured env unchanged. Each cited
/// law is axiom-clean. Any other anchor string is rejected fail-closed.
pub const KERNEL_ANCHOR_GIVEBACK_CLOSURE: &str = "rust_giveback_closure";

/// In-process kernel anchor for the **trait** give-back (dynamic dispatch through a
/// vtable — trait objects), built by
/// `clean_kernel::Environment::init_giveback_trait_refinement`. Certifies the
/// dyn-dispatch fact (`vtblDispatch (mk f d) x = f x` — the call resolves to the
/// vtable's method) and concrete impls resolving to distinct give-back methods.
/// Each cited law is axiom-clean. Any other anchor string is rejected fail-closed.
pub const KERNEL_ANCHOR_GIVEBACK_TRAIT: &str = "rust_giveback_trait";

/// In-process kernel anchor for the **Vec/std-collection** give-back (a `Vec` used
/// as a stack — push/pop round-trip), built by
/// `clean_kernel::Environment::init_giveback_vec_refinement`. Certifies the LIFO
/// round-trip `vecHead (vecPush x v) = x` and `vecTail (vecPush x v) = v` — a `Vec`
/// operation and its inverse cancel. Each cited law is axiom-clean. Any other
/// anchor string is rejected fail-closed.
pub const KERNEL_ANCHOR_GIVEBACK_VEC: &str = "rust_giveback_vec";

/// In-process kernel anchor for the **HashMap** give-back (a `HashMap<Nat,Nat>`
/// with presence/absence, `Nat → Option Nat`), built by
/// `clean_kernel::Environment::init_giveback_hashmap_refinement`. Certifies the map
/// laws `mapGet (mapInsert m k v) k = some v` and `mapGet (mapRemove m k) k = none`
/// (the key is genuinely absent after removal). Each cited law is axiom-clean. Any
/// other anchor string is rejected fail-closed.
pub const KERNEL_ANCHOR_GIVEBACK_HASHMAP: &str = "rust_giveback_hashmap";

/// In-process kernel anchor for the **operational step + bisimulation** (the first
/// increment of the T-step tier), built by
/// `clean_kernel::Environment::init_giveback_step_refinement`. Certifies that the
/// give-back model simulates a reflected small-step `gbStep` over the store, indexed
/// by an operation (write / incr): `gbLookup (gbStep s a (some v)) a = v` and
/// `gbLookup (gbStep s a none) a = incrBack (gbLookup s a)`. Each cited law is
/// axiom-clean. Any other anchor string is rejected fail-closed.
pub const KERNEL_ANCHOR_GIVEBACK_STEP: &str = "rust_giveback_step";

/// In-process kernel anchor for a **TrustCg lowering rule's SAT refutation**
/// (t-silicon route 1, first milestone), built by
/// `clean_kernel::Environment::with_prelude` + `init_resolution_soundness` —
/// the EXISTING verified resolution reflection checker
/// (`Clean.Res.checkRefutes3`, PROVED sound via `Clean.Res.checkRefutes3_sound`,
/// clean-kernel `resolution_check.rs` / `resolution_soundness.rs`). Unlike the
/// other anchors, the cited theorem is **per-certificate ground data**: the
/// validator decodes the certificate's `term` bytes as a
/// [`SatResolutionCertPayload`](super::satres::SatResolutionCertPayload)
/// (clause list + binary resolution steps), registers
/// `TrustCg.LoweringRes.cert_unsat : Clean.Res.Unsat cs :=
/// checkRefutes3_sound cs steps (Eq.refl Bool Bool.true)` into the anchor
/// environment ITSELF (never trusting a producer-supplied kernel term), and
/// the kernel discharges it by reflection — a forged refutation reduces to
/// `Bool.false` and is rejected. The proof term is fully constructive (empty
/// structural axiom closure).
///
/// Provides non-authoritative CNF assurance for
/// [`ObligationKind::TranslationValidation`] candidates whose formula pins the
/// producer-selected clause list by digest
/// ([`satres_formula`](super::satres::satres_formula)). It does **not** certify
/// the obligation: the validator does not independently derive the exact
/// semantic miter from the lowering rule and Trust-IR function, and optional
/// provenance still asserts the final gate-DAG⇔semantics link. The validator
/// may replay the reflection proof for diagnostics/reporting, but rejects a
/// `Certified` claim through this anchor fail-closed.
///
/// [`ObligationKind::TranslationValidation`]: super::ObligationKind::TranslationValidation
pub const KERNEL_ANCHOR_TRUSTCG_LOWERING_RESOLUTION: &str = "trustcg_lowering_resolution";
/// In-process kernel anchor for the **clean-compiler backend
/// translation-validation** certificate (P2 — the first SEMANTICS-PRESERVATION
/// certificate for `clean compile --emit trustir/obj`). Unlike the fixed-law
/// give-back anchors, the certified theorem here is **per-declaration**: the
/// producer (clean's `emit_trust_ir_tv` minter, untrusted) records, for one
/// emitted function in the Fragment-2 arithmetic fragment (single block,
/// call-free, memory-free, branch-free: params + `Const Int` +
/// `BinOp{Add,Sub,Mul}` at one unsigned width `w` + `Return`), the equation
///
/// ```text
/// CleanTV.<fn>.denotes : ∀ (x1 … xn : Nat), ⟦emitted fn⟧ = ⟦original defn⟧
/// ```
///
/// over the shared `Nat`-mod-`2^w` denotation vocabulary (trust-ir's ratified
/// wrapping semantics, `docs/ub-numerics-policy.md`). The re-checker
/// (`trust_ir_build::validate`, feature `clean-tv-anchor`) builds the GROUND
/// `clean_kernel::Environment::with_prelude()` for this anchor, RE-DERIVES the
/// left-hand side from the module's own function (synthesis-by-recomputation —
/// a post-emit tamper of the body changes the re-derived LHS and the equation
/// no longer checks), decodes the comparand and proof term from the
/// certificate payload (`context` / `term`, a canonical resource-bounded codec
/// of `clean_kernel::Expr`),
/// declares the theorem in-process (the kernel type-checks the proof term on
/// insertion — the actual translation-validation judgment, decided by
/// definitional equality), and then runs the standard per-theorem re-check
/// (rooted authority audit + micro cross-validation). Only an
/// [`ObligationKind::TranslationValidation`] obligation may cite this anchor;
/// translation validation also has a distinct, formula-bound lowering-
/// resolution anchor. Any cross-domain use, unknown anchor, or this anchor
/// without the `clean-tv-anchor` feature is rejected fail-closed.
pub const KERNEL_ANCHOR_CLEAN_BACKEND_TV: &str = "clean_backend_tv";

/// The in-process kernel anchor identifier for the **literal Mathlib-dependent**
/// Crownproof slack-certificate soundness theorem
/// (`Crownproof.SlackCertZ.checkSlackEntailmentZ_sound`). Unlike
/// [`KERNEL_ANCHOR_FARKAS_CONSTRUCTIVE`] (which builds a Mathlib-free
/// constructive analog purely from `clean-kernel` declaration builders), this
/// anchor's environment is built by LOADING the vendored `.olean` closure of
/// `Crownproof.SlackCertZ` (Lean stdlib + Mathlib + the Crownproof library) into
/// the trusted `clean-kernel` environment, so the kernel re-checks the genuine
/// proof TERM Lean produced — not a re-statement.
///
/// The re-checker arm that builds this environment is compiled only under the
/// default-OFF `slackcertz-anchor` cargo feature of `trust-ir-build` (it pulls
/// the heavy `clean-mathverse`/`clean-olean` olean-load pipeline). When that
/// feature is off, this anchor falls to the unknown-anchor reject (fail-closed).
/// Even when the feature is on, the arm FAILS CLOSED if the oleans / lean lib
/// cannot be located, so a machine without the artifacts rejects rather than
/// faith-accepts. The closure load is a one-time ~18min / ~6GB cost; the kernel
/// judgment itself is a few seconds.
pub const KERNEL_ANCHOR_SLACKCERTZ: &str = "crownproof_slackcertz";

#[derive(Debug, Clone, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum ProofEvidence {
    SmtProof(Vec<u8>),
    LeanProof(String),
    KaniHarness(String),
    GammaCrownBound {
        epsilon: f64,
        verified_layers: u32,
    },
    TranslationValidation {
        rule_name: String,
        smt_hash: [u8; 32],
    },
    Trusted(String),
    /// Cross-language proof composition: this obligation is discharged because
    /// a callee already discharged the named obligation. The caller (which may
    /// be a different frontend language than the callee) inherits that result
    /// rather than re-proving it.
    ///
    /// This is *not* self-justifying evidence: a validator must confirm that
    /// `callee` exists and that `obligation` is itself discharged by ground
    /// (non-inherited) evidence somewhere in the module. See
    /// `trust_ir_build::validate` for the enforcement rule.
    InheritedFromCallee {
        /// The callee function whose proof is being composed in.
        callee: FuncId,
        /// The callee-side obligation (by module obligation id) relied upon.
        obligation: ProofId,
    },
    /// A kernel-checkable CIC evidence payload — the de Bruijn "Certified"
    /// tier. The exact `term`/`context` wire schema is anchor-specific and must
    /// be decoded with that schema's canonical, bounded decoder. A certifying
    /// validator reconstructs the claim from the obligation/module and checks
    /// the decoded evidence against it; non-empty opaque bytes are never proof.
    /// `lineage` is identity/replay binding only, not proof authority.
    CleanCic {
        term: Vec<u8>,
        context: Vec<u8>,
        lineage: ProofDigest,
        /// Optional kernel re-check directive. When present,
        /// `trust_ir_build::validate` actually re-runs the cited theorems in
        /// the kernel **in-process** instead of trusting the certificate. When
        /// absent, a validator that performs real kernel re-checking treats the
        /// certificate as unrecheckable and rejects it (fail-closed). The
        /// lineage-only helper may still report an identity match, but must not
        /// be used to admit the claim as discharged.
        #[cfg_attr(feature = "serde", serde(default))]
        kernel_recheck: Option<CleanCicKernelRecheck>,
    },
}

#[derive(Debug, Clone, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ProofCertificate {
    pub obligation: ProofId,
    pub prover: String,
    pub evidence: ProofEvidence,
}

/// Digest algorithm used by proof and artifact identities.
///
/// `Sha256` is mandatory for identities that cross an untrusted boundary or
/// participate in replay/authority selection. `TrustIrStableV1` is retained
/// only for legacy, non-security deterministic checksums; validators must never
/// use it as proof authority or content-addressed admission identity.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum ProofDigestAlgorithm {
    Sha256,
    TrustIrStableV1,
}

/// Fixed-width digest used to bind modules, certificates, and composed stages.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ProofDigest {
    pub algorithm: ProofDigestAlgorithm,
    pub bytes: [u8; 32],
}

impl ProofDigest {
    pub const fn sha256(bytes: [u8; 32]) -> Self {
        Self {
            algorithm: ProofDigestAlgorithm::Sha256,
            bytes,
        }
    }

    pub const fn zero() -> Self {
        Self {
            algorithm: ProofDigestAlgorithm::Sha256,
            bytes: [0u8; 32],
        }
    }

    pub fn trust_ir_stable(domain: &str, bytes: &[u8]) -> Self {
        let mut hasher = StableDigest::new(domain);
        hasher.update(bytes);
        Self {
            algorithm: ProofDigestAlgorithm::TrustIrStableV1,
            bytes: hasher.finish(),
        }
    }

    /// Domain-separated SHA-256 for security-relevant identities.
    ///
    /// The preimage is canonically framed as:
    ///
    /// `"trust-ir.sha256-domain.v1\0" || u64be(domain_len) || domain ||
    ///  u64be(payload_len) || payload`.
    ///
    /// Checked `usize`→`u64` conversions prevent silent length truncation. This
    /// API is the required replacement for [`Self::trust_ir_stable`] whenever a
    /// digest crosses serialization, selects evidence, or joins replay state.
    pub fn sha256_domain(domain: &str, bytes: &[u8]) -> Self {
        let domain_len = u64::try_from(domain.len())
            .expect("digest domain length exceeds canonical u64 framing");
        let payload_len = u64::try_from(bytes.len())
            .expect("digest payload length exceeds canonical u64 framing");
        let domain_len = domain_len.to_be_bytes();
        let payload_len = payload_len.to_be_bytes();
        Self::sha256(crate::request::sha256_parts(&[
            b"trust-ir.sha256-domain.v1\0",
            &domain_len,
            domain.as_bytes(),
            &payload_len,
            bytes,
        ]))
    }

    pub const fn is_zero(self) -> bool {
        let mut i = 0;
        while i < self.bytes.len() {
            if self.bytes[i] != 0 {
                return false;
            }
            i += 1;
        }
        true
    }
}

impl core::fmt::Display for ProofDigestAlgorithm {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.write_str(match self {
            ProofDigestAlgorithm::Sha256 => "sha256",
            ProofDigestAlgorithm::TrustIrStableV1 => "trust_ir-stable-v1",
        })
    }
}

impl core::fmt::Display for ProofDigest {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "{}:", self.algorithm)?;
        for byte in &self.bytes {
            write!(f, "{byte:02x}")?;
        }
        Ok(())
    }
}

/// Stable reference to a certificate in a module's certificate table.
///
/// Existing `ProofCertificate`s do not have first-class IDs. This selector
/// binds the obligation, prover identity, and deterministic evidence digest so
/// lineage consumers can distinguish two certificates for the same obligation.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ProofCertificateRef {
    pub obligation: ProofId,
    pub prover: String,
    pub evidence_digest: ProofDigest,
}

impl ProofCertificate {
    pub fn evidence_digest(&self) -> ProofDigest {
        let mut bytes = Vec::new();
        write_proof_evidence_stable(&mut bytes, &self.evidence);
        ProofDigest::sha256_domain("trust_ir.proof.evidence.v2", &bytes)
    }

    pub fn stable_digest(&self) -> ProofDigest {
        let mut bytes = Vec::new();
        write_u32_stable(&mut bytes, self.obligation.index());
        write_str_stable(&mut bytes, &self.prover);
        write_digest_stable(&mut bytes, &self.evidence_digest());
        ProofDigest::sha256_domain("trust_ir.proof.certificate.v2", &bytes)
    }

    pub fn lineage_ref(&self) -> ProofCertificateRef {
        ProofCertificateRef {
            obligation: self.obligation,
            prover: self.prover.clone(),
            evidence_digest: self.evidence_digest(),
        }
    }

    pub fn uses_trusted_evidence(&self) -> bool {
        matches!(self.evidence, ProofEvidence::Trusted(_))
    }
}

impl ProofEvidence {
    /// The lineage digest carried by a [`ProofEvidence::CleanCic`] payload, or
    /// `None` for any other evidence kind.
    pub fn clean_cic_lineage(&self) -> Option<ProofDigest> {
        match self {
            ProofEvidence::CleanCic { lineage, .. } => Some(*lineage),
            _ => None,
        }
    }

    /// The kernel re-check directive carried by a [`ProofEvidence::CleanCic`]
    /// payload, or `None` for any other evidence kind (or a `CleanCic` payload
    /// minted without one).
    pub fn clean_cic_kernel_recheck(&self) -> Option<&CleanCicKernelRecheck> {
        match self {
            ProofEvidence::CleanCic { kernel_recheck, .. } => kernel_recheck.as_ref(),
            _ => None,
        }
    }
}

/// Deterministic digest binding a [`ProofEvidence::CleanCic`] certificate to the
/// exact obligation it certifies: its id, kind, description, formula, optional
/// function scope, and embedded source/public identity — i.e. the complete
/// stored *claim*, independent of the mutable [`ProofStatus`] label. The binding uses SHA-256 because lineage
/// crosses an untrusted serialization boundary; the non-cryptographic stable
/// checksum is reserved for in-memory identity/caching uses.
///
/// `Certified` is the kernel-checkable ("CleanCic") tier — strictly stronger
/// than `Trusted`, which is a manual audit taken on faith. That extra strength
/// is sound only when the obligation actually carries a `CleanCic` certificate
/// whose `lineage` equals this digest. The binding stops a `CleanCic`
/// certificate minted for one obligation from being replayed to certify a
/// different (e.g. weaker) obligation, and — together with the status<->evidence
/// invariant enforced by `trust_ir_build::validate` and the native
/// verification-bundle validators — stops a producer from stamping `Certified`
/// with no kernel-checkable evidence at all.
///
/// [`ProofStatus`]: super::obligations::ProofStatus
pub fn clean_cic_lineage_digest(obligation: &ProofObligation) -> ProofDigest {
    let mut bytes = Vec::new();
    write_u32_stable(&mut bytes, obligation.id.index());
    write_u8_stable(&mut bytes, obligation_kind_tag(&obligation.kind));
    write_str_stable(&mut bytes, &obligation.description);
    match &obligation.formula {
        None => write_u8_stable(&mut bytes, 0),
        Some(formula) => {
            write_u8_stable(&mut bytes, 1);
            write_str_stable(&mut bytes, &formula.schema);
            write_str_stable(&mut bytes, &formula.payload);
            match formula.smtlib.as_deref() {
                None => write_u8_stable(&mut bytes, 0),
                Some(s) => {
                    write_u8_stable(&mut bytes, 1);
                    write_str_stable(&mut bytes, s);
                }
            }
            match formula.sort.as_deref() {
                None => write_u8_stable(&mut bytes, 0),
                Some(s) => {
                    write_u8_stable(&mut bytes, 1);
                    write_str_stable(&mut bytes, s);
                }
            }
        }
    }
    match obligation.function {
        None => write_u8_stable(&mut bytes, 0),
        Some(function) => {
            write_u8_stable(&mut bytes, 1);
            write_u32_stable(&mut bytes, function.index());
        }
    }
    write_proof_obligation_source_identity_stable(&mut bytes, obligation.source.as_ref());
    ProofDigest::sha256_domain("trust_ir.proof.clean_cic.lineage.v4", &bytes)
}

/// Content bytes + SHA-256 behind [`crate::Module::obligation_digest`] (v23,
/// WS4-M2 cert-cache key). See that method for the identity contract; this
/// helper owns the byte layout:
///
/// `domain || kind tag || description || formula(presence, schema, payload,
/// smtlib, sort) || source/public identity || function scope(presence, name,
/// canonical content, entry block index, summary(presence, requires, ensures,
/// params))` — all via the
/// `write_*_stable` length-prefixed encoders, hashed with the in-crate
/// SHA-256. `entry` and `summary` are hashed explicitly because the canonical
/// text form carries neither (the text format has no entry marker or summary
/// syntax), yet both are proof-relevant content: `entry` decides execution
/// order, and `summary.requires`/`ensures` are the contract a cached
/// certificate may have assumed. Deliberately EXCLUDED: [`ProofStatus`] and
/// [`FunctionSummary::proved`] (both mutable verification progress, not
/// identity) and the obligation's own `ProofId` / `FuncId` (renumbering is
/// not identity either).
///
/// v2 bumped the domain from `…digest.v1` when `entry` and `summary` were
/// added to the layout (soundness fix: a contract or entry-block edit must
/// invalidate the cache slot). v3 replaced the ad hoc embedded-domain preimage
/// and truncating 32-bit sequence lengths with `sha256_domain` framing and
/// checked 64-bit lengths. v4 adds the embedded source identity, exact range,
/// and atomic public id/digest so cache entries cannot cross frontend proof
/// units that happen to carry the same human-readable claim.
///
/// [`ProofStatus`]: super::obligations::ProofStatus
/// [`FunctionSummary::proved`]: crate::FunctionSummary::proved
#[cfg(feature = "fmt")]
pub(crate) fn obligation_content_digest(
    obligation: &ProofObligation,
    function_content: Option<(&crate::Function, &str)>,
) -> ProofDigest {
    let mut bytes = Vec::new();
    write_u8_stable(&mut bytes, obligation_kind_tag(&obligation.kind));
    write_str_stable(&mut bytes, &obligation.description);
    match &obligation.formula {
        None => write_u8_stable(&mut bytes, 0),
        Some(formula) => {
            write_u8_stable(&mut bytes, 1);
            write_proof_formula_stable(&mut bytes, formula);
        }
    }
    write_proof_obligation_source_identity_stable(&mut bytes, obligation.source.as_ref());
    match function_content {
        None => write_u8_stable(&mut bytes, 0),
        Some((func, content)) => {
            write_u8_stable(&mut bytes, 1);
            write_str_stable(&mut bytes, &func.name);
            write_str_stable(&mut bytes, content);
            write_u32_stable(&mut bytes, func.entry.index());
            match &func.summary {
                None => write_u8_stable(&mut bytes, 0),
                Some(summary) => {
                    write_u8_stable(&mut bytes, 1);
                    write_len_stable(&mut bytes, summary.requires.len());
                    for clause in &summary.requires {
                        write_proof_formula_stable(&mut bytes, clause);
                    }
                    write_len_stable(&mut bytes, summary.ensures.len());
                    for clause in &summary.ensures {
                        write_proof_formula_stable(&mut bytes, clause);
                    }
                    write_len_stable(&mut bytes, summary.params.len());
                    for param in &summary.params {
                        write_str_stable(&mut bytes, param);
                    }
                }
            }
        }
    }
    ProofDigest::sha256_domain("trust_ir.obligation.digest.v4", &bytes)
}

/// Stable length-prefixed encoding of one [`ProofFormula`]: schema, payload,
/// then presence-prefixed `smtlib` and `sort`. Shared by the obligation
/// formula and the summary contract clauses in
/// [`obligation_content_digest`].
#[cfg(feature = "fmt")]
fn write_proof_formula_stable(out: &mut Vec<u8>, formula: &super::obligations::ProofFormula) {
    write_str_stable(out, &formula.schema);
    write_str_stable(out, &formula.payload);
    match formula.smtlib.as_deref() {
        None => write_u8_stable(out, 0),
        Some(s) => {
            write_u8_stable(out, 1);
            write_str_stable(out, s);
        }
    }
    match formula.sort.as_deref() {
        None => write_u8_stable(out, 0),
        Some(s) => {
            write_u8_stable(out, 1);
            write_str_stable(out, s);
        }
    }
}

pub(crate) fn obligation_kind_tag(kind: &ObligationKind) -> u8 {
    match kind {
        ObligationKind::Precondition => 0,
        ObligationKind::Postcondition => 1,
        ObligationKind::LoopInvariant => 2,
        ObligationKind::TypeInvariant => 3,
        ObligationKind::RefinementType => 4,
        ObligationKind::TranslationValidation => 5,
        ObligationKind::MemorySafety => 6,
        ObligationKind::PanicFreedom => 7,
        ObligationKind::TemporalSafety => 8,
        ObligationKind::Liveness => 9,
        ObligationKind::ArithmeticSafety => 10,
        ObligationKind::BoundsCheck => 11,
        ObligationKind::GiveBackRefinement => 12,
    }
}

/// Returns `true` iff `certificates` contains a [`ProofEvidence::CleanCic`]
/// certificate for `obligation` whose `lineage` matches
/// [`clean_cic_lineage_digest`] — a kernel-checkable certificate genuinely bound
/// to this obligation.
///
/// This is an identity/binding helper, **not an admissibility gate**. An
/// obligation stamped [`ProofStatus::Certified`] is authoritative only after
/// [`obligation_has_kernel_rechecked_clean_cic`] (or an equally strict,
/// obligation-aware validator) succeeds. Both the payload and lineage can be
/// produced from public data, so a kernel-less consumer must fail closed rather
/// than treating this match as discharged. The non-empty check merely rejects
/// the most obviously content-free carrier.
///
/// [`ProofStatus::Certified`]: super::obligations::ProofStatus::Certified
/// [`ProofStatus::Trusted`]: super::obligations::ProofStatus::Trusted
pub fn obligation_has_matching_clean_cic(
    obligation: &ProofObligation,
    certificates: &[ProofCertificate],
) -> bool {
    let expected = clean_cic_lineage_digest(obligation);
    certificates.iter().any(|cert| {
        cert.obligation == obligation.id
            && matches!(
                &cert.evidence,
                ProofEvidence::CleanCic { term, lineage, .. }
                    if !term.is_empty() && *lineage == expected
            )
    })
}

/// A consumer-side re-validator for the *kernel-checkable content* of a
/// [`ProofEvidence::CleanCic`] certificate.
///
/// [`obligation_has_matching_clean_cic`] is a **lineage-only identity check**: it
/// confirms a certificate is *bound* to an obligation but never decodes or
/// re-checks the certificate's proof-`term` bytes. A serialized module read off
/// disk is therefore *trusted-on-read* at that gate — a tampered term whose
/// lineage still matches would be admitted. This trait closes that surface:
/// [`obligation_has_kernel_rechecked_clean_cic`] additionally requires an
/// implementation to re-establish the obligation's claim **in the Clean kernel**
/// from the certificate's own serialized proof term (the de Bruijn criterion).
///
/// # SOUNDNESS CONTRACT (implementors MUST uphold)
///
/// [`Self::kernel_rechecks_clean_cic`] returns `true` **only** when, in this
/// process, it has (1) decoded the certificate's proof-`term` bytes, (2)
/// independently reconstructed the obligation's own claim from the OBLIGATION
/// (never from the certificate's untrusted bytes), and (3) had the trusted Clean
/// kernel confirm the decoded term inhabits that claim. Any decode / kernel /
/// reconstruction failure — or any inability to run the kernel at all — MUST
/// return `false` (fail-closed). It must never be a second digest/lineage check
/// or a "trust me".
pub trait CleanCicRechecker {
    /// Re-validate `cert`'s serialized proof term against `obligation`'s own
    /// claim in the Clean kernel. Fail-closed: `false` on any failure.
    fn kernel_rechecks_clean_cic(
        &self,
        obligation: &ProofObligation,
        cert: &ProofCertificate,
    ) -> bool;
}

/// Validator capability for turning one concrete certificate into proof
/// authority. Implementations must replay the evidence against the exact
/// obligation in this process; status labels, hashes, provenance strings, and
/// opaque proof bytes alone must return `false`.
pub trait ProofAuthorityRechecker {
    fn replays_authority(
        &self,
        obligation: &ProofObligation,
        certificate: &ProofCertificate,
    ) -> bool;
}

/// Validator capability for turning one certificate into proof authority **with
/// the whole module in scope**.
///
/// # Why this exists alongside [`ProofAuthorityRechecker`]
///
/// A `CleanCic` certificate is self-contained: the obligation and the term are
/// enough to re-check it. A certificate whose claim is a fact *about the IR* is
/// not — re-establishing it requires reading the code the obligation is sited
/// in. The bit-blast route is exactly that case: the only honest binding between
/// a stored refutation and an obligation is to re-derive the goal from the
/// module at `ObligationSite`, because the refutation payload does not record
/// which formula it is about.
///
/// # Soundness contract
///
/// An implementation MUST:
///
/// * reconstruct the claim from `module` and `obligation` — never from the
///   certificate's own bytes, which are an untrusted artifact;
/// * verify the reconstructed claim is the one the certificate establishes,
///   not merely that the certificate is internally consistent;
/// * fail closed (`false`) on every decode failure, every mismatch, and every
///   unsupported shape.
///
/// The `module` is a PARAMETER rather than captured state on purpose: a
/// capability built against one module cannot be applied to another, so the
/// wrong-module hazard is removed structurally instead of by discipline.
pub trait ModuleProofAuthority {
    fn replays_authority(
        &self,
        module: &crate::Module,
        obligation: &ProofObligation,
        certificate: &ProofCertificate,
    ) -> bool;
}

/// Fail-closed [`ModuleProofAuthority`]: replays nothing, authorizes nothing.
///
/// This is what the structural entry points supply, which is why
/// `validate_module` can never admit a `Discharged` row on its own.
#[derive(Debug, Clone, Copy, Default)]
pub struct RejectingModuleProofAuthority;

impl ModuleProofAuthority for RejectingModuleProofAuthority {
    #[inline]
    fn replays_authority(
        &self,
        _module: &crate::Module,
        _obligation: &ProofObligation,
        _certificate: &ProofCertificate,
    ) -> bool {
        false
    }
}

/// Fail-closed authority capability for structural-only consumers.
#[derive(Debug, Clone, Copy, Default)]
pub struct RejectingProofAuthorityRechecker;

impl ProofAuthorityRechecker for RejectingProofAuthorityRechecker {
    fn replays_authority(
        &self,
        _obligation: &ProofObligation,
        _certificate: &ProofCertificate,
    ) -> bool {
        false
    }
}

/// Adapter from an obligation-aware Clean kernel rechecker to the shared proof
/// authority capability.
pub struct CleanCicProofAuthorityRechecker<'a> {
    pub clean_cic: &'a dyn CleanCicRechecker,
}

impl ProofAuthorityRechecker for CleanCicProofAuthorityRechecker<'_> {
    fn replays_authority(
        &self,
        obligation: &ProofObligation,
        certificate: &ProofCertificate,
    ) -> bool {
        certificate.obligation == obligation.id
            && matches!(
                &certificate.evidence,
                ProofEvidence::CleanCic { term, lineage, .. }
                    if !term.is_empty() && *lineage == clean_cic_lineage_digest(obligation)
            )
            && self
                .clean_cic
                .kernel_rechecks_clean_cic(obligation, certificate)
    }
}

/// True only when a strong-status obligation (`Discharged` or `Certified`) has
/// at least one exact certificate replayed by the supplied validator
/// capability. This is the shared authority predicate for admission,
/// inheritance, proof references, and lineage closure.
pub fn obligation_has_replayed_authority(
    obligation: &ProofObligation,
    certificates: &[ProofCertificate],
    rechecker: &dyn ProofAuthorityRechecker,
) -> bool {
    matches!(
        obligation.status,
        super::obligations::ProofStatus::Discharged | super::obligations::ProofStatus::Certified
    ) && certificates
        .iter()
        .any(|certificate| rechecker.replays_authority(obligation, certificate))
}

/// The **fail-closed default** [`CleanCicRechecker`]: it re-checks nothing and
/// therefore rejects every certificate.
///
/// Use it in any build or consumer that cannot run the Clean kernel (e.g. the
/// default zero-dependency `trust-ir` format build). Wiring a consumer with this
/// rechecker means [`obligation_has_kernel_rechecked_clean_cic`] is *always*
/// `false`, so a `Certified` obligation is never promoted above the weaker tiers
/// unless a real, kernel-backed rechecker is injected. This is the dependency
/// inversion that lets a submodule with no kernel dependency stay sound: it
/// degrades `Certified` rather than trusting the term on read.
#[derive(Debug, Clone, Copy, Default)]
pub struct RejectingCleanCicRechecker;

impl CleanCicRechecker for RejectingCleanCicRechecker {
    #[inline]
    fn kernel_rechecks_clean_cic(
        &self,
        _obligation: &ProofObligation,
        _cert: &ProofCertificate,
    ) -> bool {
        false
    }
}

/// The **sound** admissibility gate for the `Certified` tier: it admits an
/// obligation only when it carries a lineage-bound, non-empty-term
/// [`ProofEvidence::CleanCic`] certificate (exactly as
/// [`obligation_has_matching_clean_cic`]) **AND** `rechecker` re-establishes the
/// obligation's claim in the Clean kernel from that certificate's serialized
/// proof-term bytes.
///
/// This removes the trusted-on-read surface: a serialized module's `CleanCic`
/// obligation is accepted only if the kernel re-checks the term, not merely the
/// lineage digest. With [`RejectingCleanCicRechecker`] (the fail-closed default,
/// for kernel-less builds) it is always `false`; a kernel-backed
/// [`CleanCicRechecker`] injected by a kernel-capable orchestrator makes it a
/// genuine de Bruijn re-check.
pub fn obligation_has_kernel_rechecked_clean_cic(
    obligation: &ProofObligation,
    certificates: &[ProofCertificate],
    rechecker: &dyn CleanCicRechecker,
) -> bool {
    let expected = clean_cic_lineage_digest(obligation);
    certificates.iter().any(|cert| {
        cert.obligation == obligation.id
            && matches!(
                &cert.evidence,
                ProofEvidence::CleanCic { term, lineage, .. }
                    if !term.is_empty() && *lineage == expected
            )
            && rechecker.kernel_rechecks_clean_cic(obligation, cert)
    })
}

struct StableDigest {
    lanes: [u64; 4],
}

impl StableDigest {
    fn new(domain: &str) -> Self {
        let mut digest = Self {
            lanes: [
                0xcbf29ce484222325,
                0x9e3779b97f4a7c15,
                0x6a09e667f3bcc909,
                0xbb67ae8584caa73b,
            ],
        };
        digest.update(domain.as_bytes());
        digest.update(&[0]);
        digest
    }

    fn update(&mut self, bytes: &[u8]) {
        let byte_len =
            u64::try_from(bytes.len()).expect("legacy checksum input length exceeds u64 framing");
        for (idx, byte) in bytes.iter().copied().enumerate() {
            let lane = idx & 3;
            self.lanes[lane] ^= u64::from(byte);
            self.lanes[lane] = self.lanes[lane].wrapping_mul(0x100000001b3);
            self.lanes[lane] ^= self.lanes[(lane + 1) & 3].rotate_left(13);
        }
        for lane in 0..4 {
            self.lanes[lane] ^= byte_len.rotate_left((lane * 11) as u32);
            self.lanes[lane] = self.lanes[lane]
                .rotate_left(17)
                .wrapping_mul(0x9e3779b185ebca87);
        }
    }

    fn finish(mut self) -> [u8; 32] {
        for round in 0..8 {
            let a = self.lanes[round & 3];
            let b = self.lanes[(round + 1) & 3];
            self.lanes[round & 3] = a.rotate_left(29) ^ b.wrapping_mul(0xd6e8feb86659fd93);
        }

        let mut out = [0u8; 32];
        for (idx, lane) in self.lanes.iter().enumerate() {
            out[idx * 8..(idx + 1) * 8].copy_from_slice(&lane.to_le_bytes());
        }
        out
    }
}

pub(crate) fn write_u8_stable(out: &mut Vec<u8>, value: u8) {
    out.push(value);
}

pub(crate) fn write_u32_stable(out: &mut Vec<u8>, value: u32) {
    out.extend_from_slice(&value.to_le_bytes());
}

pub(crate) fn write_u64_stable(out: &mut Vec<u8>, value: u64) {
    out.extend_from_slice(&value.to_le_bytes());
}

pub(crate) fn write_len_stable(out: &mut Vec<u8>, value: usize) {
    write_u64_stable(
        out,
        u64::try_from(value).expect("identity length exceeds canonical u64 framing"),
    );
}

fn write_f64_stable(out: &mut Vec<u8>, value: f64) {
    out.extend_from_slice(&value.to_bits().to_le_bytes());
}

pub(crate) fn write_str_stable(out: &mut Vec<u8>, value: &str) {
    write_len_stable(out, value.len());
    out.extend_from_slice(value.as_bytes());
}

fn write_bytes_stable(out: &mut Vec<u8>, value: &[u8]) {
    write_len_stable(out, value.len());
    out.extend_from_slice(value);
}

pub(crate) fn write_digest_stable(out: &mut Vec<u8>, digest: &ProofDigest) {
    write_u8_stable(
        out,
        match digest.algorithm {
            ProofDigestAlgorithm::Sha256 => 0,
            ProofDigestAlgorithm::TrustIrStableV1 => 1,
        },
    );
    out.extend_from_slice(&digest.bytes);
}

/// Canonical stable encoding of an obligation's optional embedded source
/// identity. This is shared by every proof-claim digest and diff fingerprint;
/// changing it requires coordinated domain bumps at all call sites.
pub(crate) fn write_proof_obligation_source_identity_stable(
    out: &mut Vec<u8>,
    source: Option<&ProofObligationSourceIdentity>,
) {
    let Some(source) = source else {
        write_u8_stable(out, 0);
        return;
    };
    write_u8_stable(out, 1);
    write_str_stable(out, &source.source_id);
    write_str_stable(out, &source.assertion_id);
    match source.range {
        None => write_u8_stable(out, 0),
        Some(range) => {
            write_u8_stable(out, 1);
            write_u32_stable(out, range.file);
            write_u32_stable(out, range.start_line);
            write_u32_stable(out, range.start_col);
            write_u32_stable(out, range.end_line);
            write_u32_stable(out, range.end_col);
        }
    }
    match &source.public {
        None => write_u8_stable(out, 0),
        Some(public) => {
            write_u8_stable(out, 1);
            write_str_stable(out, &public.obligation_id);
            write_digest_stable(out, &public.semantic_digest);
        }
    }
}

fn write_proof_evidence_stable(out: &mut Vec<u8>, evidence: &ProofEvidence) {
    match evidence {
        ProofEvidence::SmtProof(data) => {
            write_u8_stable(out, 0);
            write_bytes_stable(out, data);
        }
        ProofEvidence::LeanProof(term) => {
            write_u8_stable(out, 1);
            write_str_stable(out, term);
        }
        ProofEvidence::KaniHarness(name) => {
            write_u8_stable(out, 2);
            write_str_stable(out, name);
        }
        ProofEvidence::GammaCrownBound {
            epsilon,
            verified_layers,
        } => {
            write_u8_stable(out, 3);
            write_f64_stable(out, *epsilon);
            write_u32_stable(out, *verified_layers);
        }
        ProofEvidence::TranslationValidation {
            rule_name,
            smt_hash,
        } => {
            write_u8_stable(out, 4);
            write_str_stable(out, rule_name);
            out.extend_from_slice(smt_hash);
        }
        ProofEvidence::Trusted(reason) => {
            write_u8_stable(out, 5);
            write_str_stable(out, reason);
        }
        ProofEvidence::InheritedFromCallee { callee, obligation } => {
            write_u8_stable(out, 6);
            write_u32_stable(out, callee.index());
            write_u32_stable(out, obligation.index());
        }
        ProofEvidence::CleanCic {
            term,
            context,
            lineage,
            kernel_recheck,
        } => {
            write_u8_stable(out, 7);
            write_bytes_stable(out, term);
            write_bytes_stable(out, context);
            write_digest_stable(out, lineage);
            match kernel_recheck {
                None => write_u8_stable(out, 0),
                Some(recheck) => {
                    write_u8_stable(out, 1);
                    write_str_stable(out, &recheck.module);
                    write_len_stable(out, recheck.theorems.len());
                    for thm in &recheck.theorems {
                        write_str_stable(out, thm);
                    }
                    write_str_stable(out, &recheck.anchor);
                    write_len_stable(out, recheck.allowed_axioms.len());
                    for ax in &recheck.allowed_axioms {
                        write_str_stable(out, ax);
                    }
                }
            }
        }
    }
}
