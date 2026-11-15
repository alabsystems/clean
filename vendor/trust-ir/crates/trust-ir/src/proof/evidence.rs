// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Proof evidence and digests: [`ProofEvidence`], [`ProofCertificate`],
//! [`ProofCertificateRef`], the [`ProofDigest`] / [`ProofDigestAlgorithm`]
//! pair and its deterministic digest infrastructure, plus the CleanCic
//! lineage helpers ([`clean_cic_lineage_digest`],
//! [`obligation_has_matching_clean_cic`]).

use super::obligations::{
    ObligationKind, ObligationSite, ProofObligation, ProofObligationSourceIdentity,
};
use crate::value::{FuncId, ProofId};
use sha2::{Digest, Sha256};

mod observed;

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
///    noncanonical foundations, missing values, and dependency cycles.
///
/// Optional micro diagnostics do not supply or fence production authority.
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
    /// Fully-qualified kernel equation/theorem identities whose proof TERM is
    /// re-checked in-process (e.g. `"NNVerify.farkas_combine_2_le_bound"`). The
    /// existing theorem-library and backend-TV anchors require each citation
    /// to be a `Declaration::Theorem` in their checked environment. The distinct
    /// [`KERNEL_ANCHOR_CLEAN_BACKEND_SOURCE_CALLS_V1`] instead derives the sole
    /// equation identity from the actual function and checks its payload proof
    /// against the reconstructed closed statement with ONE checker shared by
    /// the family, then applies the same rooted authority audit directly to
    /// that proof. It inserts no extra declaration or unchecked authority.
    /// All citations must pass their anchor's exact statement/obligation binding
    /// before they carry certification authority.
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
    /// What this certificate is BOUND to (roadmap WS1.12a, findings F-007 /
    /// F-005 / F-008): the kernel environment and the exact statement the
    /// validator re-derives, the minting module of a relocated certificate,
    /// the source definition (carrier only until WS1.13), and the ordered
    /// callee link symbols a `clean_backend_tv` statement quantifies over or a
    /// source-call-family statement specializes to checked source definitions.
    ///
    /// `None` means UNBOUND — the pre-binding meaning of every existing
    /// certificate, unchanged. A validator under
    /// `ValidationConfig::require_bound_certificates` refuses an unbound
    /// `Certified` row; the default lanes keep admitting it, exactly as before.
    /// A present binding is never taken on faith: every field a validator can
    /// recompute it recomputes and compares (see [`CertificateBinding`]).
    ///
    /// Sole trailing skipped field of this struct, so positional MessagePack
    /// stays satisfied and every existing serde golden keeps its bytes. Boxed
    /// so the binding's five fields do not widen every `ProofEvidence` (serde
    /// sees through the box; the wire shape is the struct's).
    ///
    /// # Wire status
    ///
    /// Binary v61 (`binary::CERTIFICATE_BINDING_FORMAT_VERSION`, reserved
    /// 07fb5515 — the carrier WS1.12a deferred) writes it as a presence byte
    /// after the directive's axiom list, then the binding's fields in struct
    /// order. The writer selects v61 only for a module that carries a binding,
    /// so an all-unbound module keeps its older bytes exactly; a pre-v61 blob
    /// decodes every directive UNBOUND; an explicit v38 projection refuses a
    /// bound module (`CertificateBindingRequiresV61`) — no binary path narrows
    /// a binding to `None`. JSON / MessagePack carry it as the serde field.
    /// Text loses the whole directive and records it
    /// (`TextLoss::KernelRecheck`).
    #[cfg_attr(
        feature = "serde",
        serde(default, skip_serializing_if = "Option::is_none")
    )]
    pub binding: Option<Box<CertificateBinding>>,
}

/// The exact things a kernel-re-checked certificate is bound to (roadmap
/// WS1.12a). Every field is either RECOMPUTED by the validator and compared,
/// or checked against something the validator holds:
///
/// * [`Self::environment_digest`] — [`kernel_environment_digest`] of the
///   anchor environment the validator itself builds (prelude plus the
///   anchor's own definitional vocabulary, BEFORE the certificate's theorem
///   is declared). Closes finding F-007: a certificate now names the kernel
///   closure it was checked in, and re-checks only in an equal one.
/// * [`Self::statement_digest`] — [`clean_cic_statement_digest`] of the
///   statement the validator derives (TV: the `∀`-equation; contract: the
///   grounded goal). The producer never chooses the statement; a mismatch is
///   a refusal.
/// * [`Self::origin_module`] — where a RELOCATED certificate was minted, as
///   that module's identity digest; `None` for a certificate minted in the
///   module that carries it. Must name a declared import row; the linked walk
///   requires that row to be authenticated.
/// * [`Self::source`] — the source definition the comparand was derived from.
///   CHECKED only against a carried island ([`Self::environment`], roadmap
///   WS1.13, finding F-008): on a `clean_backend_tv` certificate that carries
///   an island, the re-check requires the comparand to be definitionally
///   equal to the value of `source.decl` in the island environment. A
///   `source` with NO island names nothing the validator can check: it stays
///   the WS1.12a carrier (preserved and digested, never read as source
///   binding), and a consumer that needs the binding refuses island-free
///   certificates with `ValidationConfig::with_source_bound_certificates`
///   (`trust_ir_build`).
/// * [`Self::environment`] — the island of declarations the certificate was
///   checked in ([`IslandEnvironment`], WS1.13): the canonical,
///   resource-bounded encoding of a Clean declaration closure, installed into
///   the anchor environment by the kernel (every declaration re-checked on
///   insertion) before the certificate's own judgment. REQUIRED by the
///   `clean_island` anchor, optional on a `clean_backend_tv` certificate
///   (where it source-binds the comparand), refused on every other anchor.
/// * [`Self::callees`] — for a `clean_backend_tv` certificate, the callee LINK
///   SYMBOLS the statement quantifies over, in the validator's canonical
///   (name-sorted) order; EMPTY for every other anchor. The validator requires
///   it to equal the callee list re-derived from the body, and every
///   `InheritedFromCallee` row to name one of them — which closes the WS1.4
///   residual (a CONSISTENT retarget of call and row to another certified
///   callee of the same arity and rank).
///
/// [`kernel_environment_digest`]: crate::proof::kernel_environment_digest
/// [`clean_cic_statement_digest`]: crate::proof::clean_cic_statement_digest
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct CertificateBinding {
    /// Digest of the kernel environment the certificate was checked in
    /// (domain `trust_ir.clean_cic.environment.v1`).
    pub environment_digest: ProofDigest,
    /// Digest of the statement the certificate proves (domain
    /// `trust_ir.clean_cic.statement.v1`).
    pub statement_digest: ProofDigest,
    /// Identity digest of the module a relocated certificate was minted in.
    pub origin_module: Option<ProofDigest>,
    /// The source definition behind the comparand, checked against
    /// [`Self::environment`] (WS1.13).
    pub source: Option<SourceDefinitionRef>,
    /// Ordered callee link symbols of a `clean_backend_tv` statement.
    pub callees: Vec<String>,
    /// The island of declarations the certificate was checked in (roadmap
    /// WS1.13; finding F-012, and the check half of F-008). `None` means NO
    /// ISLAND — every certificate minted before WS1.13 keeps its meaning.
    ///
    /// Sole trailing skipped field of this struct, so positional MessagePack
    /// stays satisfied and every existing bound certificate keeps its serde
    /// bytes; it enters [`Self::write_stable`] only when present, so every
    /// existing v8 lineage and evidence digest keeps its bytes too. Binary
    /// v61 (`binary::CERTIFICATE_BINDING_FORMAT_VERSION`) carries it as the
    /// binding's last field: a presence byte, the declaration bytes
    /// length-framed and OPAQUE (never decoded by the reader), then the
    /// digest it RECORDS (never recomputed by the reader, so a forged digest
    /// reaches the validator that refuses it).
    #[cfg_attr(
        feature = "serde",
        serde(default, skip_serializing_if = "Option::is_none")
    )]
    pub environment: Option<IslandEnvironment>,
}

/// An ISLAND ENVIRONMENT (roadmap WS1.13): the Clean declarations a
/// kernel-checked certificate needs beyond its anchor's fixed vocabulary —
/// a user theorem and the definitions it is about, or the source definition
/// a translation-validation comparand must equal.
///
/// `declarations` is OPAQUE to trust-ir: the canonical, resource-bounded
/// `clean-kernel` encoding of the island's declaration closure
/// (`trust_ir::proof::encode_island_declarations_v1`, feature `clean-expr`),
/// decoded only by the anchor's own bounded decoder and re-checked by the
/// Clean kernel declaration by declaration, exactly like a `CleanCic`
/// payload's `term` / `context` (`docs/SPEC_RATIFICATIONS.md` §8, which names
/// this field as an admitted opaque payload). No `Π` / `λ` / `Prop` enters
/// the IR type system through it.
///
/// `digest` is [`island_declarations_digest`] of `declarations` (domain
/// `trust_ir.clean_cic.island.v1`); a validator recomputes it from the bytes
/// BEFORE decoding anything and refuses a mismatch. It is the island's
/// identity: two certificates are checked in the same island exactly when
/// their digests are equal, which is how a theorem about island constant `c`
/// is bridged to the emitted function whose translation-validation
/// certificate is source-bound to `c`.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct IslandEnvironment {
    /// Canonical encoding of the island's declaration closure (opaque here).
    pub declarations: Vec<u8>,
    /// [`island_declarations_digest`] of [`Self::declarations`].
    pub digest: ProofDigest,
}

/// Digest domain of [`island_declarations_digest`].
pub const ISLAND_DECLARATIONS_DIGEST_V1_DOMAIN: &str = "trust_ir.clean_cic.island.v1";

/// The identity of an island's declaration bytes —
/// [`IslandEnvironment::digest`]: SHA-256 under `trust_ir.clean_cic.island.v1`
/// over the canonical encoding. The encoding is canonical (a decoder refuses
/// any byte string that does not re-encode to itself), so this is a content
/// identity of the declaration list.
#[must_use]
pub fn island_declarations_digest(declarations: &[u8]) -> ProofDigest {
    ProofDigest::sha256_domain(ISLAND_DECLARATIONS_DIGEST_V1_DOMAIN, declarations)
}

impl IslandEnvironment {
    /// An island over `declarations`, with its digest computed here.
    #[must_use]
    pub fn new(declarations: Vec<u8>) -> Self {
        let digest = island_declarations_digest(&declarations);
        Self {
            declarations,
            digest,
        }
    }
}

/// The source definition a translation-validation comparand was derived from
/// (the certificate-binding half of the Lean-home `source_digest` row): the
/// declaration's name in the producing language and the digest of its source
/// closure. CHECKED (WS1.13) only against a carried [`IslandEnvironment`]:
/// the comparand must be definitionally equal to the value of `decl` in the
/// island. `closure_digest` names the source text the island was elaborated
/// from; it is carried and digested, and no validator can re-derive it (the
/// source text is not in the module).
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct SourceDefinitionRef {
    /// The declaration's fully-qualified name in the producing language.
    pub decl: String,
    /// Digest of the declaration's source closure.
    pub closure_digest: ProofDigest,
}

impl CertificateBinding {
    /// A binding for a certificate minted IN the module that carries it, with
    /// no source reference and no callees: exactly the two digests every
    /// binding must carry.
    #[must_use]
    pub fn new(environment_digest: ProofDigest, statement_digest: ProofDigest) -> Self {
        Self {
            environment_digest,
            statement_digest,
            origin_module: None,
            source: None,
            callees: Vec::new(),
            environment: None,
        }
    }

    /// Stable, presence-prefixed preimage of this binding — the "binding
    /// bytes" the v8 lineage and the evidence digest fold in.
    pub(crate) fn write_stable(&self, out: &mut Vec<u8>) {
        write_digest_stable(out, &self.environment_digest);
        write_digest_stable(out, &self.statement_digest);
        match &self.origin_module {
            None => write_u8_stable(out, 0),
            Some(digest) => {
                write_u8_stable(out, 1);
                write_digest_stable(out, digest);
            }
        }
        match &self.source {
            None => write_u8_stable(out, 0),
            Some(source) => {
                write_u8_stable(out, 1);
                write_str_stable(out, &source.decl);
                write_digest_stable(out, &source.closure_digest);
            }
        }
        write_len_stable(out, self.callees.len());
        for callee in &self.callees {
            write_str_stable(out, callee);
        }
        // WS1.13: the island enters the binding bytes ONLY when present, so
        // every binding minted before it keeps its exact preimage (and with
        // it every v8 lineage and evidence digest). No ambiguity: every
        // field above is length-framed or fixed-width, and the binding bytes
        // are the TAIL of both preimages that fold them in, so an island-free
        // preimage can never be the prefix of an island-carrying one.
        if let Some(island) = &self.environment {
            write_u8_stable(out, 1);
            write_bytes_stable(out, &island.declarations);
            write_digest_stable(out, &island.digest);
        }
    }
}

/// In-process kernel anchor for the **contract** path (roadmap WS1.12a,
/// DECIDE 1): a `CleanCic` certificate whose `term` is a proof of the
/// obligation's own grounded contract goal
/// ([`crate::clean_expr_lowering::contract::contract_goal_in`]), checked
/// against the kernel-owned ordinary prelude. Before this anchor existed the
/// contract path was the ONE directive-less arm of the re-checker, so a
/// contract certificate could carry no [`CertificateBinding`]; a directive
/// citing this anchor names the environment and statement it was checked in.
/// The directive cites NO theorem and admits NO axiom (`theorems` and
/// `allowed_axioms` must be empty): the term is checked directly against the
/// re-grounded goal, never against a library statement. A directive-less
/// contract certificate keeps its pre-binding meaning (admitted, UNBOUND).
pub const KERNEL_ANCHOR_TRUST_IR_CONTRACT: &str = "trust_ir_contract";

/// The canonical `module` a [`KERNEL_ANCHOR_TRUST_IR_CONTRACT`] directive must
/// carry.
pub const KERNEL_ANCHOR_TRUST_IR_CONTRACT_MODULE: &str = "TrustIr.Contract";

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
/// emitted function in the kernel-TV fragment, the equation
///
/// ```text
/// CleanTV.<fn>.denotes : ∀ (x1 : S1) … (xn : Sn), @Eq R ⟦emitted fn⟧ ⟦original defn⟧
/// ```
///
/// over the shared `Nat`-mod-`2^w` denotation vocabulary (trust-ir's ratified
/// wrapping semantics, `docs/ub-numerics-policy.md`), with every value at a
/// SORT: a `U8..U64` / `I8..I64` machine integer is a `Nat` bit pattern
/// (signed = two's complement over `Nat` mod `2^w`, stated at the signed
/// carrier alias `CleanTV.Int<w> : Type := Nat` so the statement binds the
/// carrier label too), a `Bool` is the kernel
/// `Bool`, a fieldless-enum param is its tag. The fragment (roadmap WS1.15,
/// S1..S5; the table is on the re-checker module in `trust_ir_build::validate`
/// and in `TRUST.md` item 6): `Const`, `Add`/`Sub`/`Mul`, `And`/`Or`/`Xor`
/// (integer and Bool), `UDiv`/`URem` with a provably nonzero divisor,
/// `Shl`/`LShr` by a provably in-range amount, every `ICmp` (signed through
/// the `2^(w-1)` bias, `Ne` through `Bool.not`), `Select`, `ZExt`/`Trunc`,
/// the enum tag-lane `ExtractField`, direct calls (Fragment-3b), the
/// closed-address heap (Fragment-4), and — as the entry terminator — a
/// `Return`, a `CondBr` diamond, or a `Switch` over return arms. The re-checker
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
/// (strict rooted CIC authority audit). Only an
/// [`ObligationKind::TranslationValidation`] obligation may cite this anchor;
/// translation validation also has a distinct, formula-bound lowering-
/// resolution anchor. Any cross-domain use, unknown anchor, or this anchor
/// without the `clean-tv-anchor` feature is rejected fail-closed.
pub const KERNEL_ANCHOR_CLEAN_BACKEND_TV: &str = "clean_backend_tv";

/// Closed, source-bound call-family TV. Every actual callee is a defined IR
/// body bound to a definition in the same checked island. Older readers refuse
/// this distinct anchor; the parametric/no-callee anchor keeps its meaning.
pub const KERNEL_ANCHOR_CLEAN_BACKEND_SOURCE_CALLS_V1: &str = "clean_backend_source_calls_v1";

/// Universal readonly-effect call-family TV in the canonical ByteV1 model.
/// This distinct anchor never upgrades a pointwise source/word coincidence.
/// It rederives actual C(Ptr)->U64 LOAD8/call bodies and checks their complete
/// context/memory/address -> memory-result functions against island Definitions.
pub const KERNEL_ANCHOR_CLEAN_BACKEND_READONLY_CALLS_V1: &str = "clean_backend_readonly_calls_v1";

/// The closed source-family anchors; each has its own rederived profile.
pub fn is_clean_source_call_anchor(anchor: &str) -> bool {
    matches!(
        anchor,
        KERNEL_ANCHOR_CLEAN_BACKEND_SOURCE_CALLS_V1 | KERNEL_ANCHOR_CLEAN_BACKEND_READONLY_CALLS_V1
    )
}

/// In-process kernel anchor for a **user theorem shipped with its island**
/// (roadmap WS1.13, finding F-012): the one anchor whose environment is not
/// fixed by the validator but carried by the certificate, as an
/// [`IslandEnvironment`] inside its [`CertificateBinding`].
///
/// The re-checker (`trust_ir_build::validate`, feature `clean-tv-anchor`)
/// recomputes the island digest from the bytes, decodes them with the
/// island's own bounded canonical decoder, refuses a declaration that
/// redeclares a name the anchor environment (or the island) already has, one
/// under a validator-owned theorem root (`CleanTV`, `NNVerify`, …: the kernel
/// witness is keyed by theorem name) and any axiom, installs every declaration into the `clean_backend_tv` anchor
/// environment with the kernel's checked `add_decl` (so the bytes are
/// untrusted), re-checks the cited theorem through the strict rooted audit,
/// grounds the obligation's first-order `ProofFormula`
/// into a kernel statement `G` with a pinned statement grounder, and requires
/// the theorem's type to be definitionally equal to `G`. Every function
/// symbol of `G` must be an island constant whose EMITTED body is
/// kernel-TV-certified in the same module by a `clean_backend_tv`
/// certificate source-bound to that constant in the SAME island, so the
/// theorem is about the code, not only about the island.
///
/// Slice 1: only an `ObligationKind::Custom { namespace: "lean.theorem", .. }`
/// row may cite it, stating a closed equation over island constants and
/// `Nat` / `Bool` literals. Contract clauses over IR places are slice 2 and
/// stay refused. Any other kind citing it, or a `lean.theorem` row citing any
/// other anchor, is refused.
pub const KERNEL_ANCHOR_CLEAN_ISLAND: &str = "clean_island";

/// The canonical `module` a [`KERNEL_ANCHOR_CLEAN_ISLAND`] directive must
/// carry.
pub const KERNEL_ANCHOR_CLEAN_ISLAND_MODULE: &str = "Clean.Island";

/// The `ObligationKind::Custom` namespace of a user theorem certified through
/// [`KERNEL_ANCHOR_CLEAN_ISLAND`] (roadmap WS1.13, decision gate DG-31):
/// `Custom { namespace: "lean.theorem", name: <the theorem's kernel name> }`.
/// Owned by Clean (the producer of the island), with trust-ir's
/// `ADMITTED_OBLIGATION_NAMESPACES` as the pin of record. The anchor keys on
/// it in both directions: only a row in this namespace may cite the island
/// anchor, and a row in this namespace may be `Certified` only through it.
pub const LEAN_THEOREM_OBLIGATION_NAMESPACE: &str = "lean.theorem";

/// Whether `kind` is a [`LEAN_THEOREM_OBLIGATION_NAMESPACE`] row (byte-exact).
#[must_use]
pub fn is_lean_theorem_kind(kind: &ObligationKind) -> bool {
    matches!(kind, ObligationKind::Custom { namespace, .. } if namespace == LEAN_THEOREM_OBLIGATION_NAMESPACE)
}

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
        /// The callee function whose proof is being composed in. ALWAYS a
        /// module-local id, in both the local and the cross-crate form: for an
        /// import it is this module's own bodyless declaration of the callee,
        /// so the call edge and the inherited proof name one entity.
        callee: FuncId,
        /// The callee-side obligation relied upon. ALWAYS a module-local
        /// [`ProofId`]; see `external` for what "relied upon" means in the
        /// cross-crate form.
        obligation: ProofId,
        /// Cross-crate authority for this inheritance (v41). `None` is the
        /// pre-v41 meaning, unchanged and byte-identical on the wire.
        ///
        /// # Why the local fields were not enough
        ///
        /// `callee`/`obligation` are two module-local `u32`s and the validator
        /// requires both to resolve HERE. That is exactly right for a
        /// same-module inheritance and makes a cross-crate one UNSPELLABLE: a
        /// separately compiled callee's obligation does not exist in this
        /// module's arena, so a producer had no way to say "this is discharged
        /// because crate X's `foo` discharged its obligation 7".
        ///
        /// # What `Some` means
        ///
        /// The claim moves to the imported module: [`ExternRef::module`] names
        /// the [`crate::ModuleImport`] (hence the authenticating digest),
        /// [`ExternRef::symbol`] the callee's link-time symbol there, and
        /// [`ExternRef::obligation`] the obligation in THAT module's id space.
        /// The local `obligation` field then names this module's own
        /// restatement of the inherited claim — the obligation this certificate
        /// discharges on this side of the boundary — and carries NO authority
        /// of its own.
        ///
        /// # Fail-closed by default
        ///
        /// A validator whose rule is "the inherited `obligation` must be
        /// discharged by ground evidence in THIS module" therefore REJECTS
        /// every `Some` until it grows an import-authentication rule, which is
        /// the correct default: nothing may be inherited across an edge whose
        /// far side has not been authenticated against
        /// [`crate::ModuleImport::digest`].
        ///
        /// Encoded at a NEW binary tag (8) rather than by widening tag 6, so a
        /// pre-v41 blob's two-`u32` payload keeps its exact byte layout and
        /// decodes to `None`.
        #[cfg_attr(feature = "serde", serde(default))]
        external: Option<crate::ExternRef>,
    },
    /// A kernel-checkable CIC evidence payload — the de Bruijn "Certified"
    /// tier. The exact `term`/`context` wire schema is anchor-specific and must
    /// be decoded with that schema's canonical, bounded decoder. A certifying
    /// validator reconstructs the claim from the obligation/module and checks
    /// the decoded evidence against it; non-empty opaque bytes are never proof.
    /// `lineage` is identity/replay binding only, not proof authority.
    /// Must-refuse corpus row `refuse/certified_with_empty_kernel_term`: a
    /// `Certified` row whose `term` is empty, lineage matching, is refused as
    /// `CertifiedWithoutCleanCic`.
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

variant_shape! {
    /// The payload-free shape of a [`ProofEvidence`]: its variant, as a `Copy`
    /// value. The evidence→kind admission table (WS1.8 rule (d),
    /// `trust_ir_laws::evidence_admits_kind`) is stated over this type and
    /// [`super::ObligationKindShape`]; see `variant_shape!` for why the
    /// projection cannot drift.
    pub enum ProofEvidenceShape for ProofEvidence {
        SmtProof,
        LeanProof,
        KaniHarness,
        GammaCrownBound,
        TranslationValidation,
        Trusted,
        InheritedFromCallee,
        CleanCic,
    }
}

/// How much of the input / behavior space one discharge actually covered (v41).
///
/// Mirrors the coverage axis of trust's five-axis grade record, NOT the retired
/// flat `AssuranceLevel`. Defined here rather than imported because `trust-ir`
/// has zero required dependencies.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[non_exhaustive]
pub enum CoverageBound {
    /// All inputs; unbounded behavior.
    Unbounded,
    /// Bounded exploration (loop unwinding / path depth) up to `depth`.
    UnwindBounded { depth: u64 },
    /// A finite model instance of size `size`.
    ModelBounded { size: u64 },
    /// The producing pipeline recorded no coverage bound. NEVER equivalent to
    /// [`CoverageBound::Unbounded`] — an import must not gain unbounded
    /// standing by omission.
    Unrecorded,
}

/// A [`CoverageBound`] PROJECTED from a specific evidence bundle, carrying the
/// identity of what it was projected from (v41).
///
/// # NON-AUTHORITATIVE
///
/// This row establishes NOTHING. Coverage is a verdict the CONSUMER derives
/// from evidence it re-checks itself
/// (`trust_ir_build::coverage_establishment_report`): a certificate the
/// consumer's own kernel replayed, of a classified claim family (basis K), or a
/// solver result cited from a sealed
/// [`NativeCoverageAttestation`](crate::request::NativeCoverageAttestation)
/// and re-verified by a
/// [`NativeCoverageResultReplay`](crate::request::NativeCoverageResultReplay)
/// (basis R). Producers emit `None`. A consumer reads a `Some` row only to
/// REFUSE the bundle when the row claims more than the bound derived for THAT
/// certificate — basis K; a basis-R result is about the obligation and vouches
/// for no certificate, so it never supports a certificate's row — a producer
/// that over-states coverage is lying about something it cannot establish —
/// and otherwise ignores it.
///
/// Why the row could not stay the source: `request_digest` cites a request
/// whose replay transcript binds the module digest, and the module digest
/// covers this row, so a row citing a module-bound request has no fixed point
/// (row → module digest → transcript → request digest → row). The attestation
/// lives outside every digest instead. The wire field (v41) is kept so old
/// blobs still read.
///
/// Without `request_digest` this row would be a SECOND source of truth: a
/// consumer could not tell a faithful projection from a producer's bare
/// assertion. With it, the legacy rule (`trust_ir_build::coverage_assurance_report`,
/// deprecated) re-derives the bound from the request's MODE alone, which is
/// false provenance: a request is not a result.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct CoverageAssurance {
    /// The projected bound.
    pub bound: CoverageBound,
    /// The evidence bundle's request digest, so the projection is checkable.
    pub request_digest: ProofDigest,
}

#[derive(Debug, Clone, PartialEq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct ProofCertificate {
    pub obligation: ProofId,
    pub prover: String,
    pub evidence: ProofEvidence,
    /// Coverage this discharge actually achieved, projected from the native
    /// evidence bundle (v41).
    ///
    /// **NON-AUTHORITATIVE** (see [`CoverageAssurance`]): producers emit
    /// `None`, and a consumer derives coverage from evidence it re-checks
    /// (`trust_ir_build::coverage_establishment_report`). A `Some` row that
    /// claims more than this certificate's own derived (basis K) bound
    /// refuses the bundle; any other `Some` row is ignored. It is outside [`ProofCertificate::lineage_ref`], so a
    /// certificate's identity does not move when the row does.
    ///
    /// `None` = NOT RECORDED. A fail-closed consumer must treat that as UNKNOWN
    /// coverage, never as [`CoverageBound::Unbounded`] — the v34 `site = None`
    /// precedent. The must-refuse corpus cannot express this
    /// (`refuse/coverage_assurance_none_is_unknown`): a certificate with no
    /// assurance is well-formed and must be accepted; the rule binds the
    /// consumer's reading of it. This exists because a module separated from its
    /// `NativeVerificationBundle` otherwise carries no record of whether a
    /// discharge was a depth-1 bounded check or an unbounded proof.
    ///
    /// Sole trailing skipped field of this struct, so positional MessagePack is
    /// satisfied without flipping any earlier field.
    #[cfg_attr(
        feature = "serde",
        serde(default, skip_serializing_if = "Option::is_none")
    )]
    pub assurance: Option<CoverageAssurance>,
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

/// Exact-length failure for an incremental domain-separated SHA-256 identity.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ProofDigestStreamError {
    /// A chunk would make the stream longer than its declared payload.
    PayloadTooLong {
        /// Exact payload length declared when the stream was constructed.
        declared: u64,
        /// Saturating lower bound on the attempted total length.
        attempted_at_least: u64,
    },
    /// Finalization was requested before the declared payload was complete.
    PayloadIncomplete {
        /// Exact payload length declared when the stream was constructed.
        declared: u64,
        /// Exact number of bytes accepted by the stream.
        written: u64,
    },
}

impl core::fmt::Display for ProofDigestStreamError {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::PayloadTooLong {
                declared,
                attempted_at_least,
            } => write!(
                formatter,
                "domain-separated digest declared {declared} payload bytes but received at least {attempted_at_least}"
            ),
            Self::PayloadIncomplete { declared, written } => write!(
                formatter,
                "domain-separated digest declared {declared} payload bytes but received {written}"
            ),
        }
    }
}

impl std::error::Error for ProofDigestStreamError {}

/// Move-only incremental form of [`ProofDigest::sha256_domain`].
///
/// The caller declares the exact payload length once, then supplies any number
/// of borrowed chunks without concatenating them. Overrun and incomplete
/// finalization fail closed, and an overrun does not mutate the accepted prefix.
pub struct ProofDigestSha256DomainStream {
    hasher: Sha256,
    declared_payload_len: u64,
    written: u64,
}

impl core::fmt::Debug for ProofDigestSha256DomainStream {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        formatter
            .debug_struct("ProofDigestSha256DomainStream")
            .field("declared_payload_len", &self.declared_payload_len)
            .field("written", &self.written)
            .finish_non_exhaustive()
    }
}

impl ProofDigestSha256DomainStream {
    /// Append one exact borrowed payload chunk.
    pub fn update(&mut self, chunk: &[u8]) -> Result<(), ProofDigestStreamError> {
        let chunk_len = match u64::try_from(chunk.len()) {
            Ok(chunk_len) => chunk_len,
            Err(_) => {
                return Err(ProofDigestStreamError::PayloadTooLong {
                    declared: self.declared_payload_len,
                    attempted_at_least: u64::MAX,
                });
            }
        };
        let attempted_at_least = match self.written.checked_add(chunk_len) {
            Some(attempted) => attempted,
            None => {
                return Err(ProofDigestStreamError::PayloadTooLong {
                    declared: self.declared_payload_len,
                    attempted_at_least: u64::MAX,
                });
            }
        };
        if attempted_at_least > self.declared_payload_len {
            return Err(ProofDigestStreamError::PayloadTooLong {
                declared: self.declared_payload_len,
                attempted_at_least,
            });
        }
        self.hasher.update(chunk);
        self.written = attempted_at_least;
        Ok(())
    }

    /// Return the exact declared payload length.
    #[must_use]
    pub const fn declared_payload_len(&self) -> u64 {
        self.declared_payload_len
    }

    /// Return the number of payload bytes accepted so far.
    #[must_use]
    pub const fn written(&self) -> u64 {
        self.written
    }

    /// Finish the identity after exactly the declared payload was supplied.
    pub fn finish(self) -> Result<ProofDigest, ProofDigestStreamError> {
        if self.written != self.declared_payload_len {
            return Err(ProofDigestStreamError::PayloadIncomplete {
                declared: self.declared_payload_len,
                written: self.written,
            });
        }
        Ok(ProofDigest::sha256(self.hasher.finalize().into()))
    }
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

    /// Start an exact-length incremental form of [`Self::sha256_domain`].
    ///
    /// This writes the same versioned domain and payload-length framing up
    /// front. The returned stream accepts borrowed chunks and refuses to
    /// finalize unless their total length is exactly `payload_len`.
    pub fn sha256_domain_stream(domain: &str, payload_len: u64) -> ProofDigestSha256DomainStream {
        let domain_len = u64::try_from(domain.len())
            .expect("digest domain length exceeds canonical u64 framing");
        let mut hasher = Sha256::new();
        hasher.update(b"trust-ir.sha256-domain.v1\0");
        hasher.update(domain_len.to_be_bytes());
        hasher.update(domain.as_bytes());
        hasher.update(payload_len.to_be_bytes());
        ProofDigestSha256DomainStream {
            hasher,
            declared_payload_len: payload_len,
            written: 0,
        }
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
/// function scope, embedded source/public identity, and exact optional IR site
/// (function, block, and instruction index), and — under the `v6` domain, only
/// when present — the formula's v41 typed clause bindings, and — under the
/// `v7` domain, only when present — the v46 `spec` temporal backref (with the
/// bindings block after it) — i.e. the complete stored *claim*,
/// independent of the mutable [`ProofStatus`] label. The binding uses SHA-256
/// because lineage crosses an untrusted serialization boundary; the
/// non-cryptographic stable checksum is reserved for in-memory identity/caching
/// uses.
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
    write_obligation_kind_digest(&mut bytes, &obligation.kind);
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
    write_obligation_site_stable(&mut bytes, obligation.site);
    // v41 typed clause bindings are part of what the formula MEANS: without
    // them a certificate minted for `x: Int` replays against the same text with
    // `x: BitVec(64)`, a claim that can be false at `u64::MAX`. They get their
    // own domain, used only when bindings are present, so every lineage minted
    // for a binding-free formula keeps its exact `v5` digest. The two domains
    // cannot collide, and a certificate minted on either side of a bindings
    // change no longer matches.
    //
    // v46: the `spec` temporal backref — WHICH temporal property the
    // obligation discharges — is part of what it MEANS for the same reason:
    // two liveness rows differing only there state different properties, so
    // a certificate minted for one must not replay on the other. Same
    // presence-gated shape: a third domain, `v7`, used only when a backref is
    // present, so every v5/v6 lineage keeps its exact digest. Under v7 the
    // bindings block is always written (possibly empty) after the backref.
    let bindings = obligation
        .formula
        .as_ref()
        .map_or(&[][..], |formula| formula.bindings.as_slice());
    if let Some(spec) = &obligation.spec {
        write_u8_stable(&mut bytes, 1);
        write_str_stable(&mut bytes, &spec.machine);
        write_str_stable(&mut bytes, &spec.temporal);
        write_clause_bindings_stable(&mut bytes, bindings);
        return ProofDigest::sha256_domain("trust_ir.proof.clean_cic.lineage.v7", &bytes);
    }
    if bindings.is_empty() {
        return ProofDigest::sha256_domain("trust_ir.proof.clean_cic.lineage.v5", &bytes);
    }
    write_clause_bindings_stable(&mut bytes, bindings);
    ProofDigest::sha256_domain("trust_ir.proof.clean_cic.lineage.v6", &bytes)
}

/// Length-prefixed stable encoding of a formula's typed clause bindings, in
/// declaration order: name, sort, place.
fn write_clause_bindings_stable(
    out: &mut Vec<u8>,
    bindings: &[(String, super::obligations::ClauseBinding)],
) {
    write_len_stable(out, bindings.len());
    for (name, binding) in bindings {
        write_str_stable(out, name);
        write_clause_sort_stable(out, &binding.sort);
        write_clause_place_stable(out, &binding.place);
    }
}

/// The v8 CleanCic lineage (roadmap WS1.12b, DECIDE 4): the binding of a
/// certificate to its obligation keyed on CONTENT AND LINK SYMBOL, never on
/// the `ProofId` / `FuncId` indices the v5/v6/v7 digests fold in.
///
/// Domain `trust_ir.proof.clean_cic.lineage.v8` over: the kind, description,
/// formula WITH its typed bindings, source identity, the site as `(function
/// link symbol, block, instruction index)`, the owning function's link symbol,
/// the v46 `spec` temporal backref (machine and property names), and the
/// certificate's [`CertificateBinding`] bytes (presence-prefixed, so
/// an unbound certificate has a well-defined v8 lineage too). A merge that
/// renumbers obligations or functions therefore leaves a v8 lineage intact,
/// where a v5/v6/v7 lineage of the same certificate is refused — the control
/// pair the roadmap names. (v7 is WS4.14's index-keyed spec-backref lineage.)
///
/// `resolve` maps a function id to its link symbol (`Function.name`, unique
/// by `DuplicateFunctionSymbol`). `None` when the owning function or the
/// site's function does not resolve: a lineage that cannot be keyed is not
/// keyed, never keyed on a guess.
///
/// Because the id is gone, two obligations of one function with identical
/// content share a v8 lineage; `trust_ir_build`'s `DuplicateObligationContent`
/// refuses that on every row a v8-matched `CleanCic` certificate certifies, so
/// the mapping stays one-to-one within a function.
pub fn clean_cic_lineage_digest_v8(
    obligation: &ProofObligation,
    resolve: &dyn Fn(FuncId) -> Option<String>,
    binding: Option<&CertificateBinding>,
) -> Option<ProofDigest> {
    let mut bytes = clean_cic_lineage_content_v8(obligation, resolve)?;
    match binding {
        None => write_u8_stable(&mut bytes, 0),
        Some(binding) => {
            write_u8_stable(&mut bytes, 1);
            binding.write_stable(&mut bytes);
        }
    }
    Some(ProofDigest::sha256_domain(
        "trust_ir.proof.clean_cic.lineage.v8",
        &bytes,
    ))
}

/// The binding-free CONTENT half of the v8 lineage preimage — what
/// `DuplicateObligationContent` compares within a function. `None` exactly
/// when [`clean_cic_lineage_digest_v8`] is `None`.
pub fn clean_cic_lineage_content_v8(
    obligation: &ProofObligation,
    resolve: &dyn Fn(FuncId) -> Option<String>,
) -> Option<Vec<u8>> {
    let mut bytes = Vec::new();
    write_obligation_kind_digest(&mut bytes, &obligation.kind);
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
            write_clause_bindings_stable(&mut bytes, &formula.bindings);
        }
    }
    match obligation.function {
        None => write_u8_stable(&mut bytes, 0),
        Some(function) => {
            write_u8_stable(&mut bytes, 1);
            write_str_stable(&mut bytes, &resolve(function)?);
        }
    }
    write_proof_obligation_source_identity_stable(&mut bytes, obligation.source.as_ref());
    match obligation.site {
        None => write_u8_stable(&mut bytes, 0),
        Some(site) => {
            write_u8_stable(&mut bytes, 1);
            write_str_stable(&mut bytes, &resolve(site.function)?);
            write_u32_stable(&mut bytes, site.block.index());
            write_u32_stable(&mut bytes, site.inst_index);
        }
    }
    // The v46 `spec` temporal backref is part of what the obligation MEANS
    // (the reason the index-keyed digest grew its `v7` domain): two liveness
    // rows differing only there state different properties, so a v8
    // certificate minted for one must not replay on the other, and the two
    // are NOT duplicate content. Always presence-prefixed — v8 has no legacy
    // spelling to preserve. It is already a NAME pair, so it needs no resolver.
    match &obligation.spec {
        None => write_u8_stable(&mut bytes, 0),
        Some(spec) => {
            write_u8_stable(&mut bytes, 1);
            write_str_stable(&mut bytes, &spec.machine);
            write_str_stable(&mut bytes, &spec.temporal);
        }
    }
    Some(bytes)
}

/// Whether `evidence` is a `CleanCic` payload whose `lineage` binds it to
/// `obligation` under ANY accepted lineage: the index-keyed v5/v6/v7
/// ([`clean_cic_lineage_digest`]) or the symbol-keyed v8
/// ([`clean_cic_lineage_digest_v8`], computed with the certificate's own
/// binding). `resolve` is the link-symbol resolver the v8 form needs; a
/// lineage that cannot be keyed under v8 is compared under v5/v6/v7 only.
pub fn clean_cic_lineage_binds(
    obligation: &ProofObligation,
    evidence: &ProofEvidence,
    resolve: &dyn Fn(FuncId) -> Option<String>,
) -> bool {
    let ProofEvidence::CleanCic {
        lineage,
        kernel_recheck,
        ..
    } = evidence
    else {
        return false;
    };
    if *lineage == clean_cic_lineage_digest(obligation) {
        return true;
    }
    let binding = kernel_recheck
        .as_ref()
        .and_then(|recheck| recheck.binding.as_deref());
    clean_cic_lineage_digest_v8(obligation, resolve, binding).is_some_and(|v8| *lineage == v8)
}

/// The link-symbol resolver a v8 lineage needs, over `module`'s function
/// table (`Function.name`, unique by `DuplicateFunctionSymbol`; a duplicated
/// FUNCTION ID resolves to the first row, which the validator refuses on its
/// own as `DuplicateFunctionId`).
pub fn module_symbol_resolver(module: &crate::Module) -> impl Fn(FuncId) -> Option<String> + '_ {
    move |id| module.function_by_id(id).map(|f| f.name.clone())
}

/// Whether `evidence`'s lineage is the symbol-keyed v8 form for `obligation`
/// (and NOT merely the index-keyed one). What `DuplicateObligationContent`
/// scopes itself to.
pub fn clean_cic_lineage_is_v8(
    obligation: &ProofObligation,
    evidence: &ProofEvidence,
    resolve: &dyn Fn(FuncId) -> Option<String>,
) -> bool {
    let ProofEvidence::CleanCic {
        lineage,
        kernel_recheck,
        ..
    } = evidence
    else {
        return false;
    };
    let binding = kernel_recheck
        .as_ref()
        .and_then(|recheck| recheck.binding.as_deref());
    clean_cic_lineage_digest_v8(obligation, resolve, binding).is_some_and(|v8| *lineage == v8)
}

/// Content bytes + SHA-256 behind [`crate::Module::obligation_digest`] (v23,
/// WS4-M2 cert-cache key). See that method for the identity contract; this
/// helper owns the byte layout:
///
/// `domain || kind tag || description || formula(presence, schema, payload,
/// smtlib, sort) || source/public identity || site(presence, function index,
/// block index, instruction index) || resolved function content(presence,
/// name, canonical content, entry block index, summary(presence, requires,
/// ensures, params, decreases, effects))` — all via the `write_*_stable`
/// length-prefixed encoders,
/// hashed with the in-crate SHA-256. `entry` and `summary` are hashed explicitly
/// because the canonical text form carries neither (the text format has no
/// entry marker or summary syntax), yet both are proof-relevant content: `entry` decides execution
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
/// units that happen to carry the same human-readable claim. v5 adds the exact
/// optional IR site so a certificate cached for one check cannot be replayed at
/// another instruction carrying an otherwise identical claim. v6 adds the
/// summary's `decreases` measures, each clause's typed `bindings`, and
/// `ObligationKind::Custom`'s namespace and name — all three change what a
/// contract MEANS, so two clauses differing only in a bound name's arithmetic
/// domain must not share a cache slot. (Two development lines each claimed v5
/// for one of these; the merged preimage carries both, hence v6.) v7 (wire
/// v46) adds the obligation's `spec` temporal backref — WHICH temporal
/// property a `Liveness`/`TemporalSafety` row discharges — after the site,
/// for the same reason. v8 (wire v59, roadmap WS1.14) adds the owning
/// summary's `effects` frame after its `decreases`: which memory a call may
/// touch is part of what the contract means. `Function`'s `body_gate` and
/// `display_path` are deliberately EXCLUDED: a codegen license and a display
/// name grant nothing to a proof.
///
/// A `ClausePlace::Value(v)` binding — in the obligation's formula or in a
/// summary clause of the owning function — is written as the CANONICAL id of
/// `v` in that function (roadmap WS4.4 review, NEW-1 in the cache key): the
/// function content is its canonical text, in which `v` is densely renumbered,
/// so the binding must be renumbered by the same plan
/// ([`crate::canonicalize::FunctionCanonicalPlan::map_binding_value`], the
/// rewrite `format::into_canonical` performs). Until then the preimage held
/// the canonical body beside the RAW binding id, so two functions with one
/// canonical text whose raw `%9` named different values (a result in one, a
/// parameter in the other) shared a cache slot — a stale HIT, the direction
/// the identity contract rules out — while renumbering a function together
/// with its bindings moved the slot. No layout byte changes, and every row
/// without a `Value` binding in a non-canonical function keeps its exact
/// preimage, so the domain stays `v7`: no producer on trust, clean or
/// trust-cg `origin/main` mints a `Value` place (measured 2026-09-27), so no
/// persisted `v7` key carries one. An obligation with no resolved function
/// writes its bindings raw; the validator refuses a `Value` place there
/// (`InvalidObligationBinding`).
///
/// [`ProofStatus`]: super::obligations::ProofStatus
/// [`FunctionSummary::proved`]: crate::FunctionSummary::proved
#[cfg(feature = "fmt")]
pub(crate) fn obligation_content_digest(
    obligation: &ProofObligation,
    function_content: Option<(&crate::Function, &str)>,
) -> ProofDigest {
    let plan = function_content.and_then(|(func, _)| value_binding_plan(obligation, func));
    let plan = plan.as_ref();
    let mut bytes = Vec::new();
    write_obligation_kind_digest(&mut bytes, &obligation.kind);
    write_str_stable(&mut bytes, &obligation.description);
    match &obligation.formula {
        None => write_u8_stable(&mut bytes, 0),
        Some(formula) => {
            write_u8_stable(&mut bytes, 1);
            write_proof_formula_stable(&mut bytes, formula, plan);
        }
    }
    write_proof_obligation_source_identity_stable(&mut bytes, obligation.source.as_ref());
    write_obligation_site_stable(&mut bytes, obligation.site);
    // v7 (wire v46): the `spec` temporal backref — WHICH temporal property the
    // obligation discharges — changes what the obligation MEANS, so two rows
    // differing only here must not share a cache slot. Presence byte, then
    // machine and property names.
    match &obligation.spec {
        None => write_u8_stable(&mut bytes, 0),
        Some(spec) => {
            write_u8_stable(&mut bytes, 1);
            write_str_stable(&mut bytes, &spec.machine);
            write_str_stable(&mut bytes, &spec.temporal);
        }
    }
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
                        write_proof_formula_stable(&mut bytes, clause, plan);
                    }
                    write_len_stable(&mut bytes, summary.ensures.len());
                    for clause in &summary.ensures {
                        write_proof_formula_stable(&mut bytes, clause, plan);
                    }
                    write_len_stable(&mut bytes, summary.params.len());
                    for param in &summary.params {
                        write_str_stable(&mut bytes, param);
                    }
                    // v41: termination measures are part of the contract, so a
                    // changed `decreases` must invalidate the cache slot.
                    write_len_stable(&mut bytes, summary.decreases.len());
                    for clause in &summary.decreases {
                        write_proof_formula_stable(&mut bytes, clause, plan);
                    }
                    // v8 (wire v59): the effect frame is part of the contract
                    // too — a certificate cached for a summary that writes
                    // only `*p` must not be replayed for one that writes
                    // everything. Presence byte (None = UNRECORDED), then the
                    // summary.
                    match &summary.effects {
                        None => write_u8_stable(&mut bytes, 0),
                        Some(effects) => {
                            write_u8_stable(&mut bytes, 1);
                            write_effect_summary_stable(&mut bytes, effects);
                        }
                    }
                }
            }
        }
    }
    ProofDigest::sha256_domain("trust_ir.obligation.digest.v8", &bytes)
}

/// Stable preimage for a [`crate::EffectSummary`] (v59), tagged as on the
/// wire: `reads`, `writes`, then the four flags.
#[cfg(feature = "fmt")]
fn write_effect_summary_stable(out: &mut Vec<u8>, effects: &crate::EffectSummary) {
    fn set(out: &mut Vec<u8>, set: &crate::EffectSet) {
        match set {
            crate::EffectSet::Nothing => write_u8_stable(out, 0),
            crate::EffectSet::Places(places) => {
                write_u8_stable(out, 1);
                write_len_stable(out, places.len());
                for place in places {
                    match place {
                        crate::EffectPlace::ParamPointee { index } => {
                            write_u8_stable(out, 0);
                            write_u32_stable(out, *index);
                        }
                        crate::EffectPlace::Global(global) => {
                            write_u8_stable(out, 1);
                            write_u32_stable(out, global.index());
                        }
                    }
                }
            }
            crate::EffectSet::Everything => write_u8_stable(out, 2),
        }
    }
    set(out, &effects.reads);
    set(out, &effects.writes);
    write_u8_stable(out, u8::from(effects.allocates));
    write_u8_stable(out, u8::from(effects.frees));
    write_u8_stable(out, u8::from(effects.may_unwind));
    write_u8_stable(out, u8::from(effects.io));
}

/// Stable presence-prefixed encoding of the exact IR location an obligation is
/// about. Raw ids are intentional here: unlike the owning function scope used
/// to locate canonical function content, the site itself is the claim's exact
/// `(function, block, instruction)` coordinate.
fn write_obligation_site_stable(out: &mut Vec<u8>, site: Option<ObligationSite>) {
    match site {
        None => write_u8_stable(out, 0),
        Some(site) => {
            write_u8_stable(out, 1);
            write_u32_stable(out, site.function.index());
            write_u32_stable(out, site.block.index());
            write_u32_stable(out, site.inst_index);
        }
    }
}

/// The canonical plan a digest's `ClausePlace::Value` bindings are written
/// through (see [`obligation_content_digest`]): `None` when neither the
/// obligation's formula nor `func`'s summary binds a `Value`, or when `func`
/// is already canonical (the plan would be the identity).
#[cfg(feature = "fmt")]
fn value_binding_plan(
    obligation: &ProofObligation,
    func: &crate::Function,
) -> Option<crate::canonicalize::FunctionCanonicalPlan> {
    let binds_value = |formula: &super::obligations::ProofFormula| {
        formula
            .bindings
            .iter()
            .any(|(_, binding)| matches!(binding.place, super::obligations::ClausePlace::Value(_)))
    };
    let summary_binds_value = func.summary.as_ref().is_some_and(|summary| {
        summary
            .requires
            .iter()
            .chain(&summary.ensures)
            .chain(&summary.decreases)
            .any(binds_value)
    });
    if !(obligation.formula.as_ref().is_some_and(binds_value) || summary_binds_value) {
        return None;
    }
    crate::canonicalize::FunctionCanonicalPlan::new_if_needed(func)
}

/// Stable length-prefixed encoding of one [`ProofFormula`]: schema, payload,
/// then presence-prefixed `smtlib` and `sort`. Shared by the obligation
/// formula and the summary contract clauses in
/// [`obligation_content_digest`]; `plan` is the owning function's canonical
/// plan, through which a `ClausePlace::Value` binding is written.
#[cfg(feature = "fmt")]
fn write_proof_formula_stable(
    out: &mut Vec<u8>,
    formula: &super::obligations::ProofFormula,
    plan: Option<&crate::canonicalize::FunctionCanonicalPlan>,
) {
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
    // v41: the typed clause bindings. Without them two clauses differing ONLY
    // in a bound name's arithmetic domain hash equal — and that is exactly the
    // difference between a claim that holds over `Int` and one that is false at
    // `u64::MAX`, so they must never share a cert-cache slot.
    write_len_stable(out, formula.bindings.len());
    for (name, binding) in &formula.bindings {
        write_str_stable(out, name);
        write_clause_sort_stable(out, &binding.sort);
        match (&binding.place, plan) {
            (super::obligations::ClausePlace::Value(value), Some(plan)) => {
                write_clause_place_stable(
                    out,
                    &super::obligations::ClausePlace::Value(plan.map_binding_value(*value)),
                );
            }
            (place, _) => write_clause_place_stable(out, place),
        }
    }
}

/// Stable preimage for a [`super::obligations::ClauseSort`]. Recursive, because
/// `Array` and `Datatype` nest.
fn write_clause_sort_stable(out: &mut Vec<u8>, sort: &super::obligations::ClauseSort) {
    use super::obligations::ClauseSort as CS;
    match sort {
        CS::Bool => write_u8_stable(out, 0),
        CS::Int => write_u8_stable(out, 1),
        CS::BitVec(w) => {
            write_u8_stable(out, 2);
            write_u32_stable(out, *w);
        }
        CS::Array(k, v) => {
            write_u8_stable(out, 3);
            write_clause_sort_stable(out, k);
            write_clause_sort_stable(out, v);
        }
        CS::Float { eb, sb } => {
            write_u8_stable(out, 4);
            write_u32_stable(out, *eb);
            write_u32_stable(out, *sb);
        }
        CS::RoundingMode => write_u8_stable(out, 5),
        CS::Datatype { name, constructors } => {
            write_u8_stable(out, 6);
            write_str_stable(out, name);
            write_len_stable(out, constructors.len());
            for (ctor, fields) in constructors {
                write_str_stable(out, ctor);
                write_len_stable(out, fields.len());
                for (field, field_sort) in fields {
                    write_str_stable(out, field);
                    write_clause_sort_stable(out, field_sort);
                }
            }
        }
    }
}

/// Stable preimage for a [`super::obligations::ClausePlace`].
fn write_clause_place_stable(out: &mut Vec<u8>, place: &super::obligations::ClausePlace) {
    use super::obligations::ClausePlace as CP;
    match place {
        CP::Param { index } => {
            write_u8_stable(out, 0);
            write_u32_stable(out, *index);
        }
        CP::ResultSlot { index } => {
            write_u8_stable(out, 1);
            write_u32_stable(out, *index);
        }
        CP::MutParamExit { index } => {
            write_u8_stable(out, 2);
            write_u32_stable(out, *index);
        }
        CP::World => write_u8_stable(out, 3),
        CP::Unwind => write_u8_stable(out, 4),
        CP::Value(v) => {
            write_u8_stable(out, 5);
            write_u32_stable(out, v.index());
        }
        // v46: spec-variable places, tagged as on the wire.
        CP::SpecVar { index } => {
            write_u8_stable(out, 6);
            write_u32_stable(out, *index);
        }
        CP::SpecVarNext { index } => {
            write_u8_stable(out, 7);
            write_u32_stable(out, *index);
        }
        // v59: the world epochs, tagged as on the wire. They enter a preimage
        // only where a clause binds one, so no earlier digest moves.
        CP::WorldPre => write_u8_stable(out, 8),
        CP::WorldPost => write_u8_stable(out, 9),
        // v62: the entry-state pointee of a reference parameter, tagged as on
        // the wire. A fresh tag byte, so no older preimage changes and none
        // can equal one that carries it (no digest-domain move).
        CP::ParamPointeeEntry { index } => {
            write_u8_stable(out, 10);
            write_u32_stable(out, *index);
        }
    }
}

/// Write a kind into a stable digest preimage.
///
/// `Custom` MUST contribute its namespace and name: a bare tag would make
/// every `Custom` hash equal, so two obligations from different producer
/// namespaces would share a cert-cache slot.
pub(crate) fn write_obligation_kind_digest(out: &mut Vec<u8>, kind: &ObligationKind) {
    write_u8_stable(out, obligation_kind_tag(kind));
    if let ObligationKind::Custom { namespace, name } = kind {
        write_str_stable(out, namespace);
        write_str_stable(out, name);
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
        ObligationKind::Termination => 13,
        ObligationKind::Ownership => 14,
        // The payload is written separately by `write_obligation_kind_digest`;
        // this tag alone does NOT identify a `Custom` kind.
        ObligationKind::Custom { .. } => 15,
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
/// the most obviously content-free carrier. (Corpus: the content-free carrier
/// is `refuse/certified_with_empty_kernel_term`; "a kernel-less consumer fails
/// closed" is consumer-internal and not expressible as a module —
/// `refuse/coverage_assurance_none_is_unknown` records that.)
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
///
/// A module-free rechecker cannot see what a clause's free names DENOTE (their
/// binding, their place's IR type), so it must refuse every clause whose claim
/// depends on that — in practice every non-literal contract clause. Such a
/// clause is re-checked only through [`ModuleCleanCicRechecker`].
pub trait CleanCicRechecker {
    /// Re-validate `cert`'s serialized proof term against `obligation`'s own
    /// claim in the Clean kernel. Fail-closed: `false` on any failure.
    fn kernel_rechecks_clean_cic(
        &self,
        obligation: &ProofObligation,
        cert: &ProofCertificate,
    ) -> bool;
}

/// The **module-bound** sibling of [`CleanCicRechecker`]: re-validates a
/// `CleanCic` certificate with the obligation's MODULE in scope.
///
/// A contract clause over a free name (`(>= result 0)`) is a claim about an IR
/// PLACE — the name's binding says which one, and the owning function's
/// signature says what IR type it has. Neither is visible to a module-free
/// rechecker, so the module-free [`CleanCicRechecker`] re-checks only closed
/// (literal-only) goals and refuses every free-name clause. Only a
/// module-bound rechecker can confirm that the kernel proposition it
/// re-grounds (e.g. `∀ x : Nat, Nat.ble 0 x = true`) is a faithful reading of
/// the clause over THAT place — for instance that the place is an unsigned
/// integer read at sort `Int` — before the kernel judgment counts.
///
/// # Soundness contract
///
/// The [`CleanCicRechecker`] contract, plus: the claim is reconstructed from
/// `module` AND `obligation` (never from the certificate), and every binding,
/// place or type the reconstruction cannot establish is a `false`.
///
/// Like [`ModuleProofAuthority`], `module` is a parameter rather than captured
/// state, so a rechecker cannot be applied to a module it was not given.
pub trait ModuleCleanCicRechecker {
    /// Re-validate `cert`'s serialized proof term against `obligation`'s claim,
    /// grounded in `module`, in the Clean kernel. Fail-closed.
    fn kernel_rechecks_clean_cic_in(
        &self,
        module: &crate::Module,
        obligation: &ProofObligation,
        cert: &ProofCertificate,
    ) -> bool;

    /// WHICH classified claim family
    /// [`kernel_rechecks_clean_cic_in`](Self::kernel_rechecks_clean_cic_in)
    /// re-checks for this certificate, or `None` when the rechecker does not
    /// classify it.
    ///
    /// A CLASSIFICATION, not a replay: callers ask it only about a certificate
    /// the rechecker has just ACCEPTED (see
    /// [`CleanCicModuleProofAuthority`]'s
    /// [`ModuleProofAuthority::replayed_claim_family`]). The default is `None`
    /// so a rechecker that re-checks a family nobody has quantified yet (a
    /// give-back refinement, a Farkas bound, a translation-validation
    /// equation, a fuel-quantified statement) confers NO coverage by default:
    /// a family arrives unclassified until its quantification is written down
    /// and tested ([`KernelClaimFamily`]).
    fn rechecked_claim_family(
        &self,
        _module: &crate::Module,
        _obligation: &ProofObligation,
        _cert: &ProofCertificate,
    ) -> Option<KernelClaimFamily> {
        None
    }
}

/// The QUANTIFICATION FAMILY of a claim an in-process kernel replay
/// re-established — what a consumer derives input coverage from (basis K of
/// `trust_ir_build::coverage_establishment_report`).
///
/// A kernel replay proves the obligation's claim AS THE REPLAY RE-GROUNDED IT.
/// How much of the input space that claim quantifies over is a property of
/// the grounding, not of the kernel: a closed ground decision is a statement
/// about every input, a fuel-bounded or `Done`-conditional statement is not.
/// Each family therefore needs its quantification written down before it may
/// carry any coverage, and a family nobody has written down is simply not a
/// variant here — a replayed claim with no family is UNCLASSIFIED and
/// establishes nothing.
///
/// `#[non_exhaustive]` so a consumer's table over it needs a fail-closed
/// wildcard: a family added here arrives in a downstream build as "no bound".
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[non_exhaustive]
pub enum KernelClaimFamily {
    /// The CONTRACT path: the claim the kernel re-checked is the obligation's
    /// own contract predicate — its ONE SMT-LIB text
    /// ([`super::ProofFormula::smtlib_text`]; an opaque or self-contradicting
    /// formula grounds nothing) — re-grounded from the obligation (and, for a
    /// free-name clause, from the module) by
    /// `clean_expr_lowering::contract::contract_goal_in` — either a CLOSED
    /// ground Bool decision over literals (`@Eq Bool <decision> Bool.true`),
    /// or the single free-name nonneg tautology `∀ x : Nat, Nat.ble 0 x =
    /// true` bound to an unsigned-integer IR place. Both are universally
    /// closed: the certificate proves the obligation's formula for every
    /// input, which is `CoverageBound::Unbounded` relative to that formula
    /// (faithfulness of the formula to the program is a separate axis).
    ///
    /// Only a directive-less certificate or one citing the
    /// [`KERNEL_ANCHOR_TRUST_IR_CONTRACT`] anchor is classified here; a
    /// certificate labelled with any other anchor stays unclassified even when
    /// the contract re-check accepts its term, because what its producer
    /// meant it to prove is not what was replayed.
    ContractGroundDecision,
}

impl KernelClaimFamily {
    /// Stable lowercase spelling for diagnostics and fingerprints.
    #[must_use]
    pub const fn code(self) -> &'static str {
        match self {
            KernelClaimFamily::ContractGroundDecision => "contract_ground_decision",
        }
    }
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

    /// The classified family of the claim this authority REPLAYS for
    /// `certificate`, or `None`.
    ///
    /// # Soundness contract
    ///
    /// `Some(family)` only when, in this call, the authority has replayed
    /// `certificate` against `obligation` exactly as
    /// [`replays_authority`](Self::replays_authority) would (a `false` there
    /// is a `None` here), AND the claim it replayed is of `family`. It is the
    /// input coverage is derived from, so it must never be a label read off
    /// the certificate.
    ///
    /// The default is `None`: an authority that does not say what it replayed
    /// confers no coverage. [`CleanCicModuleProofAuthority`] overrides it,
    /// delegating the classification to its rechecker's
    /// [`ModuleCleanCicRechecker::rechecked_claim_family`].
    fn replayed_claim_family(
        &self,
        _module: &crate::Module,
        _obligation: &ProofObligation,
        _certificate: &ProofCertificate,
    ) -> Option<KernelClaimFamily> {
        None
    }
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

/// Adapter from a module-bound Clean kernel rechecker to the module-scoped
/// proof-authority capability: the `ModuleProofAuthority` counterpart of
/// [`CleanCicProofAuthorityRechecker`]. Same identity floor (certificate names
/// the obligation, non-empty term, lineage digest matches), then the
/// module-bound kernel re-check.
pub struct CleanCicModuleProofAuthority<'a> {
    pub clean_cic: &'a dyn ModuleCleanCicRechecker,
}

impl ModuleProofAuthority for CleanCicModuleProofAuthority<'_> {
    fn replays_authority(
        &self,
        module: &crate::Module,
        obligation: &ProofObligation,
        certificate: &ProofCertificate,
    ) -> bool {
        certificate.obligation == obligation.id
            && matches!(
                &certificate.evidence,
                ProofEvidence::CleanCic { term, .. } if !term.is_empty()
            )
            && clean_cic_lineage_binds(
                obligation,
                &certificate.evidence,
                &module_symbol_resolver(module),
            )
            && self
                .clean_cic
                .kernel_rechecks_clean_cic_in(module, obligation, certificate)
    }

    /// Replays first — the full [`Self::replays_authority`] conjunction, the
    /// kernel re-check included — and only then asks the rechecker to
    /// classify what it re-checked. A certificate this authority does not
    /// replay has no family, whatever its directive says.
    fn replayed_claim_family(
        &self,
        module: &crate::Module,
        obligation: &ProofObligation,
        certificate: &ProofCertificate,
    ) -> Option<KernelClaimFamily> {
        if !ModuleProofAuthority::replays_authority(self, module, obligation, certificate) {
            return None;
        }
        self.clean_cic
            .rechecked_claim_family(module, obligation, certificate)
    }
}

/// [`obligation_has_replayed_authority`] with the module in scope: true only
/// when a strong-status obligation has a certificate `authority` replays
/// against `module`.
pub fn obligation_has_replayed_module_authority(
    module: &crate::Module,
    obligation: &ProofObligation,
    certificates: &[ProofCertificate],
    authority: &dyn ModuleProofAuthority,
) -> bool {
    obligation.status.is_discharged_tier()
        && certificates
            .iter()
            .any(|certificate| authority.replays_authority(module, obligation, certificate))
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
    obligation.status.is_discharged_tier()
        && certificates
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

impl ModuleCleanCicRechecker for RejectingCleanCicRechecker {
    #[inline]
    fn kernel_rechecks_clean_cic_in(
        &self,
        _module: &crate::Module,
        _obligation: &ProofObligation,
        _cert: &ProofCertificate,
    ) -> bool {
        false
    }
}

/// [`obligation_has_kernel_rechecked_clean_cic`] with the module in scope: the
/// same lineage-bound, non-empty-term floor, then the MODULE-BOUND kernel
/// re-check ([`ModuleCleanCicRechecker`]). This is the gate that can admit a
/// free-name contract clause, because only it can check what the name denotes.
pub fn obligation_has_kernel_rechecked_clean_cic_in(
    module: &crate::Module,
    obligation: &ProofObligation,
    certificates: &[ProofCertificate],
    rechecker: &dyn ModuleCleanCicRechecker,
) -> bool {
    let resolve = module_symbol_resolver(module);
    certificates.iter().any(|cert| {
        cert.obligation == obligation.id
            && matches!(
                &cert.evidence,
                ProofEvidence::CleanCic { term, .. } if !term.is_empty()
            )
            && clean_cic_lineage_binds(obligation, &cert.evidence, &resolve)
            && rechecker.kernel_rechecks_clean_cic_in(module, obligation, cert)
    })
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
        for (lane, value) in self.lanes.iter_mut().enumerate() {
            *value ^= byte_len.rotate_left((lane * 11) as u32);
            *value = value.rotate_left(17).wrapping_mul(0x9e3779b185ebca87);
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

/// Canonical stable encoding of a cross-module reference (v41).
///
/// Framed exactly like every other identity in this module: fixed-width tags,
/// length-prefixed strings, no textual formatting. The optional obligation is a
/// presence byte so `None` and `Some(0)` can never collide.
pub(crate) fn write_extern_ref_stable(out: &mut Vec<u8>, reference: &crate::ExternRef) {
    write_u32_stable(out, reference.module.index());
    write_str_stable(out, &reference.symbol);
    match reference.obligation {
        None => write_u8_stable(out, 0),
        Some(obligation) => {
            write_u8_stable(out, 1);
            write_u32_stable(out, obligation.index());
        }
    }
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
        ProofEvidence::InheritedFromCallee {
            callee,
            obligation,
            external,
        } => {
            // Tag 6 keeps its exact stable preimage when there is no external
            // authority, so every digest already computed over a local
            // inheritance is unchanged. The cross-crate form gets its own tag
            // 8 — a content digest may never hash "discharged here" and
            // "discharged in crate X" equal.
            match external {
                None => {
                    write_u8_stable(out, 6);
                    write_u32_stable(out, callee.index());
                    write_u32_stable(out, obligation.index());
                }
                Some(external) => {
                    write_u8_stable(out, 8);
                    write_u32_stable(out, callee.index());
                    write_u32_stable(out, obligation.index());
                    write_extern_ref_stable(out, external);
                }
            }
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
                    // The binding enters the evidence identity ONLY when
                    // present, so every digest computed over an unbound
                    // directive keeps its exact bytes. No ambiguity: the
                    // axiom list is length-framed, so an unbound preimage can
                    // never be a prefix-extension of another unbound one.
                    if let Some(binding) = &recheck.binding {
                        write_u8_stable(out, 1);
                        binding.write_stable(out);
                    }
                }
            }
        }
    }
}
