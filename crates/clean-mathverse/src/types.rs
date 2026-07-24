// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Core Mathverse Library types: constant headers, axiom profiles, source systems.

use serde::{Deserialize, Serialize};

/// Index into the FlatExpr arena within a shard.
pub type ExprIdx = u32;

/// Index into the constant header table within a shard.
pub type ConstantIdx = u32;

/// Index into the string table within a shard.
pub type StringIdx = u32;

/// Index into the provenance sidecar.
pub type ProvenanceIdx = u32;

/// Index into the concept graph.
pub type ConceptIdx = u32;

/// Index into the conjecture queue.
pub type ConjectureIdx = u32;

/// Sentinel value indicating no value/axiomatized constant.
pub const NO_VALUE: u32 = u32::MAX;

// ---------------------------------------------------------------------------
// SourceSystem
// ---------------------------------------------------------------------------

/// Source proof system for an imported constant.
#[repr(u8)]
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum SourceSystem {
    Lean4 = 0,
    Coq = 1,
    Agda = 2,
    Idris2 = 3,
    FStar = 4,
    Cedille = 5,
    Isabelle = 6,
    HolLight = 7,
    Hol4 = 8,
    Metamath = 9,
    Mizar = 10,
    Dafny = 11,
    Why3 = 12,
    Nuprl = 13,
    Pvs = 14,
    Acl2 = 15,
    LiquidHaskell = 16,
    Key = 17,
    FramaC = 18,
    Spark = 19,
    GammaCrown = 20,
    AlphaBetaCrown = 21,
    Z3 = 22,
    Cvc5 = 23,
    Vampire = 24,
    CaDiCaL = 25,
    Tlc = 26,
    CleanNative = 27,
    /// Combined Key/Frama-C/SPARK (origin/main compat).
    KeyFramacSpark = 28,
    /// SMT solver (generic, origin/main compat).
    SmtSolver = 29,
    /// SAT solver (generic, origin/main compat).
    SatSolver = 30,
    /// ATP prover (generic, origin/main compat).
    Atp = 31,
    /// arXiv natural-language mathematics (autoformalization source).
    Arxiv = 32,
    /// Dedukti (.dk) logical framework.
    Dedukti = 33,
    /// Lambdapi (.lp) logical framework.
    Lambdapi = 34,
    /// Abella (.thm) proof assistant.
    Abella = 35,
    /// Beluga (.bel) proof assistant.
    Beluga = 36,
    /// Twelf (.elf) logical framework.
    Twelf = 37,
    /// Naproche (.ftl) natural language prover.
    Naproche = 38,
    /// Minlog (.scm) proof assistant.
    Minlog = 39,
    /// Arend (.ard) HoTT proof assistant.
    Arend = 40,
    /// Metamath Zero (.mm0/.mm1).
    Mm0 = 41,
    /// Kind2 (.kind2/.kind) dependent types.
    Kind2 = 42,
    /// Rzk (.rzk) simplicial HoTT.
    Rzk = 43,
    /// ATS2/Postiats (.sats/.dats) dependent types.
    Ats2 = 44,
    /// LaTTe (.clj) type theory in Clojure.
    Latte = 45,
    /// CubicalTT (.ctt) cubical type theory.
    CubicalTT = 46,
    /// cooltt (.cooltt) cubical type theory.
    Cooltt = 47,
    /// redtt (.red) cubical type theory.
    Redtt = 48,
    /// Verus — Rust verification with proof/spec functions.
    Verus = 49,
    /// Creusot — Rust verification with Pearlite contracts.
    Creusot = 50,
    /// Kani — Rust model checking with proof harnesses.
    Kani = 51,
    /// Prusti — Rust verification with Viper backend.
    Prusti = 52,
    /// Aeneas — Rust to Lean 4 verification pipeline.
    Aeneas = 53,
    /// Hax — Rust to F*/Coq/Lean verification pipeline.
    Hax = 54,
    /// CreuSAT — Creusot-verified SAT solver.
    CreuSat = 55,
    /// Stainless — Scala formal verification.
    Stainless = 56,
    /// LISA — Scala proof assistant.
    Lisa = 57,
    /// Move Prover — Move language specification prover.
    MoveProver = 58,
    /// Boogie — Intermediate verification language.
    Boogie = 59,
    /// Viper — Verification infrastructure for permission-based reasoning.
    Viper = 60,
    /// VeriFast — C/Java separation logic verifier.
    VeriFast = 61,
    /// Sail (.sail) ISA description language.
    Sail = 62,
    /// K Framework (.k) rewriting-based semantic framework.
    KFramework = 63,
    /// Alloy (.als) relational modeling language.
    Alloy = 64,
    /// P language (.p) state-machine modeling.
    PLang = 65,
    /// Ethereum Act (.act) smart contract specification.
    EthAct = 66,
    /// SV-COMP benchmarks (.c) — C verification benchmarks.
    SvBenchmarks = 67,
    /// Matita (.ma) — CIC-based interactive theorem prover.
    Matita = 68,
    /// Cake — theorems graduated from clean math projects through the
    /// `clean mathverse graduate` intake gate (with their carried definition
    /// dependencies under graduation v2). Every Cake-tagged shard must carry
    /// a digest-bound `mathverse-graduation-v2` (or legacy v1) sidecar record
    /// and pass `shard_verify::cake_gate::verify_cake_shard`.
    Cake = 69,
}

impl TryFrom<u8> for SourceSystem {
    type Error = u8;

    fn try_from(value: u8) -> Result<Self, Self::Error> {
        match value {
            0 => Ok(Self::Lean4),
            1 => Ok(Self::Coq),
            2 => Ok(Self::Agda),
            3 => Ok(Self::Idris2),
            4 => Ok(Self::FStar),
            5 => Ok(Self::Cedille),
            6 => Ok(Self::Isabelle),
            7 => Ok(Self::HolLight),
            8 => Ok(Self::Hol4),
            9 => Ok(Self::Metamath),
            10 => Ok(Self::Mizar),
            11 => Ok(Self::Dafny),
            12 => Ok(Self::Why3),
            13 => Ok(Self::Nuprl),
            14 => Ok(Self::Pvs),
            15 => Ok(Self::Acl2),
            16 => Ok(Self::LiquidHaskell),
            17 => Ok(Self::Key),
            18 => Ok(Self::FramaC),
            19 => Ok(Self::Spark),
            20 => Ok(Self::GammaCrown),
            21 => Ok(Self::AlphaBetaCrown),
            22 => Ok(Self::Z3),
            23 => Ok(Self::Cvc5),
            24 => Ok(Self::Vampire),
            25 => Ok(Self::CaDiCaL),
            26 => Ok(Self::Tlc),
            27 => Ok(Self::CleanNative),
            28 => Ok(Self::KeyFramacSpark),
            29 => Ok(Self::SmtSolver),
            30 => Ok(Self::SatSolver),
            31 => Ok(Self::Atp),
            32 => Ok(Self::Arxiv),
            33 => Ok(Self::Dedukti),
            34 => Ok(Self::Lambdapi),
            35 => Ok(Self::Abella),
            36 => Ok(Self::Beluga),
            37 => Ok(Self::Twelf),
            38 => Ok(Self::Naproche),
            39 => Ok(Self::Minlog),
            40 => Ok(Self::Arend),
            41 => Ok(Self::Mm0),
            42 => Ok(Self::Kind2),
            43 => Ok(Self::Rzk),
            44 => Ok(Self::Ats2),
            45 => Ok(Self::Latte),
            46 => Ok(Self::CubicalTT),
            47 => Ok(Self::Cooltt),
            48 => Ok(Self::Redtt),
            49 => Ok(Self::Verus),
            50 => Ok(Self::Creusot),
            51 => Ok(Self::Kani),
            52 => Ok(Self::Prusti),
            53 => Ok(Self::Aeneas),
            54 => Ok(Self::Hax),
            55 => Ok(Self::CreuSat),
            56 => Ok(Self::Stainless),
            57 => Ok(Self::Lisa),
            58 => Ok(Self::MoveProver),
            59 => Ok(Self::Boogie),
            60 => Ok(Self::Viper),
            61 => Ok(Self::VeriFast),
            62 => Ok(Self::Sail),
            63 => Ok(Self::KFramework),
            64 => Ok(Self::Alloy),
            65 => Ok(Self::PLang),
            66 => Ok(Self::EthAct),
            67 => Ok(Self::SvBenchmarks),
            68 => Ok(Self::Matita),
            69 => Ok(Self::Cake),
            other => Err(other),
        }
    }
}

// ---------------------------------------------------------------------------
// ImportConfidence
// ---------------------------------------------------------------------------

/// Trust level of an imported constant.
///
/// Ordering: `KernelVerified` (highest) > `KernelBridged` > `SourceVerified` >
/// `Translated` > `KernelCheckedConditional` > `Axiomatized` > `Unverified`
/// (lowest). The `Ord` implementation reflects this trust ordering, NOT the
/// discriminant values — discriminants are stable for shard binary
/// compatibility.
#[repr(u8)]
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum ImportConfidence {
    /// Fully verified by the clean kernel from shard reconstruction.
    KernelVerified = 0,
    /// Translated from another system with type preservation proof.
    Translated = 1,
    /// Statement imported but proof axiomatized (skeleton may exist).
    Axiomatized = 2,
    /// Unverified import (statement only, no proof attempted).
    Unverified = 3,
    /// Source system verified this constant, but the mathverse reconstruction
    /// has not been independently kernel-checked. Assigned during name-match
    /// upgrade when the source .olean passes TC but the reconstructed shard
    /// representation may be lossy (placeholder Sort(0), missing universe
    /// levels, etc.).
    SourceVerified = 6,
    /// **Kernel-re-checked, conditionally trusted (two-tier Isabelle import).**
    /// The constant's proof term was re-checked by the clean kernel
    /// (`value : type` accepted), but its transitive axiom closure includes one
    /// or more **trusted-ledger axioms** (`isabelle.trusted.s<serial>`
    /// restatements the two-tier importer registers when a line failed every
    /// reconstruction/reprove arm yet its statement embedded cleanly). It is
    /// therefore **strictly weaker than [`Self::KernelVerified`]**: the kernel
    /// accepted the proof, but only *relative to* the trusted ledger, never
    /// from a foundational-only closure. The foundational gate
    /// (`⊆ FOUNDATIONAL_AXIOMS`) deliberately excludes these from
    /// `KernelVerified`; this is the honest second tier. NEVER emit it for a
    /// foundational-closure proof (that is `KernelVerified`).
    KernelCheckedConditional = 7,
    /// **Kernel-checked END-TO-END via a foundational cross-lane bridge
    /// (Isabelle ledger to Mathlib-KV).** A blocked Isabelle statement `T_isa`
    /// earns this when *all* hold: (a) a Mathlib constant `T_ml` is itself
    /// [`Self::KernelVerified`] (Clean re-checked `T_ml.value : T_ml.type`
    /// through Clean's own kernel); (b) the connective-iso composer produced a
    /// kernel-checked `bridge : stmt(T_isa) <-> type(T_ml)` whose transitive
    /// axiom closure is foundational-only (`FOUNDATIONAL_AXIOMS`); (c) the minted
    /// witness `Iff.mpr bridge T_ml.value : stmt(T_isa)` was `add_decl`-accepted
    /// by the kernel with a foundational closure.
    ///
    /// **Trust: end-to-end Clean-kernel-verified.** Both composed inputs are real
    /// kernel-checked proofs with foundational closure, so `stmt(T_isa)` is
    /// Clean-provable by composition — there is NO trusted-ledger axiom and NO
    /// oracle in the closure (unlike [`Self::KernelCheckedConditional`], which
    /// depends on `isabelle.trusted.*` restatements). It is therefore ranked
    /// immediately BELOW [`Self::KernelVerified`] and ABOVE every
    /// import-confidence tier (`SourceVerified`/`Translated`) and above the
    /// conditional tier.
    ///
    /// **Why NOT [`Self::KernelVerified`].** Per `CLAUDE.md`'s proof-soundness
    /// rules, `KernelVerified` is reserved for a constant whose *own* imported
    /// value the kernel re-checked. `KernelBridged` is honest that no native
    /// Isabelle proof term was replayed: the statement arrived via the bridge and
    /// is discharged through a *Mathlib* constant plus a foundational connective
    /// bridge. The residual distinction from native `KernelVerified` is thus
    /// **provenance** (how the statement was proved), not trust (the kernel
    /// accepted a foundational closure either way). Kept a separate tier so it is
    /// never counted in native-KV metrics and never overwrites a `KernelVerified`
    /// verdict.
    KernelBridged = 8,
}

impl ImportConfidence {
    /// Trust rank used for ordering. Lower rank = higher trust.
    /// KernelVerified(0) > KernelBridged(1) > SourceVerified(2) > Translated(3) >
    /// KernelCheckedConditional(4) > Axiomatized(5) > Unverified(6).
    /// `KernelBridged` ranks immediately below `KernelVerified`: it is an
    /// end-to-end Clean-kernel-verified, foundational-closure proof (a Mathlib-KV
    /// witness composed through a foundational connective bridge), so it outranks
    /// every import-confidence tier and the conditional tier; it sits below native
    /// `KernelVerified` only on PROVENANCE (the statement arrived via the bridge,
    /// not from a re-checked native value). `KernelCheckedConditional` outranks
    /// `Axiomatized` (it carries a real kernel-checked proof) but never the tiers
    /// above it (its closure depends on trusted-ledger axioms).
    #[inline]
    const fn trust_rank(self) -> u8 {
        match self {
            Self::KernelVerified => 0,
            Self::KernelBridged => 1,
            Self::SourceVerified => 2,
            Self::Translated => 3,
            Self::KernelCheckedConditional => 4,
            Self::Axiomatized => 5,
            Self::Unverified => 6,
        }
    }
}

impl PartialOrd for ImportConfidence {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for ImportConfidence {
    #[inline]
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.trust_rank().cmp(&other.trust_rank())
    }
}

impl TryFrom<u8> for ImportConfidence {
    type Error = u8;

    fn try_from(value: u8) -> Result<Self, Self::Error> {
        match value {
            0 => Ok(Self::KernelVerified),
            1 => Ok(Self::Translated),
            2 => Ok(Self::Axiomatized),
            3 => Ok(Self::Unverified),
            6 => Ok(Self::SourceVerified),
            7 => Ok(Self::KernelCheckedConditional),
            8 => Ok(Self::KernelBridged),
            other => Err(other),
        }
    }
}

// ---------------------------------------------------------------------------
// ContentDomain
// ---------------------------------------------------------------------------

/// Content domain classification for a constant.
#[repr(u8)]
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum ContentDomain {
    PureMath = 0,
    Software = 1,
    Complexity = 2,
    NnVerification = 3,
    Physics = 4,
    Logic = 5,
    Cryptography = 6,
}

impl TryFrom<u8> for ContentDomain {
    type Error = u8;

    fn try_from(value: u8) -> Result<Self, Self::Error> {
        match value {
            0 => Ok(Self::PureMath),
            1 => Ok(Self::Software),
            2 => Ok(Self::Complexity),
            3 => Ok(Self::NnVerification),
            4 => Ok(Self::Physics),
            5 => Ok(Self::Logic),
            6 => Ok(Self::Cryptography),
            other => Err(other),
        }
    }
}

// ---------------------------------------------------------------------------
// TrustLevel (from HEAD/main — coarser trust classification)
// ---------------------------------------------------------------------------

/// Trust level for a constant (coarser than ImportConfidence).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum TrustLevel {
    /// Fully verified by clean kernel with no axiom dependencies.
    KernelVerified,
    /// Verified with known axiom dependencies (tracked in AxiomProfile).
    AxiomDependent,
    /// Imported with proof certificate replay.
    CertificateReplayed,
    /// Imported with axiomatized gaps (e.g., LCF-erased proofs).
    PartiallyAxiomatized,
    /// Trusted oracle (e.g., SMT solver without certificate).
    TrustedOracle,
}

// ---------------------------------------------------------------------------
// Provenance (from HEAD/main — high-level provenance record)
// ---------------------------------------------------------------------------

/// Provenance record for an imported constant.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Provenance {
    pub source: SourceSystem,
    pub original_name: String,
    pub source_file: Option<String>,
    pub axiom_profile: AxiomProfile,
}

// ---------------------------------------------------------------------------
// AxiomProfile
// ---------------------------------------------------------------------------

/// Bitvector tracking which axioms a constant depends on.
///
/// **Three computation stages, do not conflate them:**
/// 1. *Local* profile — set by the per-constant importers
///    ([`crate::lean4::olean::alpha::compute_axiom_profile`]): a bit is set only
///    when the constant *is itself* a named axiom (e.g. `Classical.choice`) or
///    has `Axiom`/`Opaque` kind. This is one level deep and is what each header
///    carries immediately after lowering.
/// 2. *In-shard transitive closure* — produced by
///    [`crate::shard::ShardWriter::finalize_axiom_profiles`] (a monotone bitset
///    fixed-point over the in-shard dependency graph), which the conversion
///    entry points run before serializing. After that pass a constant's profile
///    is `union(local(T), profile(dep) for every dep reachable through any
///    depth of in-shard dependency)`. A constant that uses an axiom through a
///    chain of intermediate definitions therefore carries the axiom's bit.
/// 3. *Cross-shard transitive closure* — when the library builder splits the
///    import at `shard_size_limit`, a constant's dependency can land in a
///    *different* shard, which the in-shard pass (stage 2) necessarily skips by
///    name. After all shards are assembled, the canonical builder runs
///    [`crate::lean4::olean::axiom_profile::propagate_cross_shard_axiom_profiles`]
///    — a monotone bitset fixed-point over a *global* name→profile graph merged
///    from every shard — and writes the closed profiles back into each shard.
///    After that pass a constant's profile additionally includes every axiom
///    reachable through dependencies in *other* shards, so a theorem in shard B
///    that uses `Classical.choice` only through a constant defined in shard A
///    now carries the CHOICE bit. This cross-shard closure now runs as part of
///    library finalization ([`crate::build_library::build_lean4_library`]); it
///    is cycle-safe across shard boundaries.
///
/// The only residual gap is cross-*library* / cross-*release*: names defined in
/// no shard of the current build (genuine externals) carry no known bits and are
/// conservatively ignored, exactly as the in-shard pass treats names absent from
/// its shard. Trust enforcement uses these bits to gate access — constants with
/// certain bits set are invisible to tactics unless explicitly opted in.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct AxiomProfile(pub u64);

impl AxiomProfile {
    pub const NONE: Self = Self(0);

    // Logic axioms
    pub const CHOICE: Self = Self(1 << 0);
    pub const LEM: Self = Self(1 << 1);
    pub const PROP_EXT: Self = Self(1 << 2);
    pub const FUNC_EXT: Self = Self(1 << 3);
    pub const QUOT: Self = Self(1 << 4);
    pub const UNIVALENCE: Self = Self(1 << 5);
    pub const LARGE_ELIM: Self = Self(1 << 6);

    // Aliases for origin/main compatibility
    pub const CLASSICAL: Self = Self(1 << 0); // maps to CHOICE
    pub const EXTENSIONALITY: Self = Self(1 << 1); // maps to LEM bit
    pub const PROOF_IRRELEVANCE: Self = Self(1 << 3); // maps to FUNC_EXT bit

    // System-specific
    pub const HOL_AXIOMS: Self = Self(1 << 7);
    pub const HOL_EMBEDDING: Self = Self(1 << 7); // alias for HOL_AXIOMS
    pub const MIZAR_TG: Self = Self(1 << 8);
    pub const MIZAR_SOFT_TYPE: Self = Self(1 << 8); // alias for MIZAR_TG

    // Trust/soundness
    pub const UNIVERSE_INCON: Self = Self(1 << 10);
    pub const AXIOMATIZED: Self = Self(1 << 11);
    pub const BRIDGE_AXIOM: Self = Self(1 << 12);

    // Arithmetic/analysis
    pub const REAL_AXIOMS: Self = Self(1 << 13);
    pub const LRA_TRUSTED: Self = Self(1 << 14);

    // NN verification
    pub const FLOAT_APPROX: Self = Self(1 << 15);
    pub const NN_ABSTRACTION: Self = Self(1 << 16);

    // System-specific embedding axioms
    pub const COQ_SPROP: Self = Self(1 << 17);
    pub const COQ_MODULE_FUNCTOR: Self = Self(1 << 18);
    pub const COQ_COINDUCTIVE: Self = Self(1 << 19);
    pub const ISABELLE_LCF_ERASED: Self = Self(1 << 20);
    pub const AGDA_CUBICAL: Self = Self(1 << 21);
    pub const IDRIS_QTT: Self = Self(1 << 22);

    // Verification axioms
    pub const SMT_ORACLE: Self = Self(1 << 23);
    pub const SAT_CERT: Self = Self(1 << 24);
    pub const ATP_CERT: Self = Self(1 << 25);

    // Autoformalization axioms
    pub const ARXIV_NL_IMPORT: Self = Self(1 << 26);

    /// Convert→verify HINT (not a trust/axiom bit): the constant's value was
    /// translated using a *derived* recursor branch shape that the importer
    /// cannot fully certify structurally — a match whose return-predicate
    /// universe was derived from a defined constant's result sort
    /// (`coq::alpha::motive_result_level`), or an indexed-family match whose
    /// recursive-field induction hypotheses were synthesized as
    /// `motive fidx… field`. Such a shape is a best-effort guess; the kernel is
    /// the arbiter. If the kernel ACCEPTS the value it is a genuine
    /// `KernelVerified` (this bit is then irrelevant). If the kernel REJECTS it,
    /// the constant falls back to a CLEAN type-only axiom (`AxiomFallback(None)`,
    /// no masked-failure taint) — byte-identical in effect to never having
    /// translated the value, which is exactly the pre-derivation baseline.
    /// Deliberately excluded from `TRUST_GATED` and every axiom-counting mask: it
    /// never denotes an axiom dependency.
    pub const SPECULATIVE_MOTIVE: Self = Self(1 << 27);

    /// Dump-salvage stand-in HINT (not a trust/axiom bit): this value-less
    /// axiom row was minted by the Coq dumper's CRASH-SALVAGE rungs — the
    /// declaration is a real `Definition`/record in Coq (Coq's kernel checked
    /// a value/structure for it; conversion there can unfold it), but sertop
    /// crashed serializing that payload, so only the statement survived as a
    /// type-only `(CoqAxiom … StandIn)` stand-in. The axiom-ness of the row is
    /// already carried by [`Self::AXIOMATIZED`]; THIS bit records the
    /// *provenance* that the value-less-ness is a reconstruction gap rather
    /// than a genuinely value-free Coq `Axiom`/`Parameter`.
    ///
    /// Consumed by the verify-side taint classification
    /// (`verify::incremental`): a kernel VALUE rejection whose dependency set
    /// includes such a stand-in cannot be distinguished from a conversion the
    /// kernel simply could not complete (the stand-in cannot delta-unfold), so
    /// it is classified as a CLEAN type-only fallback (no masked-failure taint
    /// seed) instead of evidence of a wrong proof — never `KernelVerified`.
    /// Deliberately excluded from `TRUST_GATED` and every axiom-counting mask
    /// (like [`Self::SPECULATIVE_MOTIVE`]): it never denotes an ADDITIONAL
    /// axiom dependency beyond the `AXIOMATIZED` bit the row already carries.
    pub const SALVAGED_STAND_IN: Self = Self(1 << 28);

    /// Axiom-DISCHARGE provenance flag (not a trust/axiom bit): this constant
    /// was declared as an `Axiom` by its source system, but Clean re-proved its
    /// stated type with a hand-built kernel term
    /// (`crate::verify::incremental::axiom_discharge`) and registered it as a
    /// genuine `Declaration::Theorem`. The row is therefore truly
    /// `KernelVerified` and carries NO axiom dependency of its own — the flag
    /// records only the PROVENANCE that the statement was axiomatic upstream, so
    /// an auditor can tell an originally-proven theorem from a source axiom
    /// Clean discharged.
    ///
    /// Like [`Self::SPECULATIVE_MOTIVE`] / [`Self::SALVAGED_STAND_IN`], it is a
    /// [`Self::NON_AXIOM_HINTS`] member: masked out of [`Self::is_kernel_verified`]
    /// and [`Self::axiom_count`] and excluded from [`Self::TRUST_GATED`], so a
    /// discharged constant is treated for every trust / axiom-accounting purpose
    /// exactly as a from-scratch kernel-proven theorem. The current runtime
    /// record of which constants were discharged is
    /// `IncrementalVerifyReport::discharged_axiom_names`.
    ///
    /// NOTE: bit 28 (the value the BRICK 1.0 brief reserved) was already taken
    /// by [`Self::SALVAGED_STAND_IN`] on the current main; this flag takes the
    /// next free bit, 29.
    pub const DISCHARGED_AXIOM: Self = Self(1 << 29);

    /// Bits that gate trust: constants with any of these set are invisible
    /// to tactics and elaboration unless explicitly opted in.
    pub const TRUST_GATED: Self = Self(
        (1 << 11) | (1 << 10) | (1 << 15) | (1 << 16), // AXIOMATIZED | UNIVERSE_INCON | FLOAT_APPROX | NN_ABSTRACTION
    );

    /// Bits that are provenance HINTS, not axiom dependencies: masked out of
    /// [`Self::is_kernel_verified`] and [`Self::axiom_count`] so a constant
    /// carrying one is treated exactly as if it were unset for every trust /
    /// axiom-accounting purpose. [`Self::SPECULATIVE_MOTIVE`],
    /// [`Self::SALVAGED_STAND_IN`], and [`Self::DISCHARGED_AXIOM`].
    pub const NON_AXIOM_HINTS: Self = Self((1 << 27) | (1 << 28) | (1 << 29));

    /// Create a profile with the given bits set.
    #[inline]
    pub const fn new(bits: u64) -> Self {
        Self(bits)
    }

    /// Check if a specific bit is set (accepts u64 for zone alpha compat).
    #[inline]
    pub const fn has_bit(self, bit: u64) -> bool {
        (self.0 & bit) != 0
    }

    /// Check if a specific axiom flag is set.
    #[inline]
    pub const fn has(self, flag: Self) -> bool {
        (self.0 & flag.0) != 0
    }

    /// Check if a specific profile's bits are all present.
    #[inline]
    pub const fn contains(self, other: Self) -> bool {
        (self.0 & other.0) == other.0
    }

    /// Union two profiles (transitive propagation).
    #[inline]
    pub const fn union(self, other: Self) -> Self {
        Self(self.0 | other.0)
    }

    /// Check if this profile is a superset of another.
    #[inline]
    pub const fn is_superset_of(self, other: Self) -> bool {
        (self.0 & other.0) == other.0
    }

    /// Check if this profile is trust-gated (should be invisible by default).
    #[inline]
    pub const fn is_trust_gated(self) -> bool {
        (self.0 & Self::TRUST_GATED.0) != 0
    }

    /// Check if this profile has no axiom dependencies.
    #[inline]
    pub const fn is_pure(self) -> bool {
        self.0 == 0
    }

    /// Check if this is a kernel-verified constant (no axiom bits set).
    #[inline]
    pub const fn is_kernel_verified(self) -> bool {
        (self.0 & !Self::NON_AXIOM_HINTS.0) == 0
    }

    /// Count the number of axiom bits set.
    #[inline]
    pub const fn axiom_count(self) -> u32 {
        (self.0 & !Self::NON_AXIOM_HINTS.0).count_ones()
    }
}

impl std::ops::BitOr for AxiomProfile {
    type Output = Self;
    #[inline]
    fn bitor(self, rhs: Self) -> Self {
        self.union(rhs)
    }
}

impl std::ops::BitOrAssign for AxiomProfile {
    #[inline]
    fn bitor_assign(&mut self, rhs: Self) {
        self.0 |= rhs.0;
    }
}

impl std::ops::BitAnd for AxiomProfile {
    type Output = Self;
    #[inline]
    fn bitand(self, rhs: Self) -> Self {
        Self(self.0 & rhs.0)
    }
}

impl std::ops::BitAnd<u64> for AxiomProfile {
    type Output = u64;
    #[inline]
    fn bitand(self, rhs: u64) -> u64 {
        self.0 & rhs
    }
}

impl std::ops::Not for AxiomProfile {
    type Output = u64;
    #[inline]
    fn not(self) -> u64 {
        !self.0
    }
}

impl PartialEq<u64> for AxiomProfile {
    #[inline]
    fn eq(&self, other: &u64) -> bool {
        self.0 == *other
    }
}

impl PartialEq<AxiomProfile> for u64 {
    #[inline]
    fn eq(&self, other: &AxiomProfile) -> bool {
        *self == other.0
    }
}

impl From<AxiomProfile> for u64 {
    #[inline]
    fn from(p: AxiomProfile) -> u64 {
        p.0
    }
}

impl From<u64> for AxiomProfile {
    #[inline]
    fn from(bits: u64) -> Self {
        Self(bits)
    }
}

// ---------------------------------------------------------------------------
// DeclKind
// ---------------------------------------------------------------------------

/// Declaration kind for an imported constant.
///
/// Distinguishes theorems, definitions, axioms, opaques, and the three
/// inductive-family declaration kinds (inductive types, constructors,
/// recursors). Stored as a single byte in the `MathverseConstantHeader`.
///
/// Value 0 (`Theorem`) is the default, preserving backward compatibility
/// with shards written before `decl_kind` was introduced (the `_pad` byte
/// was always zeroed).
#[repr(u8)]
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum DeclKind {
    Theorem = 0,
    Definition = 1,
    Axiom = 2,
    Opaque = 3,
    Inductive = 4,
    Constructor = 5,
    Recursor = 6,
    /// Quotient type (Quot, Quot.mk, Quot.ind, Quot.lift).
    Quot = 7,
}

impl TryFrom<u8> for DeclKind {
    type Error = u8;

    fn try_from(value: u8) -> Result<Self, Self::Error> {
        match value {
            0 => Ok(Self::Theorem),
            1 => Ok(Self::Definition),
            2 => Ok(Self::Axiom),
            3 => Ok(Self::Opaque),
            4 => Ok(Self::Inductive),
            5 => Ok(Self::Constructor),
            6 => Ok(Self::Recursor),
            7 => Ok(Self::Quot),
            other => Err(other),
        }
    }
}

// ---------------------------------------------------------------------------
// MathverseConstantHeader
// ---------------------------------------------------------------------------

/// 64 bytes per constant. Trust-critical metadata on the hot path.
///
/// Designed for direct mmap access with no deserialization. All fields are
/// fixed-size and aligned for zero-copy reads.
///
/// **v2 layout (64 bytes):** Added `level_params_start`, `level_params_count`
/// for declaration-level universe parameter names (indices into string table),
/// and `levels_list_idx` for per-expression universe level arguments (index
/// into the levels-list pool section).
#[repr(C, align(64))]
#[derive(Clone, Copy, Debug)]
pub struct MathverseConstantHeader {
    /// Index into the shard string table for the constant name.
    pub name_idx: StringIdx,
    /// Index into the FlatExpr arena for the constant's type.
    pub type_idx: ExprIdx,
    /// Index into the FlatExpr arena for the constant's value.
    /// `NO_VALUE` (u32::MAX) means axiomatized (no proof term).
    pub value_idx: ExprIdx,
    /// Source proof system.
    pub source_system: u8,
    /// Trust level.
    pub import_confidence: u8,
    /// Content domain classification.
    pub content_domain: u8,
    /// Declaration kind (theorem, definition, axiom, inductive, etc.).
    /// Replaces the former `_pad` byte. Old shards that zeroed this field
    /// are read as `DeclKind::Theorem` (discriminant 0), which is correct
    /// for the pre-existing behavior where everything was treated as
    /// theorem/axiom.
    pub decl_kind: u8,
    /// Axiom profile bitvector (transitive closure of all axiom dependencies).
    pub axiom_profile: AxiomProfile,
    /// Blake3 hash of the provenance sidecar entry, truncated to 4 bytes.
    /// Used for drift detection between hot headers and cold provenance.
    pub sidecar_digest: u32,
    /// Index into the provenance sidecar for detailed import metadata.
    pub provenance_idx: ProvenanceIdx,
    // --- v2 fields (bytes 32..63) ---
    /// Start index into the shard string table for the declaration's universe
    /// level parameter names. The names occupy string table slots
    /// `[level_params_start .. level_params_start + level_params_count)`.
    pub level_params_start: StringIdx,
    /// Number of declaration-level universe parameter names.
    pub level_params_count: u16,
    /// Reserved v2 metadata bytes.
    ///
    /// Byte layout currently used:
    /// - byte 0: inductive metadata version
    /// - byte 1: inductive metadata flags
    /// - bytes 2..6: optional little-endian `InductiveDecl.num_params`
    /// - bytes 6..10: optional little-endian string-table start for
    ///   `InductiveVal.all_names`
    /// - bytes 10..12: optional little-endian `InductiveVal.all_names` count
    /// - byte 12: reducibility tag (0x80 | tag); 0 = unset
    /// - bytes 13..17: `Regular` height (u32 LE)
    /// - bytes 17..25: 8-byte reconstruction digest (corruption tripwire AND a
    ///   load-time arena-binding gate); 0 = unset
    /// - byte 25: Lean `DefinitionSafety` tag (0x80 | tag, tag ∈ {0=safe,
    ///   1=unsafe, 2=partial}) for `DeclKind::Definition` headers; 0 = unset
    ///   (legacy shard / non-definition) ⇒ treated as safe — today's behavior.
    ///   See [`Self::set_definition_safety`].
    pub _pad2: [u8; 26],
}

impl MathverseConstantHeader {
    pub const SIZE: usize = 64;

    /// Size of the legacy (v1) 32-byte header for backward compatibility.
    pub const LEGACY_SIZE: usize = 32;

    const INDUCTIVE_METADATA_VERSION: u8 = 1;
    const INDUCTIVE_METADATA_VERSION_OFFSET: usize = 0;
    const INDUCTIVE_METADATA_FLAGS_OFFSET: usize = 1;
    const INDUCTIVE_METADATA_NUM_PARAMS_OFFSET: usize = 2;
    const INDUCTIVE_METADATA_ALL_NAMES_START_OFFSET: usize = 6;
    const INDUCTIVE_METADATA_ALL_NAMES_COUNT_OFFSET: usize = 10;
    const INDUCTIVE_METADATA_HAS_NUM_PARAMS: u8 = 1 << 0;
    const INDUCTIVE_METADATA_HAS_ALL_NAMES: u8 = 1 << 1;
    /// `_pad2` byte holding the reducibility tag (0x80 | tag) — see
    /// `ShardWriter::set_constant_reducibility`. 0 = unset (legacy).
    const REDUCIBILITY_TAG_OFFSET: usize = 12;
    /// `_pad2` bytes holding the `Regular` height (u32 LE).
    const REDUCIBILITY_HEIGHT_OFFSET: usize = 13;
    /// `_pad2` bytes 17..25 holding the 8-byte reconstruction digest — see
    /// `ShardWriter::set_constant_recon_digest`. All-zero == unset. 64-bit
    /// CORRUPTION tripwire (collision ~2^-64), NOT a tamper boundary against a
    /// fully-malicious attacker. Footer-hashed, and now ALSO recomputed at load
    /// time by `closure_load::verify_closure_shards_against_oleans` (a real
    /// load-time gate binding the served arena to the verified content).
    const RECON_DIGEST_OFFSET: usize = 17;
    const RECON_DIGEST_LEN: usize = 8;
    /// `_pad2` byte holding the Lean `DefinitionSafety` tag (0x80 | tag) for
    /// `DeclKind::Definition` headers — see [`Self::set_definition_safety`] /
    /// `ShardWriter::set_constant_definition_safety`. 0 = unset (legacy shard /
    /// non-definition) ⇒ treated as safe.
    const DEFINITION_SAFETY_OFFSET: usize = 25;

    /// Decode the kernel `Reducibility` recorded by
    /// `ShardWriter::set_constant_reducibility`, or `None` for a legacy shard
    /// that never wrote it (byte is 0 / high bit clear) — the caller then falls
    /// back to a decl_kind heuristic.
    #[inline]
    pub fn reducibility(&self) -> Option<clean_kernel::env::Reducibility> {
        use clean_kernel::env::Reducibility;
        let b = self._pad2[Self::REDUCIBILITY_TAG_OFFSET];
        if b & 0x80 == 0 {
            return None;
        }
        let height = u32::from_le_bytes([
            self._pad2[Self::REDUCIBILITY_HEIGHT_OFFSET],
            self._pad2[Self::REDUCIBILITY_HEIGHT_OFFSET + 1],
            self._pad2[Self::REDUCIBILITY_HEIGHT_OFFSET + 2],
            self._pad2[Self::REDUCIBILITY_HEIGHT_OFFSET + 3],
        ]);
        Some(match b & 0x7F {
            0 => Reducibility::Reducible,
            1 => Reducibility::Regular(height),
            2 => Reducibility::Irreducible,
            3 => Reducibility::Opaque,
            _ => return None,
        })
    }

    /// Decode the 8-byte reconstruction digest, or `None` when unset (all zero).
    /// 64-bit CORRUPTION tripwire (NOT a tamper boundary), now ALSO a real
    /// load-time gate — see [`Self::RECON_DIGEST_OFFSET`].
    #[inline]
    pub(crate) fn recon_digest(&self) -> Option<[u8; 8]> {
        let start = Self::RECON_DIGEST_OFFSET;
        let mut d = [0u8; Self::RECON_DIGEST_LEN];
        d.copy_from_slice(&self._pad2[start..start + Self::RECON_DIGEST_LEN]);
        if d == [0u8; 8] {
            None
        } else {
            Some(d)
        }
    }

    /// Store the 8-byte reconstruction digest into `_pad2[17..25]`.
    #[inline]
    pub(crate) fn set_recon_digest(&mut self, digest: [u8; 8]) {
        let start = Self::RECON_DIGEST_OFFSET;
        self._pad2[start..start + Self::RECON_DIGEST_LEN].copy_from_slice(&digest);
    }

    /// Decode the Lean `DefinitionSafety` recorded by
    /// [`Self::set_definition_safety`], or `None` for a legacy shard / a
    /// non-definition header that never wrote it (byte 0 / high bit clear) —
    /// callers then treat the constant as `safe`, which is exactly the
    /// pre-existing behavior for every shard written before this byte existed.
    #[inline]
    pub fn definition_safety(&self) -> Option<clean_olean::DefinitionSafety> {
        let b = self._pad2[Self::DEFINITION_SAFETY_OFFSET];
        if b & 0x80 == 0 {
            return None;
        }
        clean_olean::DefinitionSafety::from_tag(u64::from(b & 0x7F))
    }

    /// Record the Lean `DefinitionSafety` flag (`safe` / `unsafe` / `partial`)
    /// carried by a `DeclKind::Definition` header, as `0x80 | tag` in
    /// `_pad2[25]` (0 = unset ⇒ safe, so legacy shards keep today's behavior).
    ///
    /// Lean `unsafe def`s bypass termination/positivity checking and are
    /// structurally barred from proofs by Lean's kernel, so they can never
    /// carry proof-grade trust; the incremental replay reads this flag back to
    /// route them to the trusted-context `UnsafeAccepted` lane instead of a
    /// masked axiom fallback.
    #[inline]
    pub fn set_definition_safety(&mut self, safety: clean_olean::DefinitionSafety) {
        // `to_tag()` ∈ {0, 1, 2} — always fits the low 7 bits.
        self._pad2[Self::DEFINITION_SAFETY_OFFSET] = 0x80 | (safety.to_tag() as u8);
    }

    /// Check if this constant has a proof term (is not axiomatized).
    #[inline]
    pub const fn has_value(&self) -> bool {
        self.value_idx != NO_VALUE
    }

    /// Get the declaration kind as an enum.
    #[inline]
    pub fn decl_kind(&self) -> Result<DeclKind, u8> {
        DeclKind::try_from(self.decl_kind)
    }

    /// Check if this constant is an inductive-family declaration
    /// (inductive type, constructor, or recursor).
    #[inline]
    pub const fn is_inductive_family(&self) -> bool {
        matches!(
            self.decl_kind,
            4..=6 // Inductive | Constructor | Recursor
        )
    }

    /// Get the source system as an enum.
    #[inline]
    pub fn source(&self) -> Result<SourceSystem, u8> {
        SourceSystem::try_from(self.source_system)
    }

    /// Get the import confidence as an enum.
    #[inline]
    pub fn confidence(&self) -> Result<ImportConfidence, u8> {
        ImportConfidence::try_from(self.import_confidence)
    }

    /// Get the content domain as an enum.
    #[inline]
    pub fn domain(&self) -> Result<ContentDomain, u8> {
        ContentDomain::try_from(self.content_domain)
    }

    /// Get the axiom profile.
    #[inline]
    pub const fn profile(&self) -> AxiomProfile {
        self.axiom_profile
    }

    /// Check if this constant is trust-gated.
    #[inline]
    pub const fn is_trust_gated(&self) -> bool {
        self.axiom_profile.is_trust_gated()
    }

    /// Check if this constant has declaration-level universe parameters.
    #[inline]
    pub const fn has_level_params(&self) -> bool {
        self.level_params_count > 0
    }

    /// Store typed shard metadata for `InductiveDecl.num_params`.
    ///
    /// This is meaningful on `DeclKind::Inductive` headers and lets incremental
    /// replay rebuild parameterized or indexed single-type inductive families
    /// through checked `Environment::add_inductive`.
    #[inline]
    pub fn set_inductive_decl_num_params(&mut self, num_params: u32) {
        self._pad2[Self::INDUCTIVE_METADATA_VERSION_OFFSET] = Self::INDUCTIVE_METADATA_VERSION;
        self._pad2[Self::INDUCTIVE_METADATA_FLAGS_OFFSET] |=
            Self::INDUCTIVE_METADATA_HAS_NUM_PARAMS;
        let start = Self::INDUCTIVE_METADATA_NUM_PARAMS_OFFSET;
        self._pad2[start..start + 4].copy_from_slice(&num_params.to_le_bytes());
    }

    /// Read typed shard metadata for `InductiveDecl.num_params`, when present.
    #[inline]
    pub fn inductive_decl_num_params(&self) -> Option<u32> {
        if self._pad2[Self::INDUCTIVE_METADATA_VERSION_OFFSET] != Self::INDUCTIVE_METADATA_VERSION {
            return None;
        }
        if (self._pad2[Self::INDUCTIVE_METADATA_FLAGS_OFFSET]
            & Self::INDUCTIVE_METADATA_HAS_NUM_PARAMS)
            == 0
        {
            return None;
        }
        let start = Self::INDUCTIVE_METADATA_NUM_PARAMS_OFFSET;
        Some(u32::from_le_bytes([
            self._pad2[start],
            self._pad2[start + 1],
            self._pad2[start + 2],
            self._pad2[start + 3],
        ]))
    }

    /// Store typed shard metadata for the mutual `InductiveVal.all_names` block.
    ///
    /// The names are stored as a contiguous string-table run. This metadata is
    /// meaningful on `DeclKind::Inductive` headers and lets incremental replay
    /// rebuild the full `InductiveDecl.types` block for simple mutual families.
    #[inline]
    pub fn set_inductive_decl_all_names(&mut self, start: StringIdx, count: u16) {
        self._pad2[Self::INDUCTIVE_METADATA_VERSION_OFFSET] = Self::INDUCTIVE_METADATA_VERSION;
        self._pad2[Self::INDUCTIVE_METADATA_FLAGS_OFFSET] |= Self::INDUCTIVE_METADATA_HAS_ALL_NAMES;
        let start_offset = Self::INDUCTIVE_METADATA_ALL_NAMES_START_OFFSET;
        self._pad2[start_offset..start_offset + 4].copy_from_slice(&start.to_le_bytes());
        let count_offset = Self::INDUCTIVE_METADATA_ALL_NAMES_COUNT_OFFSET;
        self._pad2[count_offset..count_offset + 2].copy_from_slice(&count.to_le_bytes());
    }

    /// Read typed shard metadata for `InductiveVal.all_names`, when present.
    #[inline]
    pub fn inductive_decl_all_names_block(&self) -> Option<(StringIdx, u16)> {
        if self._pad2[Self::INDUCTIVE_METADATA_VERSION_OFFSET] != Self::INDUCTIVE_METADATA_VERSION {
            return None;
        }
        if (self._pad2[Self::INDUCTIVE_METADATA_FLAGS_OFFSET]
            & Self::INDUCTIVE_METADATA_HAS_ALL_NAMES)
            == 0
        {
            return None;
        }
        let start_offset = Self::INDUCTIVE_METADATA_ALL_NAMES_START_OFFSET;
        let count_offset = Self::INDUCTIVE_METADATA_ALL_NAMES_COUNT_OFFSET;
        Some((
            u32::from_le_bytes([
                self._pad2[start_offset],
                self._pad2[start_offset + 1],
                self._pad2[start_offset + 2],
                self._pad2[start_offset + 3],
            ]),
            u16::from_le_bytes([self._pad2[count_offset], self._pad2[count_offset + 1]]),
        ))
    }

    /// Serialize to bytes (for shard writing).
    pub fn to_bytes(&self) -> [u8; Self::SIZE] {
        let mut buf = [0u8; Self::SIZE];
        buf[0..4].copy_from_slice(&self.name_idx.to_le_bytes());
        buf[4..8].copy_from_slice(&self.type_idx.to_le_bytes());
        buf[8..12].copy_from_slice(&self.value_idx.to_le_bytes());
        buf[12] = self.source_system;
        buf[13] = self.import_confidence;
        buf[14] = self.content_domain;
        buf[15] = self.decl_kind;
        buf[16..24].copy_from_slice(&self.axiom_profile.0.to_le_bytes());
        buf[24..28].copy_from_slice(&self.sidecar_digest.to_le_bytes());
        buf[28..32].copy_from_slice(&self.provenance_idx.to_le_bytes());
        // v2 fields
        buf[32..36].copy_from_slice(&self.level_params_start.to_le_bytes());
        buf[36..38].copy_from_slice(&self.level_params_count.to_le_bytes());
        buf[38..64].copy_from_slice(&self._pad2);
        buf
    }

    /// Deserialize from bytes (for shard reading).
    pub fn from_bytes(buf: &[u8; Self::SIZE]) -> Self {
        Self {
            name_idx: u32::from_le_bytes([buf[0], buf[1], buf[2], buf[3]]),
            type_idx: u32::from_le_bytes([buf[4], buf[5], buf[6], buf[7]]),
            value_idx: u32::from_le_bytes([buf[8], buf[9], buf[10], buf[11]]),
            source_system: buf[12],
            import_confidence: buf[13],
            content_domain: buf[14],
            decl_kind: buf[15],
            axiom_profile: AxiomProfile(u64::from_le_bytes([
                buf[16], buf[17], buf[18], buf[19], buf[20], buf[21], buf[22], buf[23],
            ])),
            sidecar_digest: u32::from_le_bytes([buf[24], buf[25], buf[26], buf[27]]),
            provenance_idx: u32::from_le_bytes([buf[28], buf[29], buf[30], buf[31]]),
            level_params_start: u32::from_le_bytes([buf[32], buf[33], buf[34], buf[35]]),
            level_params_count: u16::from_le_bytes([buf[36], buf[37]]),
            _pad2: buf[38..64].try_into().expect("constant header pad length"),
        }
    }

    /// Deserialize from legacy 32-byte header (backward compat).
    pub fn from_legacy_bytes(buf: &[u8; Self::LEGACY_SIZE]) -> Self {
        Self {
            name_idx: u32::from_le_bytes([buf[0], buf[1], buf[2], buf[3]]),
            type_idx: u32::from_le_bytes([buf[4], buf[5], buf[6], buf[7]]),
            value_idx: u32::from_le_bytes([buf[8], buf[9], buf[10], buf[11]]),
            source_system: buf[12],
            import_confidence: buf[13],
            content_domain: buf[14],
            // allow: decl_kind-literal
            // Legacy 32-byte headers pre-date the `decl_kind` byte; the field
            // is reconstructed as 0 (= `DeclKind::Theorem`) for backward
            // compatibility only. New writers must populate `decl_kind` from
            // the source constant's kind via `lean4::olean::decl_kind::decl_kind_*`.
            decl_kind: 0,
            axiom_profile: AxiomProfile(u64::from_le_bytes([
                buf[16], buf[17], buf[18], buf[19], buf[20], buf[21], buf[22], buf[23],
            ])),
            sidecar_digest: u32::from_le_bytes([buf[24], buf[25], buf[26], buf[27]]),
            provenance_idx: u32::from_le_bytes([buf[28], buf[29], buf[30], buf[31]]),
            level_params_start: 0,
            level_params_count: 0,
            _pad2: [0u8; 26],
        }
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_mathverse_constant_header_size() {
        assert_eq!(size_of::<MathverseConstantHeader>(), 64);
        assert_eq!(align_of::<MathverseConstantHeader>(), 64);
    }

    /// The 8-byte recon_digest round-trips through `_pad2[17..25]`; all-zero
    /// decodes as `None` (unset); and it does NOT collide with the reducibility
    /// bytes (12..17) or the inductive metadata bytes (0..12).
    #[test]
    fn test_recon_digest_round_trip_and_isolation() {
        let mut h = MathverseConstantHeader {
            name_idx: 1,
            type_idx: 2,
            value_idx: 3,
            source_system: 0,
            import_confidence: 0,
            content_domain: 0,
            decl_kind: DeclKind::Theorem as u8,
            axiom_profile: AxiomProfile::NONE,
            sidecar_digest: 0,
            provenance_idx: 0,
            level_params_start: 0,
            level_params_count: 0,
            _pad2: [0u8; 26],
        };
        assert_eq!(h.recon_digest(), None, "unset == None");

        // Set reducibility + inductive metadata first to prove isolation.
        h._pad2[12] = 0x80 | 1; // Regular tag
        h._pad2[13..17].copy_from_slice(&7u32.to_le_bytes()); // height 7
        h.set_inductive_decl_num_params(99);

        let digest = [9u8, 8, 7, 6, 5, 4, 3, 2];
        h.set_recon_digest(digest);
        assert_eq!(h.recon_digest(), Some(digest), "round-trips");
        // Reducibility + inductive metadata are untouched by the digest write.
        assert_eq!(h._pad2[12], 0x80 | 1);
        assert_eq!(
            u32::from_le_bytes([h._pad2[13], h._pad2[14], h._pad2[15], h._pad2[16]]),
            7
        );
        assert_eq!(h.inductive_decl_num_params(), Some(99));
        // Byte 25 stays reserved/zero.
        assert_eq!(h._pad2[25], 0);
    }

    #[test]
    fn test_header_round_trip() {
        let header = MathverseConstantHeader {
            name_idx: 42,
            type_idx: 100,
            value_idx: 200,
            source_system: SourceSystem::Coq as u8,
            import_confidence: ImportConfidence::Translated as u8,
            content_domain: ContentDomain::PureMath as u8,
            decl_kind: DeclKind::Definition as u8,
            axiom_profile: AxiomProfile::CHOICE | AxiomProfile::LEM,
            sidecar_digest: 0xDEAD_BEEF,
            provenance_idx: 500,
            level_params_start: 10,
            level_params_count: 3,
            _pad2: [0u8; 26],
        };

        let bytes = header.to_bytes();
        let restored = MathverseConstantHeader::from_bytes(&bytes);

        assert_eq!(header.name_idx, restored.name_idx);
        assert_eq!(header.type_idx, restored.type_idx);
        assert_eq!(header.value_idx, restored.value_idx);
        assert_eq!(header.source_system, restored.source_system);
        assert_eq!(header.import_confidence, restored.import_confidence);
        assert_eq!(header.content_domain, restored.content_domain);
        assert_eq!(header.decl_kind, restored.decl_kind);
        assert_eq!(header.axiom_profile, restored.axiom_profile);
        assert_eq!(header.sidecar_digest, restored.sidecar_digest);
        assert_eq!(header.provenance_idx, restored.provenance_idx);
        assert_eq!(header.level_params_start, restored.level_params_start);
        assert_eq!(header.level_params_count, restored.level_params_count);
    }

    #[test]
    fn test_verify_incremental_inductive_num_params_metadata_round_trip() {
        let mut header = MathverseConstantHeader {
            name_idx: 42,
            type_idx: 100,
            value_idx: NO_VALUE,
            source_system: SourceSystem::Lean4 as u8,
            import_confidence: ImportConfidence::KernelVerified as u8,
            content_domain: ContentDomain::PureMath as u8,
            decl_kind: DeclKind::Inductive as u8,
            axiom_profile: AxiomProfile::NONE,
            sidecar_digest: 0,
            provenance_idx: 0,
            level_params_start: 10,
            level_params_count: 1,
            _pad2: [0u8; 26],
        };

        assert_eq!(header.inductive_decl_num_params(), None);
        assert_eq!(header.inductive_decl_all_names_block(), None);
        header.set_inductive_decl_num_params(7);
        header.set_inductive_decl_all_names(25, 2);

        let bytes = header.to_bytes();
        let restored = MathverseConstantHeader::from_bytes(&bytes);

        assert_eq!(restored.inductive_decl_num_params(), Some(7));
        assert_eq!(restored.inductive_decl_all_names_block(), Some((25, 2)));
        assert_eq!(restored._pad2[0], 1);
        assert_eq!(restored._pad2[1] & 1, 1);
        assert_eq!(restored._pad2[1] & 2, 2);
    }

    #[test]
    fn test_axiomatized_constant() {
        let header = MathverseConstantHeader {
            name_idx: 0,
            type_idx: 0,
            value_idx: NO_VALUE,
            source_system: SourceSystem::Isabelle as u8,
            import_confidence: ImportConfidence::Axiomatized as u8,
            content_domain: ContentDomain::PureMath as u8,
            decl_kind: DeclKind::Axiom as u8,
            axiom_profile: AxiomProfile::AXIOMATIZED | AxiomProfile::HOL_AXIOMS,
            sidecar_digest: 0,
            provenance_idx: 0,
            level_params_start: 0,
            level_params_count: 0,
            _pad2: [0u8; 26],
        };

        assert!(!header.has_value());
        assert!(header.is_trust_gated());
    }

    #[test]
    fn test_decl_kind_round_trip() {
        for val in 0..=7u8 {
            let kind = DeclKind::try_from(val).unwrap();
            assert_eq!(kind as u8, val);
        }
        assert!(DeclKind::try_from(8u8).is_err());
    }

    #[test]
    fn test_decl_kind_inductive_family() {
        let make_header = |dk: DeclKind| MathverseConstantHeader {
            name_idx: 0,
            type_idx: 0,
            value_idx: NO_VALUE,
            source_system: 0,
            import_confidence: 0,
            content_domain: 0,
            decl_kind: dk as u8,
            axiom_profile: AxiomProfile::NONE,
            sidecar_digest: 0,
            provenance_idx: 0,
            level_params_start: 0,
            level_params_count: 0,
            _pad2: [0u8; 26],
        };

        assert!(!make_header(DeclKind::Theorem).is_inductive_family());
        assert!(!make_header(DeclKind::Definition).is_inductive_family());
        assert!(!make_header(DeclKind::Axiom).is_inductive_family());
        assert!(!make_header(DeclKind::Opaque).is_inductive_family());
        assert!(make_header(DeclKind::Inductive).is_inductive_family());
        assert!(make_header(DeclKind::Constructor).is_inductive_family());
        assert!(make_header(DeclKind::Recursor).is_inductive_family());
        assert!(!make_header(DeclKind::Quot).is_inductive_family());
    }

    #[test]
    fn test_backward_compat_zero_pad_is_theorem() {
        // Old shards zeroed the _pad byte, which should deserialize as
        // DeclKind::Theorem (discriminant 0).
        let kind = DeclKind::try_from(0u8).unwrap();
        assert_eq!(kind, DeclKind::Theorem);
    }

    #[test]
    fn test_axiom_profile_operations() {
        let p1 = AxiomProfile::CHOICE | AxiomProfile::LEM;
        let p2 = AxiomProfile::PROP_EXT | AxiomProfile::FUNC_EXT;

        assert!(p1.has(AxiomProfile::CHOICE));
        assert!(p1.has(AxiomProfile::LEM));
        assert!(!p1.has(AxiomProfile::PROP_EXT));

        let union = p1.union(p2);
        assert!(union.has(AxiomProfile::CHOICE));
        assert!(union.has(AxiomProfile::PROP_EXT));
        assert!(!union.is_trust_gated());
        assert!(!union.is_pure());

        assert!(AxiomProfile::NONE.is_pure());
        assert!(!AxiomProfile::NONE.is_trust_gated());

        let gated = AxiomProfile::AXIOMATIZED;
        assert!(gated.is_trust_gated());
    }

    #[test]
    fn test_axiom_profile_union_bitor() {
        let a = AxiomProfile::CLASSICAL;
        let b = AxiomProfile::FUNC_EXT;
        let c = a | b;
        assert!(c.contains(a));
        assert!(c.contains(b));
        // CLASSICAL == CHOICE (same bit), so test with UNIVALENCE instead
        assert!(!c.contains(AxiomProfile::UNIVALENCE));
        assert!(!c.is_kernel_verified());
        assert_eq!(c.axiom_count(), 2);
    }

    #[test]
    fn test_axiom_profile_superset() {
        let parent = AxiomProfile::CLASSICAL | AxiomProfile::HOL_AXIOMS;
        let child = AxiomProfile::CLASSICAL;
        assert!(parent.is_superset_of(child));
        assert!(!child.is_superset_of(parent));
    }

    #[test]
    fn test_kernel_verified() {
        assert!(AxiomProfile::NONE.is_kernel_verified());
        assert!(!AxiomProfile::CLASSICAL.is_kernel_verified());
    }

    #[test]
    fn test_source_system_round_trip() {
        for val in 0..=69u8 {
            let sys = SourceSystem::try_from(val).unwrap();
            assert_eq!(sys as u8, val);
        }
        assert!(SourceSystem::try_from(70u8).is_err());
    }

    #[test]
    fn test_import_confidence_ordering() {
        assert!(ImportConfidence::KernelVerified < ImportConfidence::KernelBridged);
        assert!(ImportConfidence::KernelBridged < ImportConfidence::SourceVerified);
        assert!(ImportConfidence::SourceVerified < ImportConfidence::Translated);
        assert!(ImportConfidence::Translated < ImportConfidence::Axiomatized);
        assert!(ImportConfidence::Axiomatized < ImportConfidence::Unverified);
    }

    #[test]
    fn test_import_confidence_kernel_bridged_round_trip_and_rank() {
        // Stable discriminant 8, round-trips through the byte form.
        let val = ImportConfidence::KernelBridged as u8;
        assert_eq!(val, 8);
        let restored = ImportConfidence::try_from(val).unwrap();
        assert_eq!(restored, ImportConfidence::KernelBridged);

        // Trust ordering: immediately below KernelVerified, above every
        // import-confidence tier AND the conditional tier — because the bridge is
        // an end-to-end, foundational-closure kernel proof (no trusted-ledger
        // axiom in its closure). It is NEVER KernelVerified: the residual
        // distinction is provenance, not trust.
        assert!(ImportConfidence::KernelVerified < ImportConfidence::KernelBridged);
        assert!(ImportConfidence::KernelBridged < ImportConfidence::SourceVerified);
        assert!(ImportConfidence::KernelBridged < ImportConfidence::Translated);
        assert!(ImportConfidence::KernelBridged < ImportConfidence::KernelCheckedConditional);
        assert!(ImportConfidence::KernelBridged < ImportConfidence::Axiomatized);
        assert!(ImportConfidence::KernelBridged < ImportConfidence::Unverified);
        assert_ne!(
            ImportConfidence::KernelBridged,
            ImportConfidence::KernelVerified
        );
    }

    #[test]
    fn test_import_confidence_source_verified_round_trip() {
        let val = ImportConfidence::SourceVerified as u8;
        assert_eq!(val, 6);
        let restored = ImportConfidence::try_from(val).unwrap();
        assert_eq!(restored, ImportConfidence::SourceVerified);
    }

    #[test]
    fn test_import_confidence_kernel_checked_conditional_round_trip_and_rank() {
        // Stable discriminant 7, round-trips through the byte form.
        let val = ImportConfidence::KernelCheckedConditional as u8;
        assert_eq!(val, 7);
        let restored = ImportConfidence::try_from(val).unwrap();
        assert_eq!(restored, ImportConfidence::KernelCheckedConditional);

        // Trust ordering: strictly weaker than KernelVerified / SourceVerified /
        // Translated, but stronger than Axiomatized / Unverified. It is NEVER
        // KernelVerified — the whole point of the second tier.
        assert!(ImportConfidence::KernelVerified < ImportConfidence::KernelCheckedConditional);
        assert!(ImportConfidence::SourceVerified < ImportConfidence::KernelCheckedConditional);
        assert!(ImportConfidence::Translated < ImportConfidence::KernelCheckedConditional);
        assert!(ImportConfidence::KernelCheckedConditional < ImportConfidence::Axiomatized);
        assert!(ImportConfidence::KernelCheckedConditional < ImportConfidence::Unverified);
        assert_ne!(
            ImportConfidence::KernelCheckedConditional,
            ImportConfidence::KernelVerified
        );
    }
}
