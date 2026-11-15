// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! CROSS-MODULE IMPORT: the first real producer of `trust_ir::Module::imports`.
//!
//! # What this is
//!
//! Given a client module this backend has just emitted and the DECODED
//! dependency artifacts the invoker named, [`link_imported_modules`] writes the
//! cross-crate identity rows — and, where and only where it can re-earn it, the
//! cross-crate PROOF row: a local `TranslationValidation` restatement grounded
//! by a `ProofEvidence::InheritedFromCallee { external: Some(..) }` certificate.
//!
//! Until now `Module.imports` had no producer anywhere in the stack. The schema
//! shipped in trust-ir binary v41, the consumer
//! (`trust_ir_build::validate_linked_module`) shipped with its own suite, and
//! nothing wrote a row. This is the writer.
//!
//! # Every value here is MEASURED
//!
//! That is the whole discipline of this module, and it is worth being explicit
//! about what it rules out:
//!
//! * `ModuleImport::digest` is [`trust_ir::Module::stable_digest`] computed over
//!   the DECODE of the artifact that was actually read. It is never taken from a
//!   filename, a manifest, a sidecar, or the dependency's own claim about
//!   itself. A consumer re-computes the same function over the same bytes, so
//!   the row is checkable rather than asserted.
//! * `ModuleImport::name` is the decoded `Module::name`. It is METADATA, not
//!   identity: `ModuleSet` keys on the digest and ignores the name, so a
//!   dependency renamed but byte-identical still resolves and a dependency
//!   rebuilt under the same name does not.
//! * `ModuleImport::producer` is written only when every producer-bearing
//!   function in the decode records the SAME producer and at least one does.
//!   `None` is never written to mean agreement — a dependency that records no
//!   producer is refused with [`LinkRefusal::ProducerUnrecorded`], because the
//!   consumer's own rule fails closed on absence and guessing is worse than
//!   refusing.
//! * `TargetInfo` must be present on BOTH sides and equal. Absence is not
//!   agreement ([`LinkRefusal::TargetMismatch`]).
//!
//! # An unresolvable row is not written
//!
//! A proof claim is written only when all of the following were established, in
//! this order, by measurement:
//!
//! 1. the far symbol is a DEFINITION — exactly one far `Function` across the
//!    supplied artifacts DEFINES the link-time name (another artifact may
//!    DECLARE it: that is its own import of the symbol), and its linkage is
//!    externally visible;
//! 2. the symbol is in the fragment whose TV statement the importer can
//!    RE-DERIVE from the far signature alone (uniform unsigned width);
//! 3. exactly one far obligation is a `Certified` `TranslationValidation`
//!    scoped to that function;
//! 4. the formula the importer DERIVES from the far `Function::name` and far
//!    `FuncTy` is byte-equal to the formula the dependency recorded. The
//!    importer does not copy A's formula: if it did, the equality
//!    `check_inherited` demands would be vacuous;
//! 5. the far `Certified` label is re-earned by an IN-PROCESS kernel replay of
//!    its `CleanCic` term — the dependency is validated here, under
//!    `RejectingModuleProofAuthority`, and the far certificate's lineage ref
//!    must appear in the replayed set. A status label is not proof authority;
//! 6. the far certificate's recorded COMPARAND (its `context` bytes — the
//!    source definition the dependency's kernel judgment was about) is equal,
//!    byte for byte after the minter's own normalization
//!    (`emit_trust_ir_tv::source_comparand_bytes`), to the comparand the
//!    CLIENT's elaboration of the same symbol yields
//!    ([`WantedSymbol::client_source`]). Steps 1–5 prove only that the far
//!    function denotes SOME recorded comparand; a dependency certified,
//!    honestly, against a different body of the same signature would back the
//!    client's meaning of the symbol without this step (the F-008 hole, seen
//!    from the importer). No client source, or a different one, is an
//!    identity row and no claim.
//!
//! If any of 2–6 fails, the symbol still gets its IDENTITY rows (the import row
//! and a typed body-less declaration) and NO proof claim at all: no obligation,
//! no certificate, no `ExternRef`. A missing row is honest; a wrong row is not.
//! If 1 fails there is nothing to declare and the symbol is declined.
//!
//! Identity rows survive only for a dependency that validates ON ITS OWN. Since
//! trust-ir WS1.7 (da6ff616) the linked walk recursively validates EVERY import
//! row, cited or not, so a dependency whose far certificate fails its own
//! validation (a replay failure, or a lineage no longer bound to its
//! obligation) is not demoted to identity-only: the final gate below refuses
//! the whole link and nothing is written (pinned by
//! `a_far_formula_mutated_by_one_byte_is_refused_at_the_producer` in
//! `emit_trust_ir_link_tests.rs`).
//!
//! # Where it is called from
//!
//! `clean compile --emit trustir-bin --link-artifact <PATH>` (clean-cli,
//! WS6.8) decodes each artifact ([`LinkedArtifact::decode`]), routes every
//! symbol exactly one artifact defines to an import rather than a definition
//! ([`importable_symbols`]), has the emitter declare those callees at the far
//! signature (refusing the compile when the client's call shape disagrees:
//! [`LinkRefusal::CallShapeDisagreesWithFarSignature`]), and then calls
//! [`link_imported_modules_for_cli`] with the client's own elaboration of each
//! imported symbol. The emitter's declaration is ADOPTED here, never
//! duplicated. Without `--link-artifact` nothing changes: the closure is
//! compiled into one self-contained module, which is sound and simply carries
//! no cross-module identity.
//!
//! # The producer's last act is the consumer's own check
//!
//! [`link_imported_modules`] finishes by running
//! `validate_linked_module(&client, &ModuleSet(deps), &RejectingModuleProofAuthority)`
//! — the same call a consumer makes — and refuses the whole link if it is not
//! `is_ok()`. So nothing is written that a consumer would not re-earn.

use std::collections::{BTreeMap, BTreeSet};

use trust_ir::proof::{
    ObligationKind, ProofCertificate, ProofEvidence, ProofFormula, ProofObligation, ProofStatus,
    RejectingModuleProofAuthority,
};
use trust_ir::value::{FuncId, ImportId, ProofId};
use trust_ir::{ExternRef, Linkage, ModuleImport, Producer};
use trust_ir_build::{validate_linked_module, ModuleSet};

use clean_kernel::Expr;

/// The signature types [`ArtifactLookup::Import`] carries, re-exported for the
/// same reason.
pub use trust_ir::ty::{FuncTy, Ty};
/// The trust-ir module and function types, re-exported for the CLI caller
/// (clean-cli has no direct trust-ir dependency; the pin is a transaction whose
/// legs are counted, so a new edge is not added for a type name).
pub use trust_ir::{Function, Module};

// The CLI-facing surface (`clean compile --link-artifact`): artifact decoding,
// the import table, and the entry point. A child module so this file stays
// the producer's discipline; everything is re-exported at its old path.
#[path = "emit_trust_ir_link_cli.rs"]
mod cli;
pub use cli::{
    importable_symbols, link_imported_modules_for_cli,
    link_imported_modules_for_cli_in_environment, link_symbol, linked_verdict, ArtifactLookup,
    LinkedArtifact,
};
pub(crate) use cli::{render_func_ty, WantedSymbol};

/// Why one symbol, or one artifact, was refused. Every arm names a
/// MEASUREMENT that failed, so a refusal is diagnosable rather than a shrug.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum LinkRefusal {
    /// No supplied artifact defines the symbol.
    SymbolNotFound,
    /// Two or more functions across the supplied artifacts DEFINE the
    /// link-time symbol. `Function::name` is normatively the link symbol, so
    /// this is ambiguous by construction and never resolved by picking one.
    /// A body-less DECLARATION of the symbol in another artifact (that
    /// artifact's own import of it) is not a second definer: there is nothing
    /// to pick, and `validate_linked_module` binds a call edge to the one
    /// dependency that DEFINES and exports the symbol in the same way.
    SymbolAmbiguous,
    /// The far site has no body: a re-declaration backs nothing.
    FarSiteIsUnbackedDeclaration,
    /// The far definition is not externally visible, so no client could link it.
    FarSiteNotExternallyVisible(Linkage),
    /// The far signature is outside the fragment whose TV statement can be
    /// re-derived from a signature alone (uniform unsigned integer width).
    OutOfFragment(String),
    /// No producer-bearing function in the dependency, so `ModuleImport::producer`
    /// could only be `None` — which the consumer's rule fails closed on.
    ProducerUnrecorded,
    /// The dependency's functions disagree about their producer.
    ProducerMismatch,
    /// One side has no `TargetInfo`, or the two disagree. Absence is not
    /// agreement.
    TargetMismatch,
    /// No `Certified` `TranslationValidation` obligation is scoped to the far
    /// function, or more than one is.
    FarDischargeNotUnique,
    /// The far obligation records no formula, so there is nothing to restate.
    FarFormulaAbsent,
    /// The formula RE-DERIVED from the far name and signature is not the one the
    /// dependency recorded.
    FarFormulaDisagreesWithSignature,
    /// The far `Certified` label was not re-earned by an in-process kernel
    /// replay: a status label is not proof authority.
    FarDischargeNotGrounded,
    /// The client supplied no elaboration of the symbol, or its elaboration
    /// yields no comparand (outside the fragment), so the far certificate's
    /// recorded comparand cannot be bound to what the CLIENT means by the
    /// symbol. Identity rows only.
    ClientSourceUnavailable(String),
    /// The far certificate's recorded comparand is not, byte for byte, the one
    /// the client's elaboration of the symbol yields: the dependency proved
    /// its function denotes a DIFFERENT source definition than the client's.
    /// Identity rows only — inheriting would back the client's meaning of the
    /// symbol with a proof about another body.
    FarComparandDisagreesWithClientSource,
    /// The client's lowered call shape for an imported symbol — the signature
    /// every client call site was emitted against — is not structurally equal
    /// to the far `FuncTy` (for instance a dependency built under a different
    /// boxing configuration). The COMPILE is refused: the call is never
    /// silently re-boxed, and no module whose call sites disagree with the
    /// far definition is written.
    CallShapeDisagreesWithFarSignature {
        /// The client's lowering of the symbol's signature.
        local: String,
        /// The far definition's signature.
        far: String,
    },
    /// The CLIENT already carries a function with this link-time symbol —
    /// almost always the emitter's boxed `fn(Ptr..) -> Ptr` extern fallback for
    /// a dropped callee.
    ///
    /// Minting a typed declaration beside it would put TWO functions in one
    /// module under one link symbol, which v41's `DuplicateFunctionSymbol` rule
    /// rejects and which `resolve_extern_ref` would see as `SymbolAmbiguous`.
    /// Replacing the fallback is not an option here either: its call sites pass
    /// BOXED arguments, so retyping the declaration without retyping the calls
    /// makes the module fail validation on argument types, so this is a
    /// refusal rather than a rewrite.
    ///
    /// The emitter's typed-import arm (WS6.8,
    /// `TrustIrConfig::imported_callees`) does not reach this refusal: it
    /// declares the symbol at the FAR signature with every call site shaped
    /// against it, and a body-less, claim-free declaration structurally equal
    /// to the far signature is ADOPTED as the import declaration.
    ClientAlreadyDeclaresSymbol,
}

impl std::fmt::Display for LinkRefusal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::SymbolNotFound => write!(f, "no supplied artifact defines this symbol"),
            Self::SymbolAmbiguous => write!(
                f,
                "the link-time symbol is defined more than once across the supplied artifacts"
            ),
            Self::FarSiteIsUnbackedDeclaration => {
                write!(f, "the far site is a declaration, not a definition")
            }
            Self::FarSiteNotExternallyVisible(l) => {
                write!(
                    f,
                    "the far definition has {l:?} linkage, so nothing may link it"
                )
            }
            Self::OutOfFragment(why) => write!(f, "out of the importable fragment: {why}"),
            Self::ProducerUnrecorded => write!(
                f,
                "the dependency records no producer; `ModuleImport::producer` would be `None`, \
                 which is not agreement"
            ),
            Self::ProducerMismatch => {
                write!(
                    f,
                    "the dependency's functions disagree about their producer"
                )
            }
            Self::TargetMismatch => write!(
                f,
                "target identity absent on one side or unequal; absence is not agreement"
            ),
            Self::FarDischargeNotUnique => write!(
                f,
                "the far function has no unique Certified TranslationValidation obligation"
            ),
            Self::FarFormulaAbsent => write!(
                f,
                "the far obligation states no formula; a claim with no statement cannot be restated"
            ),
            Self::FarFormulaDisagreesWithSignature => write!(
                f,
                "the formula re-derived from the far name and signature is not the one recorded"
            ),
            Self::FarDischargeNotGrounded => write!(
                f,
                "the far Certified label was not re-earned by an in-process kernel replay"
            ),
            Self::ClientSourceUnavailable(why) => write!(
                f,
                "the client's own definition of the symbol yields no comparand to bind the far \
                 certificate to ({why})"
            ),
            Self::FarComparandDisagreesWithClientSource => write!(
                f,
                "the far certificate's recorded comparand is not the client's definition of \
                 the symbol: the dependency proved a different body"
            ),
            Self::CallShapeDisagreesWithFarSignature { local, far } => write!(
                f,
                "the client's lowered call shape {local} is not the far signature {far}; the \
                 call is not re-boxed"
            ),
            Self::ClientAlreadyDeclaresSymbol => write!(
                f,
                "the client already declares this link-time symbol (the emitter's boxed \
                 extern fallback); a second row would be a duplicate symbol, and retyping \
                 the existing one without retyping its call sites would not validate"
            ),
        }
    }
}

/// What [`link_imported_modules`] wrote, and what it declined.
#[derive(Debug, Clone, Default)]
pub(crate) struct LinkReport {
    /// One row per artifact actually recorded, with the digest MEASURED for it.
    pub imports: Vec<(ImportId, String, trust_ir::proof::ProofDigest)>,
    /// Symbols that got identity rows AND a re-earned proof claim.
    pub proved: Vec<ImportedSymbol>,
    /// Symbols that got identity rows and NO proof claim, with the reason the
    /// claim could not be established. This is the honest half: the
    /// declaration is real, the proof is absent, and the absence is named.
    pub identity_only: Vec<(ImportedSymbol, LinkRefusal)>,
    /// Symbols nothing could be written for at all.
    pub declined: Vec<(String, LinkRefusal)>,
}

/// One imported symbol, as written into the client.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ImportedSymbol {
    /// The link-time symbol.
    pub symbol: String,
    /// The import row it was resolved through.
    pub import: ImportId,
    /// The local body-less declaration minted for it.
    pub decl: FuncId,
    /// The local restatement obligation, when a proof claim was earned.
    pub restatement: Option<ProofId>,
}

/// Why a whole link attempt was refused, leaving the client UNCHANGED.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum LinkError {
    /// One artifact could not be recorded at all.
    Artifact { path: String, why: LinkRefusal },
    /// The producer's own final gate — the consumer's check — refused the
    /// result. Nothing is written.
    ConsumerRefused(Vec<String>),
}

impl std::fmt::Display for LinkError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Artifact { path, why } => write!(f, "linked artifact {path}: {why}"),
            Self::ConsumerRefused(errors) => write!(
                f,
                "the linked client does not re-earn its own rows ({} refusal(s)): {}",
                errors.len(),
                errors.join("; ")
            ),
        }
    }
}

/// The uniform unsigned width of `ty`, or `None` when it is not one of the
/// fragment's scalar types.
fn uniform_uint_width(ty: &Ty) -> Option<u32> {
    match ty {
        Ty::U8 => Some(8),
        Ty::U16 => Some(16),
        Ty::U32 => Some(32),
        Ty::U64 => Some(64),
        _ => None,
    }
}

/// The importable fragment: every parameter and the single return at ONE
/// unsigned width. This is exactly the shape whose TV statement
/// `clean_reflect::tv_statement_formula` derives from a signature, which is why
/// the narrowing is here and not a matter of taste — outside it the importer
/// would have to COPY the dependency's formula, and the equality
/// `check_inherited` demands would prove nothing.
fn fragment_width(ft: &FuncTy) -> Result<u32, LinkRefusal> {
    if ft.is_vararg {
        return Err(LinkRefusal::OutOfFragment("vararg signature".to_string()));
    }
    let [ret] = ft.returns.as_slice() else {
        return Err(LinkRefusal::OutOfFragment(format!(
            "{} return values (the fragment has exactly one)",
            ft.returns.len()
        )));
    };
    let width = uniform_uint_width(ret).ok_or_else(|| {
        LinkRefusal::OutOfFragment(format!(
            "return type {ret} (the fragment is U8/U16/U32/U64; a boxed or \
             pointer-shaped symbol carries a statement the importer cannot re-derive \
             from its signature)"
        ))
    })?;
    for p in &ft.params {
        if uniform_uint_width(p) != Some(width) {
            return Err(LinkRefusal::OutOfFragment(format!(
                "parameter type {p} (the fragment requires every parameter at the \
                 uniform width U{width})"
            )));
        }
    }
    Ok(width)
}

/// The dependency's single recorded producer, or a named refusal. `None` is
/// never returned as "agreement" — the two failure modes are distinct arms.
fn measured_producer(module: &Module) -> Result<Producer, LinkRefusal> {
    let mut seen: BTreeSet<&Producer> = BTreeSet::new();
    for f in &module.functions {
        if let Some(p) = &f.producer {
            seen.insert(p);
        }
    }
    let mut it = seen.into_iter();
    match (it.next(), it.next()) {
        (None, _) => Err(LinkRefusal::ProducerUnrecorded),
        (Some(only), None) => Ok(only.clone()),
        (Some(_), Some(_)) => Err(LinkRefusal::ProducerMismatch),
    }
}

/// Is `linkage` visible to another module at link time?
fn externally_visible(linkage: Linkage) -> bool {
    !matches!(linkage, Linkage::Internal | Linkage::Private)
}

/// Which supplied artifact defines `symbol`, refusing ambiguity rather than
/// resolving it.
///
/// Only DEFINITIONS are candidates. A transitive build (`mid.bin` linked
/// against `lib.bin`, then a client linked against both) has `mid.bin`
/// DECLARE every `lib.bin` symbol it imports; counting that declaration as a
/// second carrier refused every import chain longer than one edge as
/// `SymbolAmbiguous` (WS6.8 review), although the consumer binds such a call
/// edge to the one dependency that defines the symbol. Two definitions are
/// still refused, never resolved by picking one; a symbol only ever declared
/// is [`LinkRefusal::FarSiteIsUnbackedDeclaration`].
fn locate<'a>(
    linked: &'a [LinkedArtifact],
    symbol: &str,
) -> Result<(usize, &'a Function), LinkRefusal> {
    let mut found: Option<(usize, &Function)> = None;
    let mut declared = false;
    for (i, artifact) in linked.iter().enumerate() {
        for f in &artifact.module.functions {
            if f.name != symbol {
                continue;
            }
            if f.is_declaration() {
                declared = true;
                continue;
            }
            if found.is_some() {
                return Err(LinkRefusal::SymbolAmbiguous);
            }
            found = Some((i, f));
        }
    }
    let Some((i, f)) = found else {
        return Err(if declared {
            LinkRefusal::FarSiteIsUnbackedDeclaration
        } else {
            LinkRefusal::SymbolNotFound
        });
    };
    if !externally_visible(f.linkage) {
        return Err(LinkRefusal::FarSiteNotExternallyVisible(f.linkage));
    }
    Ok((i, f))
}

/// The UNIQUE `Certified` `TranslationValidation` obligation scoped to `far`,
/// found by MEASUREMENT over the dependency's own table — never by index.
fn far_discharge(dep: &Module, far: FuncId) -> Result<&ProofObligation, LinkRefusal> {
    let mut rows = dep.proof_obligations.iter().filter(|o| {
        o.function == Some(far)
            && o.kind == ObligationKind::TranslationValidation
            && o.status == ProofStatus::Certified
    });
    let first = rows.next().ok_or(LinkRefusal::FarDischargeNotUnique)?;
    if rows.next().is_some() {
        return Err(LinkRefusal::FarDischargeNotUnique);
    }
    Ok(first)
}

/// Re-earn the dependency's own `Certified` labels IN THIS PROCESS: validate it
/// under `RejectingModuleProofAuthority` and return the set of certificate
/// lineage refs the Clean kernel actually replayed. A `Trusted` row, or a bare
/// `Discharged` label, contributes nothing to this set — which is the point.
fn replayed_refs(dep: &Module) -> BTreeSet<trust_ir::proof::ProofCertificateRef> {
    let empty: Vec<Module> = Vec::new();
    let set = ModuleSet::new(empty.iter());
    let report = validate_linked_module(dep, &set, &RejectingModuleProofAuthority);
    if !report.is_ok() {
        // A dependency that does not validate grounds nothing at all.
        return BTreeSet::new();
    }
    report
        .replayed_certificate_refs()
        .cloned()
        .unwrap_or_default()
}

/// Write the cross-crate rows for `wanted` into `client`, measuring every value.
///
/// See the module docs for the full discipline. On `Err` the client is left
/// exactly as it was found.
#[cfg(test)]
pub(crate) fn link_imported_modules(
    client: &mut Module,
    linked: &[LinkedArtifact],
    wanted: &[WantedSymbol],
) -> Result<LinkReport, LinkError> {
    link_imported_modules_with_environment(client, linked, wanted, None)
}

fn link_imported_modules_with_environment(
    client: &mut Module,
    linked: &[LinkedArtifact],
    wanted: &[WantedSymbol],
    source_environment: Option<&clean_kernel::Environment>,
) -> Result<LinkReport, LinkError> {
    // Check every supplied module before hashing or constructing import rows.
    // Cloning does not erase claims, but the infallible canonical digest would
    // panic for an ahead-of-wire claim (a certificate binding was one until
    // trust-ir wire v61 gave it a carrier).
    if let Some(reason) = trust_ir_build::wire_identity_blocker(client) {
        return Err(LinkError::ConsumerRefused(vec![reason.to_string()]));
    }
    for artifact in linked {
        if let Some(reason) = trust_ir_build::wire_identity_blocker(&artifact.module) {
            return Err(LinkError::ConsumerRefused(vec![format!(
                "linked artifact {}: {reason}",
                artifact.path
            )]));
        }
    }
    if linked.is_empty() || wanted.is_empty() {
        return Ok(LinkReport::default());
    }
    // Work on a scratch copy so a refusal at the final gate leaves the caller's
    // module byte-identical to what it handed in.
    let mut scratch = client.clone();
    let mut report = LinkReport::default();

    // --- artifacts: measure, then intern. ---------------------------------
    //
    // `Module::imports` is content-interned and POSITIONAL: `ImportId` is
    // meaningful only against the exact table order, so every row goes in
    // through `intern_import` and the table is never touched again once the
    // first `ExternRef` cites it.
    //
    // Only an artifact a wanted symbol is about is recorded. A supplied
    // artifact that carries no wanted symbol is not a dependency of the
    // client, and a row for it would claim one ("an unused dependency is not
    // a row", `nothing_is_written_when_nothing_was_asked_for`; WS6.8 review:
    // with a non-empty `wanted`, every supplied artifact used to get a row).
    // A symbol that RESOLVES is about its one definer only — another
    // artifact's body-less declaration of it is that artifact's own import,
    // not the client's. A symbol that does NOT resolve keeps every artifact
    // carrying it, so the consumer's gate below still judges what was
    // offered (e.g. a body-less far site whose certificate cannot replay,
    // `a_far_site_that_only_declares_is_refused`). Every supplied artifact
    // is still CHECKED below (target, producer): a wrong artifact on the
    // command line refuses rather than being ignored.
    let mut used: BTreeSet<usize> = BTreeSet::new();
    for w in wanted {
        match locate(linked, &w.symbol) {
            Ok((which, _)) => {
                used.insert(which);
            }
            Err(_) => used.extend(linked.iter().enumerate().filter_map(|(i, a)| {
                a.module
                    .functions
                    .iter()
                    .any(|f| f.name == w.symbol)
                    .then_some(i)
            })),
        }
    }
    let mut ids: BTreeMap<usize, ImportId> = BTreeMap::new();
    let mut replayed: BTreeMap<usize, BTreeSet<trust_ir::proof::ProofCertificateRef>> =
        BTreeMap::new();
    for (i, artifact) in linked.iter().enumerate() {
        let dep = &artifact.module;
        // Target identity, checked HERE so the consumer's refusal is pre-empted
        // at the producer. Absence on either side is not agreement.
        match (&scratch.target_info, &dep.target_info) {
            (Some(a), Some(b)) if a == b => {}
            _ => {
                return Err(LinkError::Artifact {
                    path: artifact.path.clone(),
                    why: LinkRefusal::TargetMismatch,
                });
            }
        }
        let producer = measured_producer(dep).map_err(|why| LinkError::Artifact {
            path: artifact.path.clone(),
            why,
        })?;
        if !used.contains(&i) {
            continue;
        }
        // MEASURED over the decode that was actually read.
        let digest = dep.stable_digest();
        // A full import table is refused like the final gate's refusals: the
        // caller's module is untouched (this is the scratch copy).
        let id = scratch
            .intern_import(ModuleImport::new(dep.name.clone(), digest).with_producer(producer))
            .map_err(|refusal| {
                LinkError::ConsumerRefused(vec![format!(
                    "linked artifact {}: the client's import table refused the row: {refusal}",
                    artifact.path
                )])
            })?;
        ids.insert(i, id);
        replayed.insert(i, replayed_refs(dep));
        report.imports.push((id, dep.name.clone(), digest));
    }

    // Fresh ids, taken above whatever the emitter already allocated.
    let mut next_proof = scratch
        .proof_obligations
        .iter()
        .map(|o| o.id.index() + 1)
        .max()
        .unwrap_or(0);

    // --- symbols. ----------------------------------------------------------
    for wanted_symbol in wanted {
        let symbol = &wanted_symbol.symbol;
        let (which, far) = match locate(linked, symbol) {
            Ok(found) => found,
            Err(why) => {
                report.declined.push((symbol.clone(), why));
                continue;
            }
        };
        let dep = &linked[which].module;
        let import = ids[&which];
        let Some(far_ft) = dep.func_types.get(far.ty.as_usize()) else {
            report
                .declined
                .push((symbol.clone(), LinkRefusal::SymbolNotFound));
            continue;
        };
        // `Function::name` is normatively the LINK-TIME SYMBOL, and v41's
        // `DuplicateFunctionSymbol` rule makes one module carrying two of them
        // invalid. The emitter mints a boxed `fn(Ptr..) -> Ptr` fallback for
        // every dropped callee, so this is the arm that fires when a client
        // already calls the symbol it is trying to import.
        //
        // Declining is not the end of it. Since trust-ir WS1.7 (da6ff616, L10)
        // every call edge binds to the one authenticated artifact that defines
        // and exports its symbol, and the import row already interned above
        // (`intern_import`) authenticates this dependency as that definer. A
        // client fallback whose signature differs from the far one is
        // therefore refused by the final gate, and the whole link returns
        // `ConsumerRefused` (pinned by
        // `a_symbol_the_client_already_declares_is_refused_not_duplicated` in
        // `emit_trust_ir_link_tests.rs`).
        //
        // The ONE exception is the emitter's IMPORTED-callee declaration
        // (WS6.8): a body-less, claim-free declaration whose signature is
        // structurally EQUAL to the far one is exactly the row this producer
        // would mint, so it is ADOPTED. Anything else — the boxed fallback, a
        // definition, a declaration at any other signature — keeps the refusal.
        let existing: Vec<&Function> = scratch
            .functions
            .iter()
            .filter(|f| f.name == far.name)
            .collect();
        let decl_id = match existing.as_slice() {
            [] => {
                // The typed body-less declaration: the FAR signature,
                // re-interned locally. Deliberately NOT the boxed
                // `fn(Ptr..) -> Ptr` extern fallback shape, which a
                // consumer's signature check would refuse.
                let local_ft = scratch.add_func_type(far_ft.clone()).map_err(|refusal| {
                    LinkError::ConsumerRefused(vec![format!(
                        "symbol {symbol}: the client's signature table refused the row: {refusal}"
                    )])
                })?;
                let decl_id =
                    FuncId::new(u32::try_from(scratch.functions.len()).unwrap_or(u32::MAX));
                let mut decl = Function::declaration(
                    decl_id,
                    far.name.clone(),
                    local_ft,
                    trust_ir::FunctionSummary::new(),
                );
                // No contract is imported: Clean emits none, and inventing a
                // summary to reach `ExternRefSite::SummaryBackedBy` would be
                // claiming a contract nobody proved.
                decl.summary = None;
                decl.producer = far.producer.clone();
                decl.display_path = far.display_path.clone();
                // A declaration is not a codegen subject, so it makes no
                // licensing claim.
                decl.body_gate = None;
                scratch.try_add_function(decl).map_err(|refusal| {
                    LinkError::ConsumerRefused(vec![format!(
                        "symbol {symbol}: the client refused the declaration: {refusal}"
                    )])
                })?;
                decl_id
            }
            [mine] if adoptable_import_declaration(&scratch, mine, far_ft) => mine.id,
            _ => {
                report
                    .declined
                    .push((symbol.clone(), LinkRefusal::ClientAlreadyDeclaresSymbol));
                continue;
            }
        };
        let mut written = ImportedSymbol {
            symbol: symbol.clone(),
            import,
            decl: decl_id,
            restatement: None,
        };

        // --- the proof claim, or its named absence. ------------------------
        match earn_claim(
            dep,
            far,
            far_ft,
            &replayed[&which],
            wanted_symbol.client_source.as_ref(),
            source_environment,
        ) {
            Err(why) => {
                // Identity written, proof claim NOT invented.
                report.identity_only.push((written, why));
            }
            Ok(earned) => {
                let restatement = ProofId::new(next_proof);
                next_proof += 1;
                scratch.proof_obligations.push(
                    ProofObligation::new(
                        restatement,
                        ObligationKind::TranslationValidation,
                        ProofStatus::Discharged,
                        format!(
                            "inherited backend translation validation: '{symbol}' denotes its \
                             Clean definition (mod 2^{}), discharged in the dependency and \
                             re-earned across an authenticated import",
                            earned.width
                        ),
                    )
                    .with_function(decl_id)
                    // The formula the importer DERIVED, which was then required
                    // to equal the one the dependency recorded.
                    .with_formula(earned.formula.clone()),
                );
                scratch.proof_certificates.push(ProofCertificate {
                    obligation: restatement,
                    prover: "clean-backend-tv-import".to_string(),
                    evidence: ProofEvidence::InheritedFromCallee {
                        callee: decl_id,
                        // The LOCAL restatement, equal to `certificate.obligation`.
                        // The FAR id belongs only in `ExternRef::obligation`.
                        obligation: restatement,
                        external: Some(
                            ExternRef::new(import, far.name.clone())
                                .relying_on(earned.far_obligation),
                        ),
                    },
                    // No `NativeVerificationBundle` and no request digest, so
                    // there is nothing to project a `CoverageBound` from.
                    assurance: None,
                });
                written.restatement = Some(restatement);
                report.proved.push(written);
            }
        }
    }

    // --- the producer's last act IS the consumer's check. -----------------
    let deps: Vec<Module> = linked.iter().map(|a| a.module.clone()).collect();
    let set = ModuleSet::new(deps.iter());
    let verdict = validate_linked_module(&scratch, &set, &RejectingModuleProofAuthority);
    if !verdict.is_ok() {
        return Err(LinkError::ConsumerRefused(
            verdict.errors().iter().map(|e| format!("{e:?}")).collect(),
        ));
    }
    *client = scratch;
    Ok(report)
}

/// Is `mine` — a client function already carrying the imported symbol — the
/// emitter's imported-callee declaration, i.e. exactly the row this producer
/// would otherwise mint? Body-less, no summary, no licensing claim, and a
/// signature structurally EQUAL to the far one. The boxed `fn(Ptr..) -> Ptr`
/// fallback fails the last clause for every in-fragment import, and is
/// refused as before.
fn adoptable_import_declaration(client: &Module, mine: &Function, far_ft: &FuncTy) -> bool {
    mine.is_declaration()
        && mine.summary.is_none()
        && mine.body_gate.is_none()
        && client.func_types.get(mine.ty.as_usize()) == Some(far_ft)
}

/// What a re-earned claim carries.
struct Earned {
    width: u32,
    formula: ProofFormula,
    far_obligation: ProofId,
}

/// Establish — by measurement, in this order — that the far discharge may be
/// inherited, or name the step that failed.
fn earn_claim(
    dep: &Module,
    far: &Function,
    far_ft: &FuncTy,
    replayed: &BTreeSet<trust_ir::proof::ProofCertificateRef>,
    client_source: Option<&Expr>,
    source_environment: Option<&clean_kernel::Environment>,
) -> Result<Earned, LinkRefusal> {
    // (2) in the fragment whose statement a signature determines.
    let width = fragment_width(far_ft)?;
    // (3) exactly one Certified TranslationValidation scoped to the far function.
    let far_obligation = far_discharge(dep, far.id)?;
    // (4) the formula, RE-DERIVED here from the far name and signature, then
    // required to be the one the dependency recorded. Copying A's formula would
    // make `check_inherited`'s equality vacuous; deriving it makes the
    // formula/signature agreement a real check.
    let arity = u32::try_from(far_ft.params.len()).unwrap_or(u32::MAX);
    let derived = clean_reflect::tv_statement_formula(&far.name, arity, width);
    let recorded = far_obligation
        .formula
        .as_ref()
        .ok_or(LinkRefusal::FarFormulaAbsent)?;
    if *recorded != derived {
        return Err(LinkRefusal::FarFormulaDisagreesWithSignature);
    }
    // (5) the far `Certified` label re-earned by an in-process kernel replay.
    // A status label is not proof authority.
    let grounded: Vec<&ProofCertificate> = dep
        .proof_certificates
        .iter()
        .filter(|c| c.obligation == far_obligation.id && replayed.contains(&c.lineage_ref()))
        .collect();
    if grounded.is_empty() {
        return Err(LinkRefusal::FarDischargeNotGrounded);
    }
    // (6) SOURCE BINDING (WS6.8 REVIEW). Steps 1-5 prove that the far function
    // denotes the comparand its certificate RECORDS; nothing so far says that
    // comparand is what the CLIENT means by the symbol. Recompute the
    // comparand from the client's own elaboration with the minter's own
    // normalization, and require every grounded far certificate to record
    // exactly those bytes.
    let source = client_source.ok_or_else(|| {
        LinkRefusal::ClientSourceUnavailable("no client definition was supplied".to_string())
    })?;
    let mine =
        crate::emit_trust_ir_tv::source_comparand_bytes(dep, far, source, source_environment)
            .map_err(LinkRefusal::ClientSourceUnavailable)?;
    let bound = grounded.iter().all(|c| match &c.evidence {
        ProofEvidence::CleanCic { context, .. } => *context == mine,
        _ => false,
    });
    if !bound {
        return Err(LinkRefusal::FarComparandDisagreesWithClientSource);
    }
    Ok(Earned {
        width,
        formula: derived,
        far_obligation: far_obligation.id,
    })
}

#[cfg(test)]
#[path = "emit_trust_ir_link_tests.rs"]
mod tests;
