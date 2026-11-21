// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Backend TRANSLATION-VALIDATION minter (P2): the first SEMANTICS-PRESERVATION
//! certificate for the `emit_trust_ir` backend — the give-back template
//! (untrusted producer + trusted in-process kernel re-check, fail-closed)
//! applied to compilation itself.
//!
//! # What is certified
//!
//! For a compiled declaration whose EMITTED trust-ir function falls in the
//! Fragment-2 arithmetic fragment (single block, call-free, memory-free,
//! branch-free: params + `Const Int` + `BinOp{Add,Sub,Mul}` at one unsigned
//! width `w` + `Return` — see `clean_reflect::denote`), the minter has the
//! kernel DECIDE the per-decl equation
//!
//! ```text
//! CleanTV.<fn>.denotes : ∀ (x1 … xn : Nat), ⟦emitted fn⟧ = ⟦original defn⟧
//! ```
//!
//! over the shared `Nat`-mod-`2^w` denotation vocabulary (trust-ir's ratified
//! wrapping semantics; simultaneously the `toNat` semantics of the kernel's
//! fixed-width `UIntW` ops). Only when `Environment::add_decl` accepts the
//! `Eq.refl`-style proof term — i.e. when the kernel finds the two open
//! denotations DEFINITIONALLY EQUAL — does the minter attach a
//! [`ObligationKind::TranslationValidation`] obligation (status `Certified`,
//! `function` set) plus [`ProofEvidence::CleanCic`] whose payload lets
//! `trust_ir_build::validate` (feature `clean-tv-anchor`, anchor
//! `clean_backend_tv`) independently RE-derive the LHS from the module and
//! re-run the same kernel judgment. This deliberately replaces the old
//! SMT-hash-shaped `ProofEvidence::TranslationValidation { rule_name,
//! smt_hash }` design for this workstream: the evidence on a
//! `TranslationValidation` obligation is a kernel-checkable `CleanCic`
//! payload, not an opaque hash.
//!
//! # Fragment-4 (heap) at the mint gate
//!
//! The denotation walker (`clean_reflect::denote`, Fragment-4) admits the
//! closed-address alloc/store/load choreography: `HeapAlloc(CleanHeap)` at
//! concrete model bases, constant-index `GEP`s folded to closed `Nat`
//! literals via the `StructDef` layout, and one heap term threaded through
//! `hwrite`/`hread` (definitional combinators the kernel unfolds —
//! [`clean_reflect::heap_vocab_declarations`] is installed into the judgment
//! environment below). Anything non-foldable — a non-constant GEP index, a
//! pointer-typed parameter, an address that does not fold, a `Load` from an
//! unrecorded or released cell — REFUSES the mint fail-closed (the decl
//! stays outside the fragment: a SKIP with the auditable walker reason).
//!
//! **A Fragment-4 cell is a reference-counted `CleanHeap` cell, released by
//! `Release` and never by `Dealloc`** (trust-ir SPEC "A reference-counted
//! cell is released by `Release`, never by `Dealloc`", ratified 2026-09-27).
//! No pointer escapes the fragment and `Retain` / `IsUnique` are outside it,
//! so the count is 1 at the cell's `Release`, which frees it. A `Dealloc` of
//! such a cell is undefined behaviour: the walker refuses it BY NAME as a
//! wrong emission, and the minter REFUSES (never skips) it.
//!
//! **The release is invisible to the value equation** (a pure value
//! denotation cannot observe a cell being freed), so the mint gate adds a
//! STRUCTURAL alloc/release balance check for in-fragment functions
//! (`alloc_release_balance`, mirrored by trust-ir's `clean_backend_tv`
//! re-checker): every `HeapAlloc` result must be `Release`d exactly once, by
//! its own result value; a `Dealloc` of an allocation base is refused; a
//! `Release` of any other value is neither counted nor refused HERE. A
//! dropped or doubled `Release` is a REFUSAL — a detected wrong-code emission
//! — not a skip; the kernel equation does not (and cannot) carry this claim.
//! TRUST.md boundary-6 wording: the heap fragment's kernel claim is
//! value-correctness; the release discipline is checked structurally here
//! (test evidence, not a kernel judgment).
//!
//! # Fragment-5 (boxed `Nat`): kernel-checked, balanced, NOT minted
//!
//! A parameter-free `() -> Ptr` body over Clean's boxed-`Nat` runtime rows
//! (`clean_reflect::denote`, Fragment-5) is still walked, still held to the
//! ownership balance, and its equation is still decided by the kernel — but
//! no obligation, no certificate and no `Gated` license is attached: the
//! decl is SKIPPED with [`FRAGMENT5_NOT_MINTED`]. Two reasons, both measured
//! 2026-09-29 (trust-ir SPEC "A reference-counted cell is released by
//! `Release`, never by `Dealloc`", clause 4):
//!
//! * **No consumer re-checks it.** trust-ir's `clean_backend_tv` has no
//!   Fragment-5: it refuses a `Ptr` return, so `validate_module` refuses a
//!   Fragment-5 certificate and, with it, the module that carries it (12 of
//!   12 certificate-carrying prelude modules, one per `UInt{8,16,32,64}.size`
//!   row per level). A `Gated` license no re-check can back was honoured
//!   without evidence by a pre-evidence-binding codegen consumer (trust-cg
//!   2fc2d576 compiled `UInt64.size` on the license alone).
//! * **Reference counting is invisible to the value equation.** Until
//!   2026-09-29 the walker treated every `Retain` / `Release` as a no-op, so
//!   it admitted — and the minter certified — bodies that free a
//!   reference they still use, free one twice, or leak one. The walker's
//!   `f5_ownership_balance` (every `Ptr` call result an owned reference at
//!   count 1; `Retain` adds one; `Release`, an `l_Nat_*` argument and the
//!   `Return` each give one up; a `clean_unbox*` argument only reads) now
//!   runs on EVERY admitted Fragment-5 body, kernel-judged or not, and a
//!   violation is a [`ReflectError::WrongEmission`] this minter REFUSES.
//!
//! So a Fragment-5 body is REFUSED when the balance or the kernel refuses it
//! (either fails the compile under `certify_translation`), and SKIPPED with
//! [`FRAGMENT5_NOT_MINTED`] when both accept it. Minting resumes only in the
//! commit that moves Clean's trust-ir pin onto a `clean_backend_tv` that
//! re-derives Fragment-5 with the same balance.
//!
//! # Fail-closed discipline
//!
//! * **Out-of-fragment decl** (either side): silently SKIPPED — no
//!   obligation, no certificate, NEVER a fake or `Trusted`-downgraded cert
//!   (mirrors `clean_reflect::reflect_module`'s skip semantics). The skip
//!   reason is recorded in the report for audit.
//! * **In-fragment but kernel REFUSES the equation**: recorded as REFUSED —
//!   this is the miscompile detector firing. The pipeline wiring
//!   (`TrustIrConfig::certify_translation`) turns any refusal into a hard
//!   compile error; the raw API surfaces it in the report.
//! * **In-fragment but the alloc/release balance is broken**: likewise
//!   REFUSED (see above). So is a `Dealloc` of a heap cell, which the walker
//!   reports as a wrong emission, and a Fragment-5 body that breaks the
//!   ownership balance.
//! * **Fragment-5 that the balance and the kernel both accept**: SKIPPED
//!   with [`FRAGMENT5_NOT_MINTED`] (see above) — decided, never minted.
//! * A serialization failure of the payload likewise refuses (never a
//!   half-built certificate).
//!
//! # Codegen license (trust-ir binary v41)
//!
//! The kernel judgment above is the ONE gate this producer owns, so it is
//! also what licenses a body for codegen: when `Environment::add_decl`
//! accepts a decl's translation equation (and its axiom closure is empty),
//! the driver stamps that function's [`trust_ir::Function::body_gate`] with
//! `Gated { authority: "clean-kernel-tv" }` ([`CLEAN_KERNEL_TV_AUTHORITY`])
//! in the same step that attaches the `Certified` obligation and its
//! `CleanCic` certificate — except a Fragment-5 body, which is never minted
//! and so never licensed. Every other emitted body keeps the `Ungated` claim
//! the emitter stamped ([`crate::emit_trust_ir`], "Codegen license"), so a
//! consumer running `trust_ir_build::validate_module_for_codegen` proceeds
//! on exactly the bodies whose certificate it can re-check and refuses the
//! rest. A skip or a refusal never touches the license.
//!
//! That one-step stamping is an INVARIANT, pinned by the WS6.7(e) tests:
//! `Gated` is written in exactly one place in this crate — the arm that also
//! pushes the `Certified` obligation and its certificate — so no path licenses
//! a body apart from its evidence. trust-ir's WS1.5 codegen gate checks the
//! same thing from the consumer side (`Gated { "clean-kernel-tv" }` requires
//! exactly one kernel-rechecked `Certified` TV row scoped to the function).
//!
//! # Certificate binding and license evidence (roadmap WS6.7(b))
//!
//! The bound mint and the license's `GateEvidence` are stated in the
//! `binding` submodule (`emit_trust_ir_tv_binding.rs`), with the helpers that
//! populate them.
//!
//! # Composition and producer identity
//!
//! Callee composition is keyed by the called FUNCTION (`FuncId`), one
//! `InheritedFromCallee` row per function the body calls — the call-edge
//! bijection trust-ir's WS1.4 rule checks. Source names are used only to find
//! a decl's own emitted function and its definition. The minter REFUSES a
//! function whose `producer` is not `Some(Producer::Clean)` (WS6.7(d)): it
//! certifies Clean's own output only. That is producer hygiene, not the
//! closure of F-016 — the `clean_backend_tv` anchor is producer-agnostic by
//! trust-ir's WS1.4 decision.
//!
//! # Trust boundaries (honest statement)
//!
//! 1. The kernel decides ONLY the equation between the two denotations. The
//!    denotation maps themselves (`clean_reflect::denote`) are checker spec —
//!    transcriptions of trust-ir's ratified wrapping semantics and the
//!    kernel's `UIntW` definitions whose own kernel-level mechanization is
//!    deferred (documented in `clean_reflect::denote`).
//! 2. The binding of the comparand to the decl's REAL source definition
//!    happens HERE, at mint time, where the source of truth (the kernel
//!    environment's `ConstantInfo.value`) lives. The trust-ir-side re-checker
//!    re-derives the LHS from the module but must trust the recorded
//!    comparand to be the original — it is carried decodably (`context`
//!    bytes) and named (`CleanTV.<fn>.denotes`, module
//!    `"CleanCompiler.BackendTV"`) so any holder of the Clean source can
//!    audit it. A BOUND certificate additionally names the source by
//!    declaration and `clean_kernel::Environment::closure_digest`, which an
//!    importer compares against its own elaboration (WS6.8); the validator
//!    carries it without checking it until WS1.13.
//! 3. The certificate says the emitted function DENOTES the source under the
//!    mod-2^w vocabulary. It does not (and does not claim to) certify
//!    anything outside the fragment: RC insertion, ctor lowering, control
//!    flow, calls, the runtime — all remain exactly as unverified as before.

use std::collections::{BTreeMap, BTreeSet};

use clean_kernel::env::{Declaration, Environment};
use clean_kernel::{BinderInfo, Expr, Name};
use clean_reflect::{
    denote_function, denote_source_nat, denote_source_nat_in_environment,
    denote_source_with_requirements, tv_anchor_environment, tv_proof_term, tv_statement,
    tv_theorem_name, RecordVocab, ReflectError,
};
use trust_ir::proof::{
    clean_cic_lineage_digest, clean_cic_lineage_digest_v8, clean_cic_statement_digest,
    kernel_environment_digest, module_symbol_resolver, CertificateBinding, CleanCicKernelRecheck,
    ObligationKind, ProofCertificate, ProofDigest, ProofEvidence, ProofObligation, ProofStatus,
    SourceDefinitionRef,
};
use trust_ir::ty::Ty;
use trust_ir::value::{FuncId, ProofId};
use trust_ir::{BodyGate, Function, GateEvidence, Module, Producer};

/// `Nat^ca → Nat` — the kernel type of a pinned callee symbol of arity `ca`
/// (used only to give the serialized comparand's outer binders honest types;
/// the re-checker rebuilds the statement from its own re-derived callee list).
fn callee_fn_ty(ca: usize) -> Expr {
    (0..ca).fold(Expr::const_str("Nat"), |acc, _| {
        Expr::arrow(Expr::const_str("Nat"), acc)
    })
}

/// The `module` audit string stamped into the recheck directive.
const TV_MODULE: &str = "CleanCompiler.BackendTV";

/// The codegen-license authority this minter stamps on a body it certified
/// (`Function::body_gate = Some(BodyGate::Gated { authority, evidence })`,
/// trust-ir binary v41; the evidence since the certificate-binding version,
/// v61). It
/// names the gate — the in-process Clean kernel's acceptance
/// of the decl's translation equation, re-checkable through the
/// `clean_backend_tv` anchor — not this crate: a consumer decides for itself
/// whether to RECOGNIZE it, and an unrecognized authority is a refusal.
pub const CLEAN_KERNEL_TV_AUTHORITY: &str = "clean-kernel-tv";

/// The skip reason of a Fragment-5 (boxed-`Nat`, `() -> Ptr`) decl whose
/// equation the kernel ACCEPTED and whose body the ownership balance
/// admitted: it is decided but not minted, because trust-ir's
/// `clean_backend_tv` has no Fragment-5 and refuses a `Ptr` return (see the
/// module docs, "Fragment-5 (boxed `Nat`)").
pub const FRAGMENT5_NOT_MINTED: &str = "Fragment-5 (boxed Nat, () -> Ptr): the kernel accepted \
     the equation and the ownership balance holds, but no certificate is minted — trust-ir's \
     clean_backend_tv has no Fragment-5 (it refuses a Ptr return), so validate_module would \
     refuse the certificate and the module that carries it";

/// Exact fields copied from an already checked original-source Theorem.
/// In-process transport only: replay requires the original environment and an
/// externally expected typed source mapping. These fields confer no authority.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub struct TvSourceEquation {
    /// Original typed source identity in the supplied environment.
    pub source: Name,
    /// Actual emitted function in the digest-bound complete module.
    pub function: FuncId,
    /// Producer's exact theorem identity; a replay may use another fresh name.
    pub theorem_name: Name,
    /// Ordered universe parameters of the actual checked theorem.
    pub level_params: Vec<Name>,
    /// Original checked judgment, without source/model reconstruction.
    pub type_: Expr,
    /// Full checked proof term for that judgment.
    pub value: Expr,
    /// Original environment's source closure identity.
    pub source_closure_digest: [u8; 32],
    /// Producer-named theorem closure identity, distinct from a fresh replay's.
    pub equation_closure_digest: [u8; 32],
}

/// Outcome of a [`certify_backend_translation`] run.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
#[non_exhaustive]
pub struct TvMintReport {
    /// Only actual original-source equations retained on successful certification.
    /// Empty for legacy calls without an original environment; no coverage upgrade.
    pub source_equations: Vec<TvSourceEquation>,
    /// Identity of the complete module AFTER every certificate and gate mutation.
    /// None without retained equations; Err means no canonical binding.
    /// Applies to every retained record. Recompute after any later module change.
    /// A digest is identity, not source authentication or a code license.
    pub final_module_digest: Option<Result<ProofDigest, String>>,
    /// Decl names whose emitted function was kernel-certified to denote its
    /// original definition (obligation + certificate attached). This is
    /// exactly the set of bodies whose codegen license was upgraded to
    /// `Gated { authority: "clean-kernel-tv" }` in this run; every other
    /// emitted body keeps `Ungated`.
    pub certified: Vec<String>,
    /// Decls skipped fail-closed with the (auditable) reason — out of the
    /// fragment on either side, no emitted function of that name, or a
    /// Fragment-5 body decided but not minted ([`FRAGMENT5_NOT_MINTED`]). No
    /// obligation is attached for these.
    pub skipped: Vec<(String, String)>,
    /// Decls whose identity is ambiguous, whose certificate could not be
    /// soundly built, or whose in-fragment equation the kernel REFUSED.
    /// Kernel refusals detect emitted code that does not denote its source.
    /// No obligation is attached; pipeline wiring escalates a refusal to a
    /// hard error.
    pub refused: Vec<(String, String)>,
}

impl TvMintReport {
    /// Number of kernel-certified declarations.
    #[must_use]
    pub fn certified_count(&self) -> usize {
        self.certified.len()
    }
}

/// Mint the backend semantics-preservation certificate for every in-fragment
/// declaration, AFTER `finalize_module` (the module handed in is the exact
/// finalized artifact).
///
/// `originals` maps decl names to their ORIGINAL kernel definition `Expr`
/// (`Environment::get_const(name).value` — the pre-lowering source of truth,
/// unfolded lambda telescope). Functions in `module` without an entry in
/// `originals` are ignored (the runtime-ABI externs, helper decls, …);
/// entries without a matching emitted function are skipped with a reason.
/// Duplicate function IDs, function names or original-definition names refuse
/// the entire request before changing any license, obligation or certificate.
/// Existing obligation IDs must be unique, and existing certificates must name
/// an existing obligation. Exhausting the ID space refuses further minting;
/// the final `u32` ID is usable and never wraps back onto an earlier obligation.
///
/// See the module docs for exactly what is (and is not) certified.
///
/// Every certificate this entry point mints is UNBOUND
/// (`CleanCicKernelRecheck::binding = None`); every license it stamps still
/// carries its `GateEvidence`. The bound form is
/// `certify_backend_translation_bound_in_environment`, which the pipeline selects under
/// [`crate::emit_trust_ir::TrustIrConfig::bind_certificates`] (the default).
#[must_use]
pub fn certify_backend_translation(
    module: &mut Module,
    originals: &[(String, Expr)],
) -> TvMintReport {
    certify_with(module, originals, None, None)
}

/// The canonical compiler has the original source environment, so it resolves
/// the actual dictionary fields there instead of assuming named instances.
pub(crate) fn certify_backend_translation_in_environment(
    module: &mut Module,
    originals: &[(String, Expr)],
    environment: &Environment,
) -> TvMintReport {
    certify_with(module, originals, None, Some(environment))
}

/// The shared driver of [`certify_backend_translation`] and
/// [`certify_backend_translation_bound_in_environment`]; `source_of` is `Some` exactly for
/// a bound mint.
fn certify_with(
    module: &mut Module,
    originals: &[(String, Expr)],
    source_of: Option<&dyn Fn(&str) -> Option<Result<SourceDefinitionRef, String>>>,
    source_environment: Option<&Environment>,
) -> TvMintReport {
    let mut report = TvMintReport::default();

    // Certificate IDs bind to function IDs, while source equations and callee
    // composition bind to names. Reject ambiguous identities before minting
    // anything, including when this public API receives an unfinalized module.
    if let Err(reason) = validate_tv_identities(module, originals) {
        report.refused = originals
            .iter()
            .map(|(name, _)| (name.clone(), reason.clone()))
            .collect();
        return report;
    }

    // ONE anchor environment per run: every decl is judged in a clone of it,
    // so a bound certificate's `environment_digest` (digested at most once per
    // run, on the first certificate that needs it) names exactly the
    // environment its equation was checked in.
    let anchor = match tv_anchor_environment() {
        Ok(env) => env,
        Err(reason) => {
            report.refused = originals
                .iter()
                .map(|(name, _)| (name.clone(), reason.clone()))
                .collect();
            return report;
        }
    };
    // The anchor digest is a whole-environment encoding (every prelude
    // constant), so it is taken LAZILY: a run that certifies nothing — every
    // decl out of the fragment, refused, or decided-not-minted — pays nothing.
    let environment_digest = std::cell::OnceCell::new();
    let binding = source_of.map(|source_of| BindingInputs {
        source_of,
        environment_digest: &environment_digest,
    });

    // Fresh, collision-free obligation ids (after any pre-existing ones —
    // e.g. the give-back pass that `ModuleBuilder::build` runs by default).
    let mut next_id = module
        .proof_obligations
        .iter()
        .map(|o| o.id.index())
        .max()
        .map_or(Some(0), |m| m.checked_add(1));

    // callee FuncId -> its certified TV obligation id (this run). Keyed by the
    // function a `Call` TARGETS, never by a source name (WS6.7(c)): one row
    // per called function is exactly the call-edge bijection trust-ir's WS1.4
    // composition rule checks. The name -> FuncId map is used only to find a
    // decl's own emitted function and its source definition.
    //
    // A caller (Fragment-3b) is certified only AFTER every callee it calls is
    // here, so its `InheritedFromCallee` composition is grounded. We iterate
    // to a fixpoint: each pass certifies leaves/callers whose callees are all
    // certified, and defers callers with an as-yet-uncertified callee; when a
    // pass certifies nothing, the still-deferred decls can never compose and
    // are skipped.
    let mut certified_tv: BTreeMap<FuncId, ProofId> = BTreeMap::new();
    let mut pending: Vec<&(String, Expr)> = originals.iter().collect();

    loop {
        let mut progressed = false;
        let mut deferred: Vec<&(String, Expr)> = Vec::new();
        for item in pending {
            let context = MintContext {
                anchor: &anchor,
                source_environment,
                binding: binding.as_ref(),
                certified_tv: &certified_tv,
            };
            match attempt_certify(module, &item.0, &item.1, &context, &mut next_id) {
                Attempt::Certified {
                    fid,
                    oid,
                    obligation,
                    cert,
                    inherited,
                    body_digest,
                    source_equation,
                } => {
                    // Codegen license (v41): the kernel has just accepted this
                    // function's equation, which is the one event that
                    // licenses its body. Stamp it HERE, in the same step as
                    // the Certified obligation + CleanCic certificate, so
                    // `Gated` can never be minted apart from them — and WITH
                    // its evidence (v61, WS6.7(b)): the obligation it rests on
                    // and the digest of the body it licenses, both of which
                    // trust-ir re-checks (`GatedEvidenceMismatch`). `fid` was
                    // resolved from `module.functions` by `attempt_certify`,
                    // so exactly one function matches.
                    debug_assert!(module.functions.iter().any(|f| f.id == fid));
                    for func in module.functions.iter_mut().filter(|f| f.id == fid) {
                        func.body_gate = Some(BodyGate::Gated {
                            authority: CLEAN_KERNEL_TV_AUTHORITY.to_string(),
                            evidence: Some(GateEvidence {
                                obligation: oid,
                                body_digest,
                            }),
                        });
                    }
                    module.proof_obligations.push(obligation);
                    module.proof_certificates.push(cert);
                    module.proof_certificates.extend(inherited);
                    certified_tv.insert(fid, oid);
                    if let Some(equation) = source_equation {
                        report.source_equations.push(*equation);
                    }
                    report.certified.push(item.0.clone());
                    progressed = true;
                }
                Attempt::Skip(reason) => report.skipped.push((item.0.clone(), reason)),
                Attempt::Refused(reason) => report.refused.push((item.0.clone(), reason)),
                Attempt::DeferCallee => deferred.push(item),
            }
        }
        if deferred.is_empty() {
            break;
        }
        if !progressed {
            // No callee will ever become certified — the composition cannot
            // close. Skip fail-closed (never a fake or partial cert).
            for item in deferred {
                report.skipped.push((
                    item.0.clone(),
                    "a named callee is not TV-certifiable (its own translation validation \
                     did not close), so the caller's compositional certificate cannot be \
                     grounded — fail-closed"
                        .to_string(),
                ));
            }
            break;
        }
        pending = deferred;
    }

    if !report.source_equations.is_empty() {
        report.final_module_digest = Some(match trust_ir_build::wire_identity_blocker(module) {
            Some(reason) => Err(reason.to_string()),
            None => Ok(module.stable_digest()),
        });
    }
    report
}

fn validate_tv_identities(module: &Module, originals: &[(String, Expr)]) -> Result<(), String> {
    let mut ids = BTreeSet::new();
    let mut names = BTreeSet::new();
    for function in &module.functions {
        if !ids.insert(function.id.index()) {
            return Err(format!("duplicate function id {}", function.id.index()));
        }
        if !names.insert(function.name.as_str()) {
            return Err(format!("duplicate function name `{}`", function.name));
        }
    }
    let mut source_names = BTreeSet::new();
    for (name, _) in originals {
        if !source_names.insert(name.as_str()) {
            return Err(format!("duplicate source name `{name}`"));
        }
    }
    let mut proof_ids = BTreeSet::new();
    for obligation in &module.proof_obligations {
        if !proof_ids.insert(obligation.id) {
            return Err(format!("duplicate proof obligation id {}", obligation.id));
        }
    }
    for certificate in &module.proof_certificates {
        if !proof_ids.contains(&certificate.obligation) {
            return Err(format!(
                "certificate references unknown proof obligation {}",
                certificate.obligation
            ));
        }
    }
    Ok(())
}

/// The per-pass state [`attempt_certify`] reads: the run's anchor
/// environment (cloned per decl), the binding inputs of a bound mint, and the
/// callees certified so far, keyed by the called function.
struct MintContext<'a> {
    anchor: &'a Environment,
    source_environment: Option<&'a Environment>,
    binding: Option<&'a BindingInputs<'a>>,
    certified_tv: &'a BTreeMap<FuncId, ProofId>,
}

/// The outcome of attempting to certify ONE decl in a fixpoint pass.
enum Attempt {
    /// Kernel-certified: attach the obligation, its CleanCic cert, and one
    /// `InheritedFromCallee` cert per callee (the compositional grounding),
    /// and license the body of `fid` for codegen (`BodyGate::Gated`).
    Certified {
        fid: FuncId,
        oid: ProofId,
        obligation: ProofObligation,
        cert: ProofCertificate,
        inherited: Vec<ProofCertificate>,
        /// `Module::function_body_digest` of `fid` as the kernel judged it —
        /// the license's `GateEvidence.body_digest`.
        body_digest: ProofDigest,
        source_equation: Option<Box<TvSourceEquation>>,
    },
    /// Out of fragment (either side), or no emitted function — no obligation.
    Skip(String),
    /// The certificate cannot be soundly allocated or built, or the kernel
    /// REFUSED the equation (the miscompile detector). No obligation is minted;
    /// pipeline wiring escalates to a hard error.
    Refused(String),
    /// In-fragment but a named callee is not yet certified — retry next pass.
    DeferCallee,
}

#[path = "emit_trust_ir_tv_balance.rs"]
mod balance;
use balance::alloc_release_balance;

/// Attempt to certify `name`'s emitted function against its `defn`, composing
/// in each callee's already-certified TV obligation. Never mutates `module`;
/// the driver attaches the returned obligation/certs.
fn attempt_certify(
    module: &Module,
    name: &str,
    defn: &Expr,
    context: &MintContext<'_>,
    next_id: &mut Option<u32>,
) -> Attempt {
    if !crate::emit_trust_ir::names::legacy_source_identity_supported(defn) {
        return Attempt::Skip(
            "legacy TV source identity is unmeasured for escaped typed names".to_string(),
        );
    }
    let Some(func) = module.functions.iter().find(|f| f.name == name) else {
        return Attempt::Skip("no emitted trust-ir function of this name".to_string());
    };
    let fid = func.id;
    // PRODUCER HYGIENE (WS6.7(d)). This minter certifies Clean's OWN output:
    // the comparand is a Clean kernel definition, so a body some other
    // producer emitted — or one whose provenance was never recorded — is not
    // the thing that definition describes, whatever its name. Refused (the
    // pipeline escalates a refusal to a hard error) rather than skipped, so a
    // lost producer stamp is loud. This keeps Clean's output honest; it is NOT
    // what closes F-016 — the `clean_backend_tv` anchor is producer-agnostic
    // by the WS1.4 DECIDE, and trust-ir's re-check never reads the producer.
    if func.producer != Some(Producer::Clean) {
        return Attempt::Refused(format!(
            "producer hygiene: `{name}` is not a Clean-produced body (Function.producer is \
             {:?}); the Clean TV minter certifies only Clean's own output",
            func.producer
        ));
    }
    let Some(fresh_id) = *next_id else {
        return Attempt::Refused("proof obligation id space is exhausted".to_string());
    };

    // (1) Denote the EMITTED function (fail-closed outside the fragment). This
    // also yields the canonical callee list (Fragment-3b). A `WrongEmission`
    // is an in-fragment structural violation a correct lowering can never
    // produce (uninitialized read, a `Dealloc` of a reference-counted heap
    // cell, self-inconsistent struct layout, a Fragment-5 body that breaks
    // the ownership balance) — a detected wrong-code emission, REFUSED like
    // the balance gate below, never an out-of-fragment skip.
    let lhs = match denote_function(module, func) {
        Ok(d) => d,
        Err(e @ ReflectError::WrongEmission(_)) => {
            return Attempt::Refused(format!("walker REFUSED (structural): {e}"));
        }
        Err(e) => return Attempt::Skip(format!("emitted side: {e}")),
    };

    // A resolved emitted callee/signature row can survive even when source
    // normalization erased its spelling. Never borrow a display twin's TV.
    if lhs.callees.iter().any(|(label, _)| {
        crate::emit_trust_ir::names::decode_wire_name(label)
            .is_none_or(|name| !crate::emit_trust_ir::names::is_legacy_name(&name))
    }) {
        return Attempt::Skip(
            "legacy TV callee identity is unmeasured for escaped typed names".to_string(),
        );
    }

    // (1a) Fragment-4 STRUCTURAL gate: the function is in-fragment, so a
    // broken alloc/release balance is a detected wrong-code emission — a
    // REFUSAL, never a skip (the kernel value equation cannot carry this).
    if let Err(reason) = alloc_release_balance(func) {
        return Attempt::Refused(reason);
    }

    // (1b) COMPOSITION GATE, keyed by the called FUNCTION (WS6.7(c)): resolve
    // each callee symbol of the canonical (name-sorted) telescope to the one
    // function a `Call` to it targets — `Function.name` is the link symbol and
    // `validate_tv_identities` refused duplicates up front — and require that
    // function's own TV obligation from this run (so its `InheritedFromCallee`
    // grounding exists). Otherwise defer.
    let mut callee_rows: Vec<(FuncId, ProofId)> = Vec::with_capacity(lhs.callees.len());
    for (cn, _) in &lhs.callees {
        let Some(callee) = module.functions.iter().find(|f| &f.name == cn) else {
            return Attempt::Refused(format!(
                "callee symbol `{cn}` denotes no function of this module, although the walker \
                 resolved it — refusing to compose against an unresolvable call target"
            ));
        };
        match context.certified_tv.get(&callee.id) {
            Some(oid) => callee_rows.push((callee.id, *oid)),
            None => return Attempt::DeferCallee,
        }
    }

    // (2) Denote the ORIGINAL kernel definition against the SAME callee list —
    // so a source `g a…` maps to the same pinned symbol the emit does — and
    // the module's record vocabulary (Fragment-4 ctor/projection sources).
    // A boxed-`Nat`-returning emitted function (Fragment-5) is compared in the
    // `Nat`-sorted source vocabulary; every scalar-returning fragment uses the
    // U-w vocabulary as before.
    let nat_return = module
        .func_types
        .get(func.ty.as_usize())
        .and_then(|ft| ft.returns.first())
        .is_some_and(|t| matches!(t, Ty::Ptr));
    let mut requires_original_source_equation = false;
    let rhs = if nat_return {
        let denotation = match context.source_environment {
            Some(env) => denote_source_nat_in_environment(defn, &lhs.callees, env),
            None => denote_source_nat(defn, &lhs.callees),
        };
        match denotation {
            Ok(d) => d,
            Err(e) => return Attempt::Skip(format!("source side (nat): {e}")),
        }
    } else {
        let records = RecordVocab::from_module(module);
        let denotation = denote_source_with_requirements(
            defn,
            lhs.width,
            &lhs.callees,
            &records,
            context.source_environment,
        );
        match denotation {
            Ok(d) => {
                requires_original_source_equation = d.requires_original_source_equation;
                d.denotation
            }
            Err(e) => return Attempt::Skip(format!("source side: {e}")),
        }
    };
    // (3) Both sides denoted: from here a mismatch is a REFUSAL, not a skip.
    if lhs.arity != rhs.arity {
        return Attempt::Refused(format!(
            "arity mismatch: emitted function takes {} argument(s), the source definition \
             binds {}",
            lhs.arity, rhs.arity
        ));
    }

    // A new propositional-ite model is not evidence about the actual source.
    // Prove its complete original UInt-valued call against the independently
    // walked emitted body, including the actual proposition and Decidable
    // value. The existing Nat-TV certificate and its grade are unchanged.
    let source_equation = if requires_original_source_equation {
        let Some(environment) = context.source_environment else {
            return Attempt::Skip("propositional ite requires the original source environment and a checked source equation".to_string());
        };
        let checked = match check_original_source_equation(environment, name, defn, &lhs) {
            Ok(checked) => checked,
            Err(error) => return Attempt::Refused(error),
        };
        let Declaration::Theorem {
            name,
            level_params,
            type_,
            value,
        } = checked.declaration()
        else {
            return Attempt::Refused("checked source equation was not a Theorem".to_string());
        };
        Some(Box::new(TvSourceEquation {
            source: checked.source().clone(),
            function: fid,
            theorem_name: name.clone(),
            level_params: level_params.clone(),
            type_: type_.clone(),
            value: value.clone(),
            source_closure_digest: *checked.source_closure_digest(),
            equation_closure_digest: *checked.equation_closure_digest(),
        }))
    } else {
        None
    };

    let callee_arities: Vec<usize> = lhs.callees.iter().map(|(_, a)| *a).collect();

    // (4) THE KERNEL JUDGMENT: declare the equation as a real Theorem in the
    // ground prelude environment. For the (parametric-in-callees) `Eq.refl`
    // term, `add_decl` reduces to definitional equality of the two open
    // denotations — the kernel decides it, universally over the callee symbols.
    let thm = tv_theorem_name(name);
    let stmt = tv_statement(&callee_arities, lhs.arity, &lhs.body, &rhs.body);
    let proof = tv_proof_term(&callee_arities, lhs.arity, &lhs.body);
    // (4a) BOUND mint (WS6.7(b)): the statement digest is taken HERE, over
    // the statement the kernel is about to check (it moves into the theorem
    // below). The rest of the binding is populated only after the judgment
    // (4c), so a decl whose binding cannot be populated is still judged and a
    // miscompile is still REFUSED, never merely skipped.
    let statement_digest = context.binding.map(|_| clean_cic_statement_digest(&stmt));
    // The run's anchor environment: the ground prelude, the Fragment-4 heap
    // vocabulary and the WS1.15 signed carrier aliases — DEFINITIONAL
    // declarations only (no axioms — the FOUNDATIONAL floor below is
    // unaffected), exactly the environment trust-ir's re-checker builds.
    // trust-ir's `clean_backend_tv` re-checker installs the same `CleanTV.h*`
    // vocabulary (since trust-ir 4257688a, 2026-07-11) and balances `Release`
    // (since trust-ir 2a4e6eb8, SPEC "A reference-counted cell is released by
    // `Release`", 2026-09-27). A re-checker older than 2a4e6eb8 refuses every
    // heap cert minted here (fail-closed); Clean pinned one until 2026-09-29.
    // The tests' `assert_pinned_trust_ir_rechecks` sends every heap corpus
    // certificate through the PINNED `validate_module`, so that window cannot
    // silently reopen.
    let mut env = context.anchor.clone();
    if let Err(e) = env.add_decl(Declaration::Theorem {
        name: Name::from_string(&thm),
        level_params: vec![],
        type_: stmt,
        value: proof.clone(),
    }) {
        return Attempt::Refused(format!(
            "kernel REFUSED the translation equation (the emitted function does not provably \
             denote its source definition): {e:?}"
        ));
    }
    // FOUNDATIONAL axiom floor: an honest Eq.refl equation has an EMPTY
    // structural axiom closure.
    match env.axiom_deps(&Name::from_string(&thm)) {
        Some(deps) if deps.is_empty() => {}
        Some(deps) => {
            return Attempt::Refused(format!(
                "equation proof unexpectedly depends on axioms {deps:?}"
            ));
        }
        None => {
            return Attempt::Refused(
                "kernel could not compute the equation's axiom closure".to_string(),
            );
        }
    }

    // (4b) FRAGMENT-5 IS DECIDED, NOT MINTED. The walker's ownership balance
    // and the kernel have both accepted the body; stop before any payload is
    // built, so no obligation, certificate or `Gated` license exists for a
    // shape trust-ir's `clean_backend_tv` refuses (module docs,
    // "Fragment-5"). Placed after the judgment on purpose: a miscompiled
    // Fragment-5 body is still REFUSED above, never skipped.
    if nat_return {
        return Attempt::Skip(FRAGMENT5_NOT_MINTED.to_string());
    }

    // (4c) BOUND mint: populate EVERY binding field, or skip with the reason
    // — never a partial binding, never an unbound certificate on this path,
    // never a license. The kernel has judged the equation by now (a miscompile
    // was REFUSED above). The environment digest is the run's one digest of
    // the anchor environment this decl was judged in a clone of.
    let binding = match context.binding {
        None => None,
        Some(inputs) => {
            let statement_digest = statement_digest
                .unwrap_or_else(|| Err("the statement digest was not taken".to_string()));
            match bound_binding(inputs, context.anchor, name, statement_digest, &lhs.callees) {
                Ok(binding) => Some(binding),
                Err(reason) => return Attempt::Skip(reason),
            }
        }
    };

    // (5) Build the decodable payload: comparand as `fun (G0…)(x…) => rhs.body`
    // (the re-checker strips `callees.len() + arity` binders), proof term as
    // minted. bincode-1-of-Expr. Serialization failure refuses (fail-closed).
    let rhs_lambda = comparand_lambda(&rhs.body, rhs.arity, &callee_arities);
    let (term, context) = match (bincode::serialize(&proof), bincode::serialize(&rhs_lambda)) {
        (Ok(t), Ok(c)) => (t, c),
        _ => return Attempt::Refused("certificate payload failed to serialize".to_string()),
    };

    // (6) Build the obligation + kernel-re-checkable certificate.
    let oid = ProofId::new(fresh_id);
    *next_id = fresh_id.checked_add(1);
    let composed = if lhs.callees.is_empty() {
        String::new()
    } else {
        format!(", composing {} certified callee(s)", lhs.callees.len())
    };
    let obligation = ProofObligation {
        id: oid,
        kind: ObligationKind::TranslationValidation,
        status: ProofStatus::Certified,
        description: format!(
            "backend translation validation: '{name}' denotes its Clean definition \
             (mod 2^{}, kernel-decided{composed})",
            lhs.width
        ),
        // The obligation STATES its claim (was `None` until 2026-09-17).
        //
        // A TV obligation with no formula cannot be inherited across a crate
        // boundary at all: `trust_ir_build`'s linked validator refuses a far
        // obligation that "carries no formula" because "a claim with no
        // statement cannot be restated", and refuses the local restatement
        // symmetrically. So a Clean library's certified decl was unimportable
        // by construction, however well the kernel had checked it — which is
        // the right refusal, and the reason this field had to stop being
        // `None`. `None` here was never "no claim"; it was an unwritten one.
        //
        // The text is a function of (symbol, arity, width) ONLY, so a
        // cross-module importer can RE-DERIVE it from the far `Function::name`
        // and far `FuncTy` and then demand byte-equality — rather than copying
        // it, which would make `check_inherited`'s formula equality vacuous.
        // `clean_reflect::tv_statement_formula` owns the single spelling.
        formula: Some(clean_reflect::tv_statement_formula(
            name,
            u32::try_from(lhs.arity).unwrap_or(u32::MAX),
            lhs.width,
        )),
        function: Some(fid),
        source: None,
        // Translation validation certifies the emitted function as a whole;
        // it is not an instruction-local check and therefore has no IR site.
        site: None,
        // trust-ir v46 `spec` names the `SpecModule` temporal property a
        // `Liveness`/`TemporalSafety` obligation DISCHARGES. A TV obligation
        // discharges none: it states a translation equation, not a temporal
        // property, and Clean emits no `SpecModule` into this module for a
        // reference to resolve against. `None` is therefore the only honest
        // value AND the only legal one — trust-ir-build's
        // `validate_obligation_spec_surface` refuses any `Some` on a kind other
        // than those two ("only a Liveness or TemporalSafety obligation states a
        // temporal property"). Not "unrecorded": there is nothing to record.
        spec: None,
    };
    // A bound certificate carries the symbol-keyed v8 lineage, which folds the
    // binding bytes in and survives id renumbering; an unbound one keeps the
    // index-keyed lineage it always had.
    let lineage = match &binding {
        None => clean_cic_lineage_digest(&obligation),
        Some(binding) => {
            let resolve = module_symbol_resolver(module);
            match clean_cic_lineage_digest_v8(&obligation, &resolve, Some(binding)) {
                Some(lineage) => lineage,
                None => {
                    return Attempt::Skip(
                        "bound mint: the obligation cannot be keyed by link symbol, so it has \
                         no v8 lineage"
                            .to_string(),
                    );
                }
            }
        }
    };
    let cert = ProofCertificate {
        obligation: oid,
        prover: "clean-backend-tv".to_string(),
        evidence: ProofEvidence::CleanCic {
            term,
            context,
            lineage,
            kernel_recheck: Some(CleanCicKernelRecheck {
                module: TV_MODULE.to_string(),
                theorems: vec![thm],
                anchor: clean_reflect::CLEAN_BACKEND_TV_ANCHOR.to_string(),
                allowed_axioms: vec![],
                // WS6.7(b): `Some` exactly on a bound mint, every field
                // populated above; `None` (UNBOUND, the pre-binding meaning)
                // on the default path. Never manufactured without its inputs.
                binding: binding.map(Box::new),
            }),
        },
        // trust-ir binary v41 added `assurance: Option<CoverageAssurance>`.
        // Read its contract before changing this: it is a coverage BOUND
        // (unbounded / unwind-bounded / model-bounded) PROJECTED from a
        // `NativeVerificationBundle` and bound to that bundle's request
        // digest, so a consumer holding the bundle re-derives the bound and
        // refuses on mismatch. It is the coverage axis of Trust's grade
        // record — explicitly NOT the retired flat `AssuranceLevel` tier —
        // and it neither adds to nor subtracts from what this certificate
        // establishes.
        //
        // NOT RECORDED, deliberately. This lane has no native bundle. What
        // the kernel decided is the translation equation itself — the
        // emitted function denotes its Clean definition for ALL inputs mod
        // 2^w, which is an unbounded claim — and the authority for that is
        // the `kernel_recheck` directive above, which `trust_ir_build`'s
        // validator re-runs in-process and rejects when it cannot. There is
        // no request digest to bind a `CoverageBound::Unbounded` projection
        // to; minting one from some other digest (the lineage, say) would be
        // exactly the producer's bare assertion the field's contract exists
        // to make distinguishable from a projection. `None` reads as UNKNOWN
        // coverage to a fail-closed consumer that does not re-run the kernel,
        // which is the right downgrade for a consumer that has checked
        // nothing; per trust's docs/TCB.md only the kernel re-check earns
        // `Certified`, and this field cannot mint or forfeit it. `None` also
        // keeps the module's wire bytes at their pre-v41 version.
        assurance: None,
    };

    // (7) One `InheritedFromCallee` certificate per callee: the caller's
    // parametric equation is grounded at each callee's OWN certified meaning
    // (the "cross-language proofs compose" thesis, enforced by the B5 validator
    // — it checks each cited callee obligation is itself ground-discharged).
    let inherited: Vec<ProofCertificate> = callee_rows
        .iter()
        .map(|&(callee_fid, callee_obligation)| {
            ProofCertificate {
                obligation: oid,
                prover: "clean-backend-tv-compose".to_string(),
                evidence: ProofEvidence::InheritedFromCallee {
                    callee: callee_fid,
                    obligation: callee_obligation,
                    // Module-local composition, spelled out (v41). `callee_fid`
                    // was resolved from THIS module's function table at the
                    // composition gate and `callee_obligation` is an obligation
                    // this same run minted, so both ids resolve here and the validator's
                    // local rule (callee exists, obligation ground-discharged
                    // in this module) is the one that applies. `None` is the
                    // pre-v41 meaning, byte-identical on the wire; the
                    // cross-crate `Some(ExternRef)` form names a separately
                    // compiled callee through `Module.imports`, which this
                    // backend never composes against.
                    external: None,
                },
                // See the ground certificate above. The composition records no
                // coverage of its own: whatever the callee's discharge covers
                // is established by re-running ITS kernel re-check, and this
                // row must not restate it.
                assurance: None,
            }
        })
        .collect();

    // (8) The license's EVIDENCE (WS6.7(b), trust-ir WS1.12(c)): the digest
    // of the body the kernel just judged, taken now so it names exactly this
    // body. `function_body_digest` excludes the license itself, so stamping
    // it below does not move the digest it cites. A body with no digest (a
    // construct with no binary carrier) is SKIPPED: never a `Gated` body
    // without its evidence.
    let body_digest = match module.function_body_digest(fid) {
        Ok(digest) => digest,
        Err(reason) => {
            return Attempt::Skip(format!(
                "license evidence: the body has no digest ({reason}), so its codegen license \
                 cannot name it — never a Gated body without its evidence"
            ));
        }
    };

    Attempt::Certified {
        fid,
        oid,
        obligation,
        cert,
        inherited,
        body_digest,
        source_equation,
    }
}

/// Shared by minting and imported-source comparand validation. A changed
/// proposition or Decidable value must not regain authority by producing the
/// same proposed Nat comparand.
fn check_original_source_equation(
    environment: &Environment,
    name: &str,
    definition: &Expr,
    denotation: &clean_reflect::TvDenotation,
) -> Result<clean_reflect::source_equation::CheckedSourceEquation, String> {
    let source = crate::emit_trust_ir::names::decode_wire_name(name)
        .ok_or("source equation requires an exact source name")?;
    if environment
        .get_const(&source)
        .and_then(|info| info.value.as_ref())
        != Some(definition)
    {
        return Err("source equation definition differs from the original environment".to_string());
    }
    clean_reflect::source_equation::check_uint_source_equation(
        environment,
        &source,
        denotation,
        Name::from_string(&format!("CleanSourceTV.{name}.denotes")),
    )
    .map_err(|error| format!("original-source conditional equation REFUSED: {error}"))
}

#[path = "emit_trust_ir_tv_binding.rs"]
mod binding;
pub(crate) use binding::certify_backend_translation_bound_in_environment;
use binding::{bound_binding, BindingInputs};
#[path = "emit_trust_ir_tv_comparand.rs"]
mod comparand;
use comparand::comparand_lambda;
pub(crate) use comparand::source_comparand_bytes;

// Keep test-only items after production for the structural license audit.
#[cfg(test)]
pub(crate) use binding::certify_backend_translation_bound;
#[cfg(test)]
pub(crate) use binding::kernel_tv_gate;
#[cfg(test)]
use clean_reflect::denote_source;

#[cfg(test)]
#[path = "emit_trust_ir_tv_tests.rs"]
mod tests;
