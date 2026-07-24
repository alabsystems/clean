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
//! unrecorded or deallocated cell — REFUSES the mint fail-closed (the decl
//! stays outside the fragment: a SKIP with the auditable walker reason).
//!
//! **`Dealloc` is invisible to the value equation** (a pure value denotation
//! cannot observe deallocation), so the mint gate adds a STRUCTURAL
//! alloc/dealloc balance check for in-fragment functions: every `HeapAlloc`
//! must be `Dealloc`ed exactly once, by its own base pointer value (count +
//! address-match per allocation). A dropped or doubled `Dealloc` is a
//! REFUSAL — a detected wrong-code emission — not a skip; the kernel
//! equation does not (and cannot) carry this claim. TRUST.md boundary-6
//! wording: the heap fragment's kernel claim is value-correctness; the
//! RC/dealloc discipline is checked structurally here (and separately by
//! trust-ir's validator rules for ARC).
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
//! * **In-fragment but the alloc/dealloc balance is broken**: likewise
//!   REFUSED (see above).
//! * A serialization failure of the payload likewise refuses (never a
//!   half-built certificate).
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
//!    audit it.
//! 3. The certificate says the emitted function DENOTES the source under the
//!    mod-2^w vocabulary. It does not (and does not claim to) certify
//!    anything outside the fragment: RC insertion, ctor lowering, control
//!    flow, calls, the runtime — all remain exactly as unverified as before.

use std::collections::BTreeMap;

use clean_kernel::env::{Declaration, Environment};
use clean_kernel::{BinderInfo, Expr, Name};
use clean_reflect::{
    denote_function, denote_source, denote_source_nat, heap_vocab_declarations, tv_proof_term,
    tv_statement, tv_theorem_name, RecordVocab, ReflectError,
};
use trust_ir::inst::Inst;
use trust_ir::proof::{
    clean_cic_lineage_digest, CleanCicKernelRecheck, ObligationKind, ProofCertificate,
    ProofEvidence, ProofObligation, ProofStatus,
};
use trust_ir::ty::Ty;
use trust_ir::value::ProofId;
use trust_ir::Function;
use trust_ir::Module;

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

/// Outcome of a [`certify_backend_translation`] run.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
#[non_exhaustive]
pub struct TvMintReport {
    /// Decl names whose emitted function was kernel-certified to denote its
    /// original definition (obligation + certificate attached).
    pub certified: Vec<String>,
    /// Decls skipped fail-closed with the (auditable) reason — out of the
    /// fragment on either side, or no emitted function of that name. No
    /// obligation is attached for these.
    pub skipped: Vec<(String, String)>,
    /// Decls where BOTH sides denoted but the kernel REFUSED the equation
    /// (or the certificate could not be soundly built). This is the
    /// miscompile detector: an in-fragment emit that provably does NOT denote
    /// its source. No obligation is attached; pipeline wiring escalates this
    /// to a hard error.
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
///
/// See the module docs for exactly what is (and is not) certified.
#[must_use]
pub fn certify_backend_translation(
    module: &mut Module,
    originals: &[(String, Expr)],
) -> TvMintReport {
    let mut report = TvMintReport::default();

    // Fresh, collision-free obligation ids (after any pre-existing ones —
    // e.g. the give-back pass that `ModuleBuilder::build` runs by default).
    let mut next_id = module
        .proof_obligations
        .iter()
        .map(|o| o.id.index())
        .max()
        .map_or(0, |m| m + 1);

    // name -> its certified TV obligation id (this run). A caller (Fragment-3b)
    // is certified only AFTER every callee it names is here, so its
    // `InheritedFromCallee` composition is grounded. We iterate to a fixpoint:
    // each pass certifies leaves/callers whose callees are all certified, and
    // defers callers with an as-yet-uncertified callee; when a pass certifies
    // nothing, the still-deferred decls can never compose and are skipped.
    let mut certified_tv: BTreeMap<String, ProofId> = BTreeMap::new();
    let mut pending: Vec<&(String, Expr)> = originals.iter().collect();

    loop {
        let mut progressed = false;
        let mut deferred: Vec<&(String, Expr)> = Vec::new();
        for item in pending {
            match attempt_certify(module, &item.0, &item.1, &certified_tv, &mut next_id) {
                Attempt::Certified {
                    oid,
                    obligation,
                    cert,
                    inherited,
                } => {
                    module.proof_obligations.push(obligation);
                    module.proof_certificates.push(cert);
                    module.proof_certificates.extend(inherited);
                    certified_tv.insert(item.0.clone(), oid);
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

    report
}

/// The outcome of attempting to certify ONE decl in a fixpoint pass.
enum Attempt {
    /// Kernel-certified: attach the obligation, its CleanCic cert, and one
    /// `InheritedFromCallee` cert per callee (the compositional grounding).
    Certified {
        oid: ProofId,
        obligation: ProofObligation,
        cert: ProofCertificate,
        inherited: Vec<ProofCertificate>,
    },
    /// Out of fragment (either side), or no emitted function — no obligation.
    Skip(String),
    /// Both sides denoted but the kernel REFUSED (the miscompile detector) —
    /// no obligation; pipeline wiring escalates to a hard error.
    Refused(String),
    /// In-fragment but a named callee is not yet certified — retry next pass.
    DeferCallee,
}

/// STRUCTURAL alloc/dealloc balance check (Fragment-4, honesty note 1): every
/// `HeapAlloc` result must be `Dealloc`ed EXACTLY ONCE, and every `Dealloc`
/// must cite an allocation's own base pointer value (count + address-match
/// per allocation). The value equation cannot observe deallocation, so this
/// is the emit gate's claim, not the kernel's — a violation on an otherwise
/// in-fragment function is a detected wrong-code emission (REFUSED).
fn alloc_dealloc_balance(func: &Function) -> Result<(), String> {
    let mut dealloc_count: BTreeMap<u32, usize> = BTreeMap::new();
    for block in &func.blocks {
        for node in &block.body {
            if let Inst::HeapAlloc { .. } = &node.inst {
                if let [r] = node.results.as_slice() {
                    dealloc_count.insert(r.index(), 0);
                }
            }
        }
    }
    for block in &func.blocks {
        for node in &block.body {
            if let Inst::Dealloc { ptr } = &node.inst {
                match dealloc_count.get_mut(&ptr.index()) {
                    Some(c) => *c += 1,
                    None => {
                        return Err(format!(
                            "alloc/dealloc balance: Dealloc of %{} which is not a \
                             HeapAlloc base pointer (address-match violated)",
                            ptr.index()
                        ));
                    }
                }
            }
        }
    }
    for (alloc, count) in &dealloc_count {
        match count {
            1 => {}
            0 => {
                return Err(format!(
                    "alloc/dealloc balance: allocation %{alloc} has no Dealloc (dropped \
                     Dealloc — a leak the value equation cannot see)"
                ));
            }
            n => {
                return Err(format!(
                    "alloc/dealloc balance: allocation %{alloc} has {n} Deallocs (doubled \
                     Dealloc — a double-free the value equation cannot see)"
                ));
            }
        }
    }
    Ok(())
}

/// Attempt to certify `name`'s emitted function against its `defn`, composing
/// in each callee's already-certified TV obligation. Never mutates `module`;
/// the driver attaches the returned obligation/certs.
fn attempt_certify(
    module: &Module,
    name: &str,
    defn: &Expr,
    certified_tv: &BTreeMap<String, ProofId>,
    next_id: &mut u32,
) -> Attempt {
    let Some(func) = module.functions.iter().find(|f| f.name == name) else {
        return Attempt::Skip("no emitted trust-ir function of this name".to_string());
    };
    let fid = func.id;

    // (1) Denote the EMITTED function (fail-closed outside the fragment). This
    // also yields the canonical callee list (Fragment-3b). A `WrongEmission`
    // is an in-fragment structural violation a correct lowering can never
    // produce (uninitialized read, self-inconsistent struct layout) — a
    // detected wrong-code emission, REFUSED like the balance gate below,
    // never an out-of-fragment skip.
    let lhs = match denote_function(module, func) {
        Ok(d) => d,
        Err(e @ ReflectError::WrongEmission(_)) => {
            return Attempt::Refused(format!("walker REFUSED (structural): {e}"));
        }
        Err(e) => return Attempt::Skip(format!("emitted side: {e}")),
    };

    // (1a) Fragment-4 STRUCTURAL gate: the function is in-fragment, so a
    // broken alloc/dealloc balance is a detected wrong-code emission — a
    // REFUSAL, never a skip (the kernel value equation cannot carry this).
    if let Err(reason) = alloc_dealloc_balance(func) {
        return Attempt::Refused(reason);
    }

    // (1b) COMPOSITION GATE: every named callee must already be TV-certified in
    // this run (so its `InheritedFromCallee` grounding exists). Otherwise defer.
    for (cn, _) in &lhs.callees {
        if !certified_tv.contains_key(cn) {
            return Attempt::DeferCallee;
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
    let rhs = if nat_return {
        match denote_source_nat(defn, &lhs.callees) {
            Ok(d) => d,
            Err(e) => return Attempt::Skip(format!("source side (nat): {e}")),
        }
    } else {
        match denote_source(
            defn,
            lhs.width,
            &lhs.callees,
            &RecordVocab::from_module(module),
        ) {
            Ok(d) => d,
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

    let callee_arities: Vec<usize> = lhs.callees.iter().map(|(_, a)| *a).collect();

    // (4) THE KERNEL JUDGMENT: declare the equation as a real Theorem in the
    // ground prelude environment. For the (parametric-in-callees) `Eq.refl`
    // term, `add_decl` reduces to definitional equality of the two open
    // denotations — the kernel decides it, universally over the callee symbols.
    let thm = tv_theorem_name(name);
    let stmt = tv_statement(&callee_arities, lhs.arity, &lhs.body, &rhs.body);
    let proof = tv_proof_term(&callee_arities, lhs.arity, &lhs.body);
    let mut env = match Environment::try_with_prelude() {
        Ok(env) => env,
        Err(e) => return Attempt::Refused(format!("prelude environment failed: {e:?}")),
    };
    // Fragment-4 heap vocabulary: three DEFINITIONAL combinators the kernel
    // unfolds (no axioms — the FOUNDATIONAL floor below is unaffected). The
    // matching trust-ir re-checker vocabulary has NOT landed yet, so an
    // independent recheck of a heap cert currently REJECTS on the unknown
    // `CleanTV.h*` constants (fail-closed) until trust-ir installs them.
    for decl in heap_vocab_declarations() {
        if let Err(e) = env.add_decl(decl) {
            return Attempt::Refused(format!("heap vocabulary failed to install: {e:?}"));
        }
    }
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

    // (5) Build the decodable payload: comparand as `fun (G0…)(x…) => rhs.body`
    // (the re-checker strips `callees.len() + arity` binders), proof term as
    // minted. bincode-1-of-Expr. Serialization failure refuses (fail-closed).
    let with_params = (0..rhs.arity).fold(rhs.body.clone(), |acc, _| {
        Expr::lam(BinderInfo::Default, Expr::const_str("Nat"), acc)
    });
    let rhs_lambda = callee_arities.iter().rev().fold(with_params, |acc, ca| {
        Expr::lam(BinderInfo::Default, callee_fn_ty(*ca), acc)
    });
    let (term, context) = match (bincode::serialize(&proof), bincode::serialize(&rhs_lambda)) {
        (Ok(t), Ok(c)) => (t, c),
        _ => return Attempt::Refused("certificate payload failed to serialize".to_string()),
    };

    // (6) Build the obligation + kernel-re-checkable certificate.
    let oid = ProofId::new(*next_id);
    *next_id += 1;
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
        formula: None,
        function: Some(fid),
        source: None,
    };
    let lineage = clean_cic_lineage_digest(&obligation);
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
            }),
        },
    };

    // (7) One `InheritedFromCallee` certificate per callee: the caller's
    // parametric equation is grounded at each callee's OWN certified meaning
    // (the "cross-language proofs compose" thesis, enforced by the B5 validator
    // — it checks each cited callee obligation is itself ground-discharged).
    let inherited: Vec<ProofCertificate> = lhs
        .callees
        .iter()
        .map(|(cn, _)| {
            let callee_fid = module
                .functions
                .iter()
                .find(|f| &f.name == cn)
                .expect("callee was resolved during denotation")
                .id;
            ProofCertificate {
                obligation: oid,
                prover: "clean-backend-tv-compose".to_string(),
                evidence: ProofEvidence::InheritedFromCallee {
                    callee: callee_fid,
                    obligation: certified_tv[cn],
                },
            }
        })
        .collect();

    Attempt::Certified {
        oid,
        obligation,
        cert,
        inherited,
    }
}

#[cfg(test)]
#[path = "emit_trust_ir_tv_tests.rs"]
mod tests;
