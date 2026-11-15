// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Semantic module diff.
//!
//! This module computes the difference between two `Module` values at the
//! structural level, ignoring cosmetic differences that arise from how the
//! producer happened to arena-allocate identifiers.
//!
//! # What is ignored
//!
//! * `FuncId`, `BlockId`, `ValueId`, `StructId`, `EnumId`, `RecordId`,
//!   `ClosureTyId`, `FuncTyId`, `TyId` numbering. Two modules that are
//!   identical up to a renumbering of these ids are considered equal.
//! * Declaration order of functions/structs/enums/records/closure types,
//!   globals, spec modules and imports in the module.
//! * Claim-style debug metadata: `SourceSpan` and lexical-scope indices on
//!   instruction nodes, plus function `value_names` and scope trees. These do
//!   not affect execution or proof authority. `source_provenance` is explicitly
//!   excluded from this list: it is proof-relevant function metadata.
//!   The scope tree — parents, opening spans and the WS4.19 inlining chain
//!   links (`ScopeData.inlined_at`) — can be OPTED IN with
//!   [`DiffOptions::include_debug`], which reports a change as the `"scopes"`
//!   function meta row; the default lane is unchanged by the option.
//! * The module `name` (reported as the diff header, never as a change) and
//!   the STRINGS of the debug-info `files` table (only spans index it, and
//!   spans are ignored). The table's LENGTH is compared (the `"files"` module
//!   row), mirroring the portable import identity
//!   ([`crate::IdentityScheme::V3`], roadmap WS4.10 / decision DG-16), which
//!   projects every `files[i]` string to `""` and keeps the length: a checkout
//!   move is cosmetic, a file entering or leaving the table is not.
//! * `obligation_diagnostics` (verifier messages keyed by obligation — a
//!   sidecar, not authority) and rows of the definition tables (`structs`,
//!   `enums`, `records`, `closure_types`, `func_types`, `types`, `universes`,
//!   `predicates`) that nothing compared references: a definition is
//!   fingerprinted structurally at every use, so an unused row is invisible.
//!
//! Nothing else is ignored (under default options; `--ignore-proofs`
//! additionally suppresses only the proof comparisons listed below). In
//! particular EVERY field of a `Function`, a `Global`, a `SpecModule`, the
//! `TargetInfo` and a `ModuleImport` that is not named above is compared, and
//! a change to it is a reported difference (audit rows
//! `b1.gap.diff_blind_to_*`, 2026-09-17: the diff used to read exactly two
//! function-metadata fields, so a Clean body losing its codegen license, an
//! exported symbol going `internal`, a global's initializer changing, or a
//! module being retargeted all produced an EMPTY diff while
//! `Module::stable_digest` moved). The same holds for every field of the
//! proof channel — a `FunctionSummary`, a `ProofFormula`, a `ProofObligation`
//! and a `ProofCertificate` (roadmap WS4.13).
//!
//! That list is enforced at COMPILE time, not by review: each carrier the
//! diff reads is destructured EXHAUSTIVELY (no `..`) where it is compared, with
//! every field either read or named `_` beside the reason it is ignored — the
//! WS4.2 `text_loss` pattern. A field added to `Module`, `Function`,
//! `FuncAttrs`, `ParamAttrs`, `InstrNode`, `Block`, `Global`, `TargetInfo`,
//! `ModuleImport`, `ExternRef`, `TupleLayoutDescriptor`, `DropGlueEntry`,
//! `ClosureLayoutDescriptor`, `StructDef`, `EnumDef`, `SpecModule`,
//! `SpecAnchor`, `FunctionSummary`, `ProofFormula`, `ClauseBinding`,
//! `ProofObligation`, `ObligationSite`, `SpecObligationRef`,
//! `ProofCertificate`, `CoverageAssurance`, `ProofContext`, the kernel
//! re-check directive, its
//! `CertificateBinding`, `SourceDefinitionRef` or `IslandEnvironment` fails to
//! build here until it is classified. (`source_provenance` is compared with
//! `!=`, which is total over every field by construction.) The dynamic half is
//! the conformance target
//! `diff_fields`: every single-field mutant that moves
//! `Module::stable_digest` must produce a non-empty diff, except the debug
//! fields listed above.
//!
//! # What is compared
//!
//! * Declared tuple layouts and (v58) declared closure layouts, including
//!   unused rows, each keyed by its STRUCTURAL type identity. These are
//!   execution metadata and are compared even with `--ignore-proofs`.
//! * A struct or enum definition's v58 nominal key (`origin`), wherever the
//!   definition is fingerprinted: the key splits type identity, so gaining,
//!   losing or re-keying it is a change.
//! * Module-level metadata, each reported as a `MetaChange` in
//!   `module_meta_changes` and never gated by `--ignore-proofs`:
//!   `target_info` (always, not only when tuple layouts are declared),
//!   `global_asm`, `completeness`, `files` (the debug file table's LENGTH;
//!   see above), `imports` (the authenticated dependency table, compared as a
//!   set), `drop_glue` (v55: the module drop-glue table, compared as a sorted
//!   multiset of key type and glue SYMBOL, so declaration order and function
//!   renumbering stay cosmetic while a duplicated row is reported), the
//!   per-name `spec_module <name>` rows (matched by machine name,
//!   declaration order ignored; an anchor's `FuncId`s are resolved to the
//!   function's symbol, so function renumbering stays cosmetic while
//!   re-pointing an anchor is reported), and the per-name `global @<name>` rows
//!   (matched by link-time symbol, declaration order ignored; every field of a
//!   `Global` — type, mutability, initializer, linkage, TLS model, alignment,
//!   section, visibility and `#[used]` retention — is part of the fingerprint).
//!   A `GlobalAddr` instruction is fingerprinted by the SYMBOL its `GlobalId`
//!   names, so reordering `Module.globals` is cosmetic too.
//! * The set of function names (added / removed).
//! * Per matched function, its metadata, each reported as a `MetaChange` in
//!   `meta_changes` and never gated by `--ignore-proofs`: `producer`,
//!   `source_provenance`, `body_gate` (the codegen license), `display_path`,
//!   `section` / `visibility` / `retained` (v45), `linkage`, `calling_conv`,
//!   `signature` (the `FuncTy`, resolved structurally so `FuncTyId`
//!   renumbering is still cosmetic) and `attrs`.
//! * Per matched function: block shape (number of blocks reachable from
//!   entry), block parameter types, and instruction bodies positionally
//!   after block alignment.
//! * Per matched instruction: the `Inst` variant and all type/constant/
//!   literal payloads it carries, compared via a structural fingerprint
//!   that resolves id references through each module's own tables, and the
//!   node's result ARITY (its result ids are renumbering, their count is
//!   not).
//! * `ProofAnnotation` sets attached to each function and each instruction
//!   node (unless `--ignore-proofs` is set).
//! * The function's separate-compilation contract (`summary`: `proved`,
//!   `params`, every `requires` / `ensures` / `decreases` clause and
//!   `backed_by`), reported through the proof channel.
//! * Module proof state: `proof_obligations` (matched by claim — kind, scope
//!   function name, description, formula, embedded source identity, the IR
//!   `site` it states a check about and the temporal `spec` property it
//!   discharges — with `status` reported as a change), `proof_certificates`
//!   (matched by obligation claim + prover + evidence + coverage
//!   `assurance`; a `CleanCic` payload's kernel re-check directive — module,
//!   anchor, theorems, admitted axioms and its `CertificateBinding` — is part
//!   of the evidence), and per-instruction `proof_context` (its
//!   `assumes`/`establishes` obligation references resolved to claim keys).
//!   Every `ProofFormula` — a summary clause or an obligation's formula — is
//!   fingerprinted with ALL of its fields, the v41 clause `bindings` (each
//!   name's sort and IR place) included. All unless `--ignore-proofs` is set,
//!   which suppresses every proof comparison and preserves the older
//!   proof-insensitive behavior.
//! * Every function-local id a proof-channel row carries is resolved the way
//!   the body is: an obligation `site` names its function by symbol and its
//!   block by DFS visit index, a clause's `Value` place names its SSA value by
//!   canonical walk index, and an `InheritedFromCallee` certificate names its
//!   callee by symbol and its obligation by claim — so renumbering stays
//!   cosmetic while re-pointing any of them is reported. The same holds for a
//!   `ProofRef` annotation, which names its obligation by CLAIM (as a
//!   certificate and a proof context do): re-pointing it — including by
//!   renumbering the obligation table under an unchanged index — is reported.
//!
//! # Alignment algorithm
//!
//! 1. Functions are matched by name. Added/removed names are reported.
//! 2. Within a matched function pair, blocks are walked in deterministic
//!    DFS preorder starting from each function's `entry` block, following
//!    successor edges in the order they appear in the terminator. Any
//!    blocks not reachable from entry are appended in block-id order so
//!    dead blocks still contribute to the diff.
//! 3. The i-th block visited in A is matched with the i-th block visited
//!    in B. If the walks produce different counts, the trailing blocks
//!    are reported as `Added` / `Removed`.
//! 4. Within a matched block pair, instructions are compared positionally.
//!    Because the walk defines a canonical block numbering on each side,
//!    operand `ValueId`s are remapped through a `value_map` keyed by
//!    each side's SSA layout so that cross-module fingerprints line up
//!    after renumbering.
//!
//! The matcher is deterministic: it never re-orders on its own, and it
//! never performs a best-match search. Consumers get stable output across
//! runs.
//!
//! # Exit-code contract (for the `trust-ir-diff` CLI)
//!
//! * `0` — the two modules are structurally isomorphic (empty `Diff`).
//! * `1` — at least one structural difference was found.
//! * `2` — parse or validation error (the CLI, not this module, maps errors
//!   to this code; this module never parses).
//!
//! # Limitations (non-goals)
//!
//! * No attempt is made to decide semantic equivalence. Two functions that
//!   compute the same IR program via different instruction shapes will be
//!   reported as different. That is the verifier's job, not the diff tool's.
//! * No three-way merge is produced.

use crate::{
    AttrEntry, AttrValue, Block, DropGlueEntry, Function, Module,
    constant::Constant,
    dialect::DialectInst,
    inst::{BindingFrameDef, BindingSlot, Inst, SwitchCase},
    node::InstrNode,
    proof::{
        Divergence, ProofAnnotation, ProofCertificate, ProofContext, ProofEvidence,
        ProofObligation, write_proof_obligation_source_identity_stable,
    },
    ty::{
        ClosureTy, EnumDef, EnumVariant, FatPtrKind, FieldDef, FuncTy, RecordDef, SetRepr,
        StructDef, Ty,
    },
    value::{
        BlockId, ClosureTyId, EnumId, FuncId, FuncTyId, ProofId, ProofTag, RecordId, StructId,
        TyId, ValueId,
    },
};
use core::fmt::Write as _;
use std::collections::HashMap;

// -----------------------------------------------------------------------------
// Public diff types
// -----------------------------------------------------------------------------

/// Options controlling diff behavior.
#[derive(Debug, Clone, Copy, Default)]
pub struct DiffOptions {
    /// If true, `ProofAnnotation`s on functions and instruction nodes are
    /// not compared. Two modules that differ only in their proof coverage
    /// are then reported as equal.
    pub ignore_proofs: bool,
    /// If true, the per-function lexical scope TREE (`Function.scopes`:
    /// parents, opening spans and WS4.19 inlining chain links) is compared
    /// too and a change is reported as the `"scopes"` meta row. Off by
    /// default: scopes are claim-style debug metadata with no execution or
    /// proof authority, so the default diff keeps ignoring them. This is a
    /// DEBUG lane, not an authority one — turning it on never changes what
    /// the default lane reports.
    pub include_debug: bool,
}

/// Result of comparing two modules.
#[derive(Debug, Clone, PartialEq)]
pub struct Diff {
    pub module_name_a: String,
    pub module_name_b: String,
    pub changes: Vec<FuncChange>,
    /// Execution-relevant module metadata, compared even under `ignore_proofs`.
    pub module_meta_changes: Vec<MetaChange>,
    /// Module-level proof-state changes: differences in `proof_obligations`
    /// and `proof_certificates`. Empty when `ignore_proofs` is set or when
    /// the proof state matches. Per-instruction proof state (`proofs` and
    /// `proof_context`) is reported inside `changes` via `InstrChange`.
    pub proof_state_changes: Vec<ProofStateChange>,
}

impl Diff {
    /// Returns `true` when there are no recorded differences.
    pub fn is_empty(&self) -> bool {
        self.changes.is_empty()
            && self.module_meta_changes.is_empty()
            && self.proof_state_changes.is_empty()
    }

    /// Exit code for CLI use: 0 if isomorphic, 1 if different.
    ///
    /// Parse/validation errors are the CLI's concern and use exit code 2.
    pub fn exit_code(&self) -> i32 {
        if self.is_empty() { 0 } else { 1 }
    }
}

/// A function-level change.
#[derive(Debug, Clone, PartialEq)]
pub enum FuncChange {
    /// Function name present in module B but not in module A.
    Added { name: String },
    /// Function name present in module A but not in module B.
    Removed { name: String },
    /// Function exists on both sides but their bodies differ.
    Changed {
        name: String,
        /// Changes in the function's own `proofs` vector. Empty when
        /// `ignore_proofs` is set or when proofs match.
        proof_changes: Vec<ProofChange>,
        /// Changes at the block level.
        block_changes: Vec<BlockChange>,
        /// Function-metadata changes: `producer`, `source_provenance`,
        /// `body_gate`, `display_path`, `section`, `visibility`, `retained`,
        /// `linkage`, `calling_conv`, `signature` and `attrs` (see
        /// [`MetaChange::field`]).
        /// NOT gated by `ignore_proofs` — none of these is proof coverage.
        meta_changes: Vec<MetaChange>,
    },
}

/// A metadata change (non-proof, non-body), on a function or the module.
#[derive(Debug, Clone, PartialEq)]
pub struct MetaChange {
    /// Which metadata field changed.
    ///
    /// On a function (`FuncChange::Changed::meta_changes`) one of
    /// `"producer"`, `"source_provenance"`, `"body_gate"`, `"display_path"`,
    /// `"section"`, `"visibility"`, `"retained"`, `"linkage"`,
    /// `"calling_conv"`, `"signature"`, `"attrs"`, or — only under
    /// [`DiffOptions::include_debug`] — `"scopes"` (the lexical scope tree
    /// with its WS4.19 inlining chain links).
    ///
    /// On the module (`Diff::module_meta_changes`) one of `"tuple_layouts"`,
    /// `"target_info"`, `"global_asm"`, `"completeness"`, `"imports"`,
    /// `"drop_glue"`, `"closure_layouts"`, a per-machine
    /// `"spec_module <name>"` row, or a per-symbol `"global @<name>"` row (an
    /// added / removed global renders the absent side as `"-"`), or `"files"`
    /// (the debug file table's length).
    pub field: String,
    /// Rendered A-side value; `"-"` when absent on that side.
    pub before: String,
    /// Rendered B-side value; `"-"` when absent on that side.
    pub after: String,
}

/// A block-level change within a matched function.
#[derive(Debug, Clone, PartialEq)]
pub enum BlockChange {
    /// The i-th block visited in B has no counterpart in A.
    /// `visit` is the DFS visit index (0 = entry).
    Added { visit: usize },
    /// The i-th block visited in A has no counterpart in B.
    Removed { visit: usize },
    /// Block structure differs (parameter count or parameter types).
    StructureDiffers { visit: usize, detail: String },
    /// Block bodies differ.
    InstrDiff {
        visit: usize,
        instr_changes: Vec<InstrChange>,
    },
}

/// An instruction-level change within a matched block.
#[derive(Debug, Clone, PartialEq)]
pub enum InstrChange {
    /// Instruction appears in B at this index but not in A.
    Added { index: usize, summary: String },
    /// Instruction appears in A at this index but not in B.
    Removed { index: usize, summary: String },
    /// Instructions at this index differ. `before` / `after` are one-line
    /// summaries suitable for unified-diff output.
    Replaced {
        index: usize,
        before: String,
        after: String,
    },
}

/// A proof-annotation-level change on a function or instruction node.
#[derive(Debug, Clone, PartialEq)]
pub enum ProofChange {
    Added { name: String },
    Removed { name: String },
}

/// A module-level proof-state change.
///
/// Obligations and certificates are matched across modules by a structural
/// fingerprint that ignores the arena `ProofId` numbering (consistent with
/// the rest of the diff), so renumbering a module's proof table alone never
/// surfaces here. An obligation is keyed by its *claim* — kind, formula,
/// description, and (function-name-resolved) scope — and its `status` is the
/// mutable field that produces a `ObligationStatusChanged` when it differs.
#[derive(Debug, Clone, PartialEq)]
pub enum ProofStateChange {
    /// An obligation present in B but not in A. `obligation` is the matched
    /// claim key; `status` is its status on the B side.
    ObligationAdded { obligation: String, status: String },
    /// An obligation present in A but not in B. `status` is its A-side status.
    ObligationRemoved { obligation: String, status: String },
    /// An obligation present on both sides whose status differs.
    ObligationStatusChanged {
        obligation: String,
        before: String,
        after: String,
    },
    /// A certificate present in B but not in A.
    CertificateAdded { certificate: String },
    /// A certificate present in A but not in B.
    CertificateRemoved { certificate: String },
}

// -----------------------------------------------------------------------------
// Public API
// -----------------------------------------------------------------------------

/// Diff two modules with default options.
pub fn diff(a: &Module, b: &Module) -> Diff {
    diff_with(a, b, DiffOptions::default())
}

/// Diff two modules with explicit options.
pub fn diff_with(a: &Module, b: &Module, opts: DiffOptions) -> Diff {
    // Compile-time coverage (roadmap WS4.13, the WS4.2 `text_loss` pattern):
    // every `Module` field is named here with WHERE it is compared, or why it
    // is not. A new field fails to build until it is classified.
    let Module {
        name: _,                   // the diff header, never a change (module doc)
        functions: _,              // matched by symbol below
        structs: _,                // fingerprinted structurally at every use
        enums: _,                  // fingerprinted structurally at every use
        records: _,                // fingerprinted structurally at every use
        closure_types: _,          // fingerprinted structurally at every use
        globals: _,                // `global @<name>` rows
        func_types: _,             // fingerprinted structurally at every use
        types: _,                  // fingerprinted structurally at every use
        proof_obligations: _,      // `proof_state_diff`
        proof_certificates: _,     // `proof_state_diff`
        target_info: _,            // `target_info` row
        files: _,                  // `files` row: the LENGTH (strings are debug)
        obligation_diagnostics: _, // IGNORED: a verifier-message sidecar, not authority
        spec_modules: _,           // `spec_module <name>` rows
        universes: _,              // fingerprinted structurally at every use
        predicates: _,             // fingerprinted structurally at every use
        global_asm: _,             // `global_asm` row
        imports: _,                // `imports` row + every `ExternRef`
        tuple_layouts: _,          // `tuple_layouts` row
        completeness: _,           // `completeness` row
        drop_glue: _,              // `drop_glue` row (v55, amendment D)
        closure_layouts: _,        // `closure_layouts` row (v58, WS3.9)
        blobs: _,                  // `blobs` row (v70): each digest and its byte count
    } = a;
    let mut changes = Vec::new();

    // Build name-indexed maps of functions on each side.
    let mut a_fns: HashMap<&str, &Function> = HashMap::new();
    for f in &a.functions {
        a_fns.insert(f.name.as_str(), f);
    }
    let mut b_fns: HashMap<&str, &Function> = HashMap::new();
    for f in &b.functions {
        b_fns.insert(f.name.as_str(), f);
    }

    // Collect the union of names deterministically.
    let mut names: Vec<&str> = a_fns.keys().copied().collect();
    for k in b_fns.keys() {
        if !a_fns.contains_key(*k) {
            names.push(*k);
        }
    }
    names.sort();

    for name in names {
        let fa = a_fns.get(name).copied();
        let fb = b_fns.get(name).copied();
        match (fa, fb) {
            (Some(_), None) => changes.push(FuncChange::Removed {
                name: name.to_string(),
            }),
            (None, Some(_)) => changes.push(FuncChange::Added {
                name: name.to_string(),
            }),
            (Some(fa), Some(fb)) => {
                // Compile-time coverage of `Function` (see the `Module`
                // destructure above).
                let Function {
                    id: _,                // renumbering: functions are matched by `name`
                    name: _,              // the match key
                    ty: _,                // `signature` row (structural)
                    entry: _,             // the block walk starts here
                    blocks: _,            // `diff_function`
                    proofs: _,            // proof channel (`proof_diff`)
                    calling_conv: _,      // `calling_conv` row
                    linkage: _,           // `linkage` row
                    attrs: _,             // `attrs` row
                    summary: _,           // proof channel (`summary_fp`)
                    producer: _,          // `producer` row
                    value_names: _,       // IGNORED: debug names
                    scopes: _,            // debug lane only (`scopes`, --include-debug)
                    source_provenance: _, // `source_provenance` row
                    body_gate: _,         // `body_gate` row
                    display_path: _,      // `display_path` row
                    section: _,           // `section` row
                    visibility: _,        // `visibility` row
                    retained: _,          // `retained` row
                } = fa;
                let mut proof_changes = if opts.ignore_proofs {
                    Vec::new()
                } else {
                    proof_diff(a, &fa.proofs, b, &fb.proofs)
                };
                // The separate-compilation contract is proof-ish: a changed
                // `requires`/`ensures`/`params`/`proved` is reported through the
                // proof channel (already gated by `ignore_proofs` and already
                // promoting the function to `Changed`).
                if !opts.ignore_proofs {
                    let sa = summary_fp(a, Some(fa), fa.summary.as_ref());
                    let sb = summary_fp(b, Some(fb), fb.summary.as_ref());
                    if sa != sb {
                        proof_changes.push(ProofChange::Removed {
                            name: format!("summary {sa}"),
                        });
                        proof_changes.push(ProofChange::Added {
                            name: format!("summary {sb}"),
                        });
                    }
                }
                // Producer provenance (v23) is function metadata, not proof
                // coverage: a producer flip is reported even under
                // `ignore_proofs`.
                let mut meta_changes = Vec::new();
                if fa.producer != fb.producer {
                    meta_changes.push(MetaChange {
                        field: "producer".to_string(),
                        before: producer_fp(fa.producer.as_ref()),
                        after: producer_fp(fb.producer.as_ref()),
                    });
                }
                if fa.source_provenance != fb.source_provenance {
                    meta_changes.push(MetaChange {
                        field: "source_provenance".to_string(),
                        before: source_provenance_fp(fa.source_provenance.as_ref()),
                        after: source_provenance_fp(fb.source_provenance.as_ref()),
                    });
                }
                // Every remaining Function field is compared too (audit rows
                // b1.gap.diff_blind_to_{body_gate,display_path,
                // function_linkage,calling_conv}). The codegen license is the
                // consumer's refusal hook: Gated -> Ungated / -> None / an
                // authority swap flips `validate_module_for_codegen`, and the
                // diff is the ONLY tool that can show a reviewer that flip
                // (`executable_content_digest_v1` excludes it by design).
                // None of these is proof coverage, so none is gated by
                // `ignore_proofs`.
                push_meta_if_changed(
                    &mut meta_changes,
                    "body_gate",
                    body_gate_fp(a, fa),
                    body_gate_fp(b, fb),
                );
                push_meta_if_changed(
                    &mut meta_changes,
                    "display_path",
                    display_path_fp(fa.display_path.as_deref()),
                    display_path_fp(fb.display_path.as_deref()),
                );
                // v45 (WS3.10): the function's symbol attributes. Each one
                // changes the object a consumer emits, so none is cosmetic.
                push_meta_if_changed(
                    &mut meta_changes,
                    "section",
                    display_path_fp(fa.section.as_deref()),
                    display_path_fp(fb.section.as_deref()),
                );
                push_meta_if_changed(
                    &mut meta_changes,
                    "visibility",
                    fa.visibility.to_string(),
                    fb.visibility.to_string(),
                );
                push_meta_if_changed(
                    &mut meta_changes,
                    "retained",
                    fa.retained.to_string(),
                    fb.retained.to_string(),
                );
                push_meta_if_changed(
                    &mut meta_changes,
                    "linkage",
                    fa.linkage.to_string(),
                    fb.linkage.to_string(),
                );
                push_meta_if_changed(
                    &mut meta_changes,
                    "calling_conv",
                    fa.calling_conv.to_string(),
                    fb.calling_conv.to_string(),
                );
                // The signature is resolved structurally through each side's
                // own `func_types` table, so `FuncTyId` renumbering stays
                // cosmetic while a changed parameter / return list or a
                // vararg flip is reported.
                push_meta_if_changed(
                    &mut meta_changes,
                    "signature",
                    fp_func_ty_ref(a, fa.ty),
                    fp_func_ty_ref(b, fb.ty),
                );
                push_meta_if_changed(
                    &mut meta_changes,
                    "attrs",
                    func_attrs_fp(&fa.attrs),
                    func_attrs_fp(&fb.attrs),
                );
                // Debug lane (opt-in): the lexical scope tree, including a
                // WS4.19 inlining chain link. Excluded by default because
                // scopes carry no authority; included so a reviewer CAN see
                // a chain appear, move or vanish when asked.
                if opts.include_debug {
                    push_meta_if_changed(
                        &mut meta_changes,
                        "scopes",
                        scopes_fp(fa.scopes.as_deref()),
                        scopes_fp(fb.scopes.as_deref()),
                    );
                }
                let block_changes = diff_function(a, b, fa, fb, opts);
                if !proof_changes.is_empty()
                    || !block_changes.is_empty()
                    || !meta_changes.is_empty()
                {
                    changes.push(FuncChange::Changed {
                        name: name.to_string(),
                        proof_changes,
                        block_changes,
                        meta_changes,
                    });
                }
            }
            (None, None) => unreachable!(),
        }
    }

    let proof_state_changes = if opts.ignore_proofs {
        Vec::new()
    } else {
        proof_state_diff(a, b)
    };

    let mut module_meta_changes = Vec::new();
    let layouts_a = tuple_layouts_fp(a);
    let layouts_b = tuple_layouts_fp(b);
    if layouts_a != layouts_b {
        module_meta_changes.push(MetaChange {
            field: "tuple_layouts".into(),
            before: layouts_a,
            after: layouts_b,
        });
    }
    // v58 declared closure layouts, diffed on exactly the same footing: a
    // producer that reorders two captures changes the module's byte image,
    // which a diff that ignored this table would render as no change at all.
    let closures_a = closure_layouts_fp(a);
    let closures_b = closure_layouts_fp(b);
    if closures_a != closures_b {
        module_meta_changes.push(MetaChange {
            field: "closure_layouts".into(),
            before: closures_a,
            after: closures_b,
        });
    }
    // v70 weight blobs: the table is part of the module's byte image (its
    // `stable_digest`), so a changed weight is a change even though no body
    // moves. Rows are compared as written, recorded digest AND bytes, so a
    // row whose bytes changed under an unchanged recorded digest (refused by
    // the validator) still renders.
    push_meta_if_changed(&mut module_meta_changes, "blobs", blobs_fp(a), blobs_fp(b));
    // Target information is execution metadata for EVERY module, not only one
    // that declares tuple layouts (audit row
    // b1.gap.diff_blind_to_spec_modules_and_target: retargeting
    // aarch64-apple-darwin -> x86_64-linux used to be an empty diff). This row
    // replaces the older `tuple_layout_target` row, which fired only when a
    // tuple table was present.
    push_meta_if_changed(
        &mut module_meta_changes,
        "target_info",
        target_info_fp(a.target_info.as_ref()),
        target_info_fp(b.target_info.as_ref()),
    );
    // Module-level `global_asm!` blocks define symbols the rest of the module
    // may reference; a consumer must refuse rather than drop them, so a
    // reviewer must see them change.
    push_meta_if_changed(
        &mut module_meta_changes,
        "global_asm",
        format!("{:?}", a.global_asm),
        format!("{:?}", b.global_asm),
    );
    // WS5.3b: the producer's completeness claim. A claim appearing,
    // disappearing, or flipping between `Complete` and `Partial` (or a
    // partial claim's rows changing) is a change in what the module says
    // about itself; `None` and `Complete` are distinct here as everywhere.
    push_meta_if_changed(
        &mut module_meta_changes,
        "completeness",
        format!("{:?}", a.completeness),
        format!("{:?}", b.completeness),
    );
    // The debug file table's LENGTH, never its strings: the portable import
    // identity (`IdentityScheme::V3`, WS4.10 / DG-16) projects every
    // `files[i]` to `""` and keeps the length, so a checkout move (every path
    // rewritten) is cosmetic here as it is there, while a file entering or
    // leaving the table moves `Module::stable_digest` and is reported.
    push_meta_if_changed(
        &mut module_meta_changes,
        "files",
        a.files.len().to_string(),
        b.files.len().to_string(),
    );
    // The authenticated dependency table. `ExternRef`s already resolve through
    // it (`fp_import_ref`), but an import nothing references yet — or a
    // digest/producer re-pin of one — is authority metadata in its own right.
    // Compared as a set: the table is content-interned, so its order carries
    // no information a reviewer needs.
    push_meta_if_changed(
        &mut module_meta_changes,
        "imports",
        imports_fp(a),
        imports_fp(b),
    );
    // Amendment D (§20): the drop-glue table decides what every `Drop` /
    // `DropInvoke` EXECUTES, so a row appearing, disappearing or re-pointing
    // is a change to the program even when no body changed. Compared as a
    // set of (key type, glue SYMBOL): function renumbering stays cosmetic.
    push_meta_if_changed(
        &mut module_meta_changes,
        "drop_glue",
        drop_glue_fp(a),
        drop_glue_fp(b),
    );
    // Spec modules (matched by machine name) and globals (matched by link-time
    // symbol): declaration order is cosmetic, content is not. Audit rows
    // b1.gap.diff_blind_to_globals / _spec_modules_and_target: a global's
    // initializer changing altered the program's RESULT (60 -> 62) while the
    // diff stayed empty, because nothing in this module read `Module.globals`.
    diff_named_rows(
        &mut module_meta_changes,
        "spec_module ",
        a.spec_modules
            .iter()
            .map(|s| (s.name.as_str(), spec_module_fp(a, s))),
        b.spec_modules
            .iter()
            .map(|s| (s.name.as_str(), spec_module_fp(b, s))),
    );
    diff_named_rows(
        &mut module_meta_changes,
        "global @",
        a.globals.iter().map(|g| (g.name.as_str(), global_fp(a, g))),
        b.globals.iter().map(|g| (g.name.as_str(), global_fp(b, g))),
    );

    Diff {
        module_name_a: a.name.clone(),
        module_name_b: b.name.clone(),
        changes,
        module_meta_changes,
        proof_state_changes,
    }
}

/// Declaration order and arena TyIds are cosmetic; offset order and duplicate
/// rows are not. A vector (not a set) preserves the descriptor multiplicity.
/// The drop-glue table as a sorted set of `key => @glue-symbol` rows (a
/// dangling glue id keeps its raw index, a distinct spelling).
fn drop_glue_fp(m: &Module) -> String {
    let mut rows: Vec<String> = m
        .drop_glue
        .iter()
        .map(|row| {
            // Every field of a row is read (compile-time coverage, WS4.13).
            let DropGlueEntry { glue, ty } = row;
            let glue = match m.function_by_id(*glue) {
                Some(function) => format!("@{}", function.name),
                None => format!("#dangling {}", glue.index()),
            };
            format!("{}=>{glue}", fp_ty(m, ty))
        })
        .collect();
    rows.sort();
    format!("[{}]", rows.join(","))
}

fn tuple_layouts_fp(m: &Module) -> String {
    // This API does not validate its inputs, but must not traverse a malformed
    // by-value cycle in the newly inspected table. The CLI rejects these inputs.
    if let Err(error) = m.validate_tuple_layouts() {
        return format!(
            "invalid {error:?}: {:?}; types={:?}",
            m.tuple_layouts, m.types
        );
    }
    let mut rows: Vec<_> = m
        .tuple_layouts
        .iter()
        .map(|layout| {
            // Compile-time coverage (roadmap WS4.13): every field is read.
            let crate::TupleLayoutDescriptor {
                tuple_type,
                size,
                align,
                field_offsets,
            } = layout;
            format!(
                "{} size={} align={} offsets={:?}",
                fp_tyid_ref(m, *tuple_type),
                size,
                align,
                field_offsets
            )
        })
        .collect();
    rows.sort();
    format!("{rows:?}")
}

/// The v58 nominal key's fingerprint: its `Display` (exact identity bytes,
/// hex-rendered) or the literal `none`, which no rendered key can spell.
fn origin_fp(origin: Option<&crate::ty::TypeOrigin>) -> String {
    origin.map_or_else(|| "none".to_string(), ToString::to_string)
}

/// The blob table as written, one `digest=<hex>:len=<n>:sha256=<hex>` entry
/// per row in stored order (the table's canonical order is the validator's
/// question; a diff renders what each side holds). The bytes enter through
/// their own SHA-256, so a row whose bytes changed under an unchanged
/// recorded digest still differs.
fn blobs_fp(m: &Module) -> String {
    // Compile-time coverage (roadmap WS4.13): every field is read.
    m.blobs
        .iter()
        .map(|crate::blob::Blob { digest, data }| {
            format!(
                "digest={digest}:len={}:sha256={}",
                data.len(),
                crate::blob::BlobDigest::of(data)
            )
        })
        .collect::<Vec<_>>()
        .join(";")
}

/// Declaration order and arena `ClosureTyId`s are cosmetic; capture-offset
/// order and duplicate rows are not. A vector (not a set) preserves descriptor
/// multiplicity, exactly as [`tuple_layouts_fp`] does.
///
/// The row is keyed by the closure type's STRUCTURAL spelling
/// ([`TypeFingerprint::closure_ref`]), never by its arena index: a producer
/// that renumbers its closure types has not changed a frame, and one that
/// renumbers AND swaps two rows HAS moved a frame from one closure type to
/// another — an index-keyed row would render the first as a change and the
/// second as none.
fn closure_layouts_fp(m: &Module) -> String {
    if let Err(error) = m.validate_closure_layouts() {
        return format!(
            "invalid {error:?}: {:?}; closure_types={:?}",
            m.closure_layouts, m.closure_types
        );
    }
    let mut rows: Vec<_> = m
        .closure_layouts
        .iter()
        .map(|layout| {
            // Compile-time coverage (roadmap WS4.13): every field is read.
            let crate::ClosureLayoutDescriptor {
                origin,
                closure,
                size,
                align,
                capture_offsets,
            } = layout;
            let nominal = origin
                .as_ref()
                .map(|origin| format!(" origin={origin}"))
                .unwrap_or_default();
            format!(
                "{} size={} align={} offsets={:?}{nominal}",
                TypeFingerprint::new(m).closure_ref(*closure),
                size,
                align,
                capture_offsets
            )
        })
        .collect();
    rows.sort();
    format!("{rows:?}")
}

/// Record a [`MetaChange`] for `field` iff the two rendered sides differ.
fn push_meta_if_changed(out: &mut Vec<MetaChange>, field: &str, before: String, after: String) {
    if before != after {
        out.push(MetaChange {
            field: field.to_string(),
            before,
            after,
        });
    }
}

/// Order-insensitive comparison of two name-keyed tables (globals by symbol,
/// spec modules by machine name). Each distinct name produces at most one
/// [`MetaChange`] whose field is `prefix + name`; an added or removed row
/// renders its absent side as `-`. A name that occurs more than once on one
/// side (ill-formed, but this API does not validate) fingerprints as the
/// sorted multiset of its rows, so a duplicate is neither hidden nor a panic.
fn diff_named_rows<'a>(
    out: &mut Vec<MetaChange>,
    prefix: &str,
    a: impl Iterator<Item = (&'a str, String)>,
    b: impl Iterator<Item = (&'a str, String)>,
) {
    fn collect<'a>(rows: impl Iterator<Item = (&'a str, String)>) -> HashMap<&'a str, Vec<String>> {
        let mut table: HashMap<&str, Vec<String>> = HashMap::new();
        for (name, fp) in rows {
            table.entry(name).or_default().push(fp);
        }
        for fps in table.values_mut() {
            fps.sort();
        }
        table
    }
    fn render(fps: Option<&Vec<String>>) -> String {
        match fps {
            None => "-".to_string(),
            Some(fps) if fps.len() == 1 => fps[0].clone(),
            Some(fps) => format!("duplicate x{} {fps:?}", fps.len()),
        }
    }
    let ta = collect(a);
    let tb = collect(b);
    let mut names: Vec<&str> = ta.keys().copied().collect();
    for k in tb.keys() {
        if !ta.contains_key(*k) {
            names.push(*k);
        }
    }
    names.sort();
    for name in names {
        push_meta_if_changed(
            out,
            &format!("{prefix}{name}"),
            render(ta.get(name)),
            render(tb.get(name)),
        );
    }
}

/// Rendered codegen license for a [`MetaChange`]; `-` is the pre-v41 "no
/// licensing claim" state, which a consumer PERMITS while it REFUSES
/// `ungated` — so the two must render differently.
///
/// A license's v61 [`crate::GateEvidence`] is rendered by what it MEANS, not
/// by its arena numbers, so the diff stays renumbering-insensitive: the cited
/// obligation by its claim key ([`fp_obligation_claim`], or `#<id>?` when the
/// module declares no such row), and the body digest by whether it still
/// names the body as it stands (`holds` / `stale` / `undigestable`). The raw
/// digest is deliberately not shown: it hashes the function's own id, so a
/// renumbered but otherwise identical module would report a change, while a
/// body rewritten under an unchanged license flips `holds` -> `stale`.
fn body_gate_fp(m: &Module, func: &Function) -> String {
    match &func.body_gate {
        None => "-".to_string(),
        Some(gate @ (crate::BodyGate::Ungated | crate::BodyGate::Gated { evidence: None, .. })) => {
            gate.to_string()
        }
        Some(crate::BodyGate::Gated {
            authority,
            evidence: Some(evidence),
        }) => {
            let mut cited = m
                .proof_obligations
                .iter()
                .filter(|o| o.id == evidence.obligation);
            let claim = match (cited.next(), cited.next()) {
                (Some(row), None) => fp_obligation_claim(m, row),
                _ => format!("#{}?", evidence.obligation.index()),
            };
            let body = match m.function_body_digest(func.id) {
                Ok(digest) if digest == evidence.body_digest => "holds",
                Ok(_) => "stale",
                Err(_) => "undigestable",
            };
            format!("gated {authority:?} evidence [{claim}] body={body}")
        }
    }
}

fn display_path_fp(p: Option<&str>) -> String {
    p.map_or_else(|| "-".to_string(), |p| format!("{p:?}"))
}

/// Every claim-style function attribute, positional parameter attributes
/// included. `naked` and `target_features` (v41) decide whether a consumer may
/// compile the body at all, so a change to them is never cosmetic.
fn func_attrs_fp(a: &crate::FuncAttrs) -> String {
    // Compile-time coverage (roadmap WS4.13): every field is read.
    let crate::FuncAttrs {
        readonly,
        readnone,
        inlinehint,
        cold,
        params,
        naked,
        target_features,
        ret,
    } = a;
    let mut s = format!(
        "readonly={} readnone={} inlinehint={} cold={} naked={} target_features={:?} ret={} \
         params=[",
        readonly,
        readnone,
        inlinehint,
        cold,
        naked,
        target_features,
        // v45: the return slot is an ABI pin like any parameter's.
        slot_attrs_fp(ret),
    );
    for (i, p) in params.iter().enumerate() {
        if i > 0 {
            s.push(',');
        }
        s.push_str(&slot_attrs_fp(p));
    }
    s.push(']');
    s
}

/// One slot's claim-style attributes, v45 ABI facts included: a changed
/// extension or pass mode changes the call's byte-level ABI, so it is never
/// cosmetic.
fn slot_attrs_fp(p: &crate::ParamAttrs) -> String {
    // Compile-time coverage (roadmap WS4.13): every field is read.
    let crate::ParamAttrs {
        dereferenceable,
        nonnull,
        align,
        noalias,
        readonly,
        byval,
        sret,
        ext,
        pass,
    } = p;
    let pass = match pass {
        None => "-".to_string(),
        Some(crate::PassMode::Cast { pieces }) => format!(
            "cast({})",
            pieces
                .iter()
                .map(ToString::to_string)
                .collect::<Vec<_>>()
                .join(",")
        ),
        Some(crate::PassMode::Indirect { on_stack }) => format!("indirect({on_stack})"),
        Some(mode) => mode.token().to_string(),
    };
    format!(
        "{{deref={} nonnull={} align={} noalias={} readonly={} byval={} sret={} ext={:?} \
         pass={pass}}}",
        dereferenceable.map_or_else(|| "-".to_string(), |d| d.to_string()),
        nonnull,
        align.map_or_else(|| "-".to_string(), |a| a.to_string()),
        noalias,
        readonly,
        byval,
        sret,
        ext,
    )
}

/// Every field of [`TargetInfo`]; `-` when the module is target-independent.
fn target_info_fp(t: Option<&crate::TargetInfo>) -> String {
    let Some(t) = t else {
        return "-".to_string();
    };
    // Compile-time coverage (roadmap WS4.13): every field is read.
    let crate::TargetInfo {
        triple,
        pointer_size,
        endianness,
        abi,
        struct_passing,
    } = t;
    format!(
        "triple={:?} pointer_size={} endianness={} abi={} struct_passing={:?}",
        triple,
        pointer_size,
        endianness,
        abi.as_deref()
            .map_or_else(|| "-".to_string(), |a| format!("{a:?}")),
        struct_passing,
    )
}

/// The dependency table as a sorted set of `(name, digest, producer, scheme)`
/// rows.
fn imports_fp(m: &Module) -> String {
    let mut rows: Vec<String> = m
        .imports
        .iter()
        .map(|imp| {
            // Compile-time coverage (roadmap WS4.13): every field is read.
            let crate::ModuleImport {
                name,
                digest,
                producer,
                scheme,
            } = imp;
            // The v44 scheme is spelled only when it is not the legacy V2,
            // so a table of V2 rows fingerprints exactly as before v44.
            let scheme = if scheme.is_v2() {
                String::new()
            } else {
                format!("{{{scheme}}}")
            };
            format!(
                "{name}@{digest}[{}]{scheme}",
                producer
                    .as_ref()
                    .map_or_else(|| "-".to_string(), ToString::to_string),
            )
        })
        .collect();
    rows.sort();
    format!("{rows:?}")
}

/// Every field of a [`Global`] other than its name (which keys the row). The
/// type is fingerprinted structurally so arena ids stay cosmetic; the
/// initializer is fingerprinted through [`fp_constant`], which resolves
/// `FnDef` / `Closure` / `SymbolAddr` references through the module.
fn global_fp(m: &Module, g: &crate::Global) -> String {
    // Compile-time coverage (roadmap WS4.13): every field is read.
    let crate::Global {
        name: _, // the row key (`global @<name>`)
        ty,
        mutable,
        initializer,
        linkage,
        tls,
        align,
        section,
        visibility,
        retained,
    } = g;
    format!(
        "ty={} mutable={} init={} linkage={} tls={} align={} section={} visibility={} retained={}",
        fp_ty(m, ty),
        mutable,
        initializer
            .as_ref()
            .map_or_else(|| "-".to_string(), |c| fp_constant(m, c)),
        linkage,
        tls.map_or_else(|| "-".to_string(), |t| t.to_string()),
        align.map_or_else(|| "-".to_string(), |a| a.to_string()),
        section
            .as_deref()
            .map_or_else(|| "-".to_string(), |s| format!("{s:?}")),
        visibility,
        retained,
    )
}

/// Every field of a [`SpecModule`](crate::spec::SpecModule) other than its
/// name (which keys the row): vars, actions, invariants, anchors, waivers,
/// proof bindings, origin, enforcement mode and the v46 temporal properties
/// (the v46 `SpecVar.sort` / `SpecInvariant.typed` / `ProofKind::CleanTheorem`
/// ride in the `Debug` of their carriers), all in declaration order
/// (within a machine, order is content — anchors and waivers are positional
/// evidence about a named action).
///
/// An anchor's `function` and `Function(..)` projection target are
/// [`FuncId`]s, so they are resolved to the function's link-time SYMBOL
/// through `m` — the key functions are matched by — rather than printed as a
/// raw arena index. A raw index would make `FuncId` renumbering a spurious
/// change AND, worse, hide a re-point: an anchor moved from `f` to `g` in a
/// build where `g` now holds `f`'s old index would fingerprint identically.
fn spec_module_fp(m: &Module, s: &crate::spec::SpecModule) -> String {
    // Compile-time coverage (roadmap WS4.13): every field is read.
    let crate::spec::SpecModule {
        name: _, // the row key (`spec_module <name>`)
        vars,
        actions,
        invariants,
        anchors,
        waivers,
        proofs,
        origin,
        enforcement,
        temporal,
    } = s;
    let anchors: Vec<String> = anchors
        .iter()
        .map(|a| {
            // Compile-time coverage (roadmap WS4.13): every field is read.
            let crate::spec::SpecAnchor {
                machine,
                action,
                rust_symbol,
                span,
                project,
                function,
                projection_target,
            } = a;
            let target = match *projection_target {
                None => "-".to_string(),
                Some(crate::spec::SpecProjectionTarget::Function(id)) => {
                    format!("function({})", spec_func_ref(m, id))
                }
                Some(t) => t.tag().to_string(),
            };
            format!(
                "{{machine={:?} action={:?} rust_symbol={:?} span={:?} project={:?} function={} projection_target={}}}",
                machine,
                action,
                rust_symbol,
                span,
                project,
                function.map_or_else(|| "-".to_string(), |id| spec_func_ref(m, id)),
                target,
            )
        })
        .collect();
    format!(
        "enforcement={:?} origin={} vars={:?} actions={:?} invariants={:?} anchors=[{}] waivers={:?} proofs={:?} temporal={:?}",
        enforcement,
        origin.label(),
        vars,
        actions,
        invariants,
        anchors.join(","),
        waivers,
        proofs,
        temporal,
    )
}

/// A module-local `FuncId` (a spec anchor's, an obligation site's, an
/// `InheritedFromCallee` callee's), resolved to `@<symbol>`; a dangling id
/// keeps its raw index under a distinct spelling (never a panic, never a match
/// for a real function).
fn spec_func_ref(m: &Module, id: FuncId) -> String {
    function_by_id(m, id).map_or_else(
        || format!("#dangling {}", id.index()),
        |f| format!("@{}", f.name),
    )
}

// -----------------------------------------------------------------------------
// Function-level diff
// -----------------------------------------------------------------------------

fn diff_function(
    ma: &Module,
    mb: &Module,
    fa: &Function,
    fb: &Function,
    opts: DiffOptions,
) -> Vec<BlockChange> {
    let walk_a = walk_blocks(fa);
    let walk_b = walk_blocks(fb);

    // Build a_order[block_id] = visit_index and the ValueId renumber map.
    // The value map assigns each ValueId defined in the function (both
    // block params and instruction results) a canonical index based on
    // DFS walk order.
    let va_map = build_value_map(fa, &walk_a);
    let vb_map = build_value_map(fb, &walk_b);

    // Precompute canonical block numbers for successor remapping.
    let ba_map: HashMap<BlockId, u32> = walk_a
        .iter()
        .enumerate()
        .map(|(i, &bid)| (bid, i as u32))
        .collect();
    let bb_map: HashMap<BlockId, u32> = walk_b
        .iter()
        .enumerate()
        .map(|(i, &bid)| (bid, i as u32))
        .collect();

    let mut changes = Vec::new();
    let n = walk_a.len().max(walk_b.len());
    for i in 0..n {
        match (walk_a.get(i), walk_b.get(i)) {
            (Some(&ba), Some(&bb)) => {
                let blk_a = fa.blocks.iter().find(|b| b.id == ba).expect("walk id");
                let blk_b = fb.blocks.iter().find(|b| b.id == bb).expect("walk id");
                // Compile-time coverage (roadmap WS4.13).
                let Block {
                    id: _,     // renumbering: blocks are matched by DFS visit order
                    params: _, // compared below (count + types)
                    body: _,   // `diff_block_body`
                } = blk_a;

                // Compare block parameter types (number + fingerprint).
                if blk_a.params.len() != blk_b.params.len() {
                    changes.push(BlockChange::StructureDiffers {
                        visit: i,
                        detail: format!(
                            "block param count: {} vs {}",
                            blk_a.params.len(),
                            blk_b.params.len()
                        ),
                    });
                    continue;
                }
                let mut param_mismatch = None;
                for (pi, ((_, ta), (_, tb))) in
                    blk_a.params.iter().zip(blk_b.params.iter()).enumerate()
                {
                    if fp_ty(ma, ta) != fp_ty(mb, tb) {
                        param_mismatch = Some(format!(
                            "block param {} type: {} vs {}",
                            pi,
                            render_ty(ma, ta),
                            render_ty(mb, tb)
                        ));
                        break;
                    }
                }
                if let Some(detail) = param_mismatch {
                    changes.push(BlockChange::StructureDiffers { visit: i, detail });
                    continue;
                }

                let instr_changes = diff_block_body(
                    ma, mb, blk_a, blk_b, &va_map, &vb_map, &ba_map, &bb_map, opts,
                );
                if !instr_changes.is_empty() {
                    changes.push(BlockChange::InstrDiff {
                        visit: i,
                        instr_changes,
                    });
                }
            }
            (Some(_), None) => changes.push(BlockChange::Removed { visit: i }),
            (None, Some(_)) => changes.push(BlockChange::Added { visit: i }),
            (None, None) => unreachable!(),
        }
    }
    changes
}

/// DFS preorder walk of reachable blocks from entry, with unreachable
/// blocks appended in block-id order.
fn walk_blocks(f: &Function) -> Vec<BlockId> {
    let by_id: HashMap<BlockId, &Block> = f.blocks.iter().map(|b| (b.id, b)).collect();
    let mut visited: std::collections::HashSet<BlockId> = std::collections::HashSet::new();
    let mut order: Vec<BlockId> = Vec::new();
    let mut stack: Vec<BlockId> = Vec::new();
    if by_id.contains_key(&f.entry) {
        stack.push(f.entry);
    }
    while let Some(bid) = stack.pop() {
        if !visited.insert(bid) {
            continue;
        }
        order.push(bid);
        let blk = match by_id.get(&bid) {
            Some(b) => b,
            None => continue,
        };
        let succs = block_successors(blk);
        // Push in reverse so first successor is visited first on pop.
        for s in succs.iter().rev() {
            if !visited.contains(s) && by_id.contains_key(s) {
                stack.push(*s);
            }
        }
    }
    // Append any unreachable blocks in id order for deterministic output.
    let mut leftover: Vec<BlockId> = f
        .blocks
        .iter()
        .map(|b| b.id)
        .filter(|bid| !visited.contains(bid))
        .collect();
    leftover.sort();
    order.extend(leftover);
    order
}

fn block_successors(blk: &Block) -> Vec<BlockId> {
    let Some(term) = blk.body.last() else {
        return Vec::new();
    };
    // The exhaustive accessor (amendment D §1.3): an invoke-family
    // terminator branches to its normal continuation or its landing pad.
    term.inst
        .successor_edges()
        .into_iter()
        .map(|edge| edge.target)
        .collect()
}

/// Build a canonical mapping from ValueId to a u32 index.
///
/// The index is the order in which the value is encountered during the
/// DFS walk. Block params come first in each block (in declared order),
/// then instruction results in order. The same walk is used on both
/// sides so that operand references, which are compared via this map,
/// line up across modules after SSA renumbering.
fn build_value_map(f: &Function, walk: &[BlockId]) -> HashMap<ValueId, u32> {
    let mut m = HashMap::new();
    let mut next: u32 = 0;
    let by_id: HashMap<BlockId, &Block> = f.blocks.iter().map(|b| (b.id, b)).collect();
    for bid in walk {
        let Some(blk) = by_id.get(bid) else { continue };
        for (v, _) in &blk.params {
            m.entry(*v).or_insert_with(|| {
                let i = next;
                next += 1;
                i
            });
        }
        for node in &blk.body {
            for r in &node.results {
                m.entry(*r).or_insert_with(|| {
                    let i = next;
                    next += 1;
                    i
                });
            }
        }
    }
    m
}

// -----------------------------------------------------------------------------
// Block-body diff
// -----------------------------------------------------------------------------

#[allow(clippy::too_many_arguments)]
fn diff_block_body(
    ma: &Module,
    mb: &Module,
    ba: &Block,
    bb: &Block,
    va: &HashMap<ValueId, u32>,
    vb: &HashMap<ValueId, u32>,
    ba_map: &HashMap<BlockId, u32>,
    bb_map: &HashMap<BlockId, u32>,
    opts: DiffOptions,
) -> Vec<InstrChange> {
    let mut changes = Vec::new();
    let n = ba.body.len().max(bb.body.len());
    for i in 0..n {
        match (ba.body.get(i), bb.body.get(i)) {
            (Some(na), Some(nb)) => {
                // Compile-time coverage (roadmap WS4.13).
                let InstrNode {
                    inst: _,          // `fp_inst`
                    results: _,       // ids: renumbering; the ARITY is compared below
                    proofs: _,        // proof channel
                    span: _,          // IGNORED: debug span
                    proof_context: _, // proof channel
                    scope: _,         // IGNORED: debug scope index
                } = na;
                let fa_key = fp_inst(ma, &na.inst, va, ba_map);
                let fb_key = fp_inst(mb, &nb.inst, vb, bb_map);
                // A node's result ids are renumbering, their COUNT is not: a
                // call node that stops binding its callee's return value moves
                // `Module::stable_digest` and must not diff empty.
                let arity_eq = na.results.len() == nb.results.len();
                let inst_eq = fa_key == fb_key && arity_eq;

                let proofs_eq = if opts.ignore_proofs {
                    true
                } else {
                    fp_proofs(ma, &na.proofs) == fp_proofs(mb, &nb.proofs)
                        && fp_proof_context(ma, na.proof_context.as_ref())
                            == fp_proof_context(mb, nb.proof_context.as_ref())
                };

                if !inst_eq || !proofs_eq {
                    let mut before = render_inst(ma, na, opts);
                    let mut after = render_inst(mb, nb, opts);
                    // Spell the arity only when it is what differs, so every
                    // other rendering keeps its earlier text.
                    if !arity_eq {
                        let _ = write!(before, " [results={}]", na.results.len());
                        let _ = write!(after, " [results={}]", nb.results.len());
                    }
                    changes.push(InstrChange::Replaced {
                        index: i,
                        before,
                        after,
                    });
                }
            }
            (Some(na), None) => changes.push(InstrChange::Removed {
                index: i,
                summary: render_inst(ma, na, opts),
            }),
            (None, Some(nb)) => changes.push(InstrChange::Added {
                index: i,
                summary: render_inst(mb, nb, opts),
            }),
            (None, None) => unreachable!(),
        }
    }
    changes
}

// -----------------------------------------------------------------------------
// Proof diff
// -----------------------------------------------------------------------------

/// The function-level annotation sets, each fingerprinted in its OWN module
/// (a `ProofRef` resolves through that module's obligation table).
fn proof_diff(
    ma: &Module,
    a: &[ProofAnnotation],
    mb: &Module,
    b: &[ProofAnnotation],
) -> Vec<ProofChange> {
    let a_keys: Vec<String> = a.iter().map(|p| fp_proof(ma, p)).collect();
    let b_keys: Vec<String> = b.iter().map(|p| fp_proof(mb, p)).collect();
    let a_set: std::collections::HashSet<&str> = a_keys.iter().map(String::as_str).collect();
    let b_set: std::collections::HashSet<&str> = b_keys.iter().map(String::as_str).collect();

    let mut out = Vec::new();
    let mut removed: Vec<&str> = a_keys
        .iter()
        .map(String::as_str)
        .filter(|k| !b_set.contains(k))
        .collect();
    removed.sort();
    removed.dedup();
    for r in removed {
        out.push(ProofChange::Removed {
            name: r.to_string(),
        });
    }
    let mut added: Vec<&str> = b_keys
        .iter()
        .map(String::as_str)
        .filter(|k| !a_set.contains(k))
        .collect();
    added.sort();
    added.dedup();
    for a in added {
        out.push(ProofChange::Added {
            name: a.to_string(),
        });
    }
    out
}

fn fp_proofs(m: &Module, ps: &[ProofAnnotation]) -> String {
    let mut keys: Vec<String> = ps.iter().map(|p| fp_proof(m, p)).collect();
    keys.sort();
    keys.join(",")
}

// -----------------------------------------------------------------------------
// Module-level proof-state diff (obligations + certificates)
// -----------------------------------------------------------------------------

/// Diff the module-level proof state: `proof_obligations` and
/// `proof_certificates`.
///
/// Like the rest of this module, the comparison is insensitive to arena id
/// renumbering and declaration order. Obligations are matched across modules
/// by their *claim* — kind, scope (function name, not `FuncId`), description,
/// formula, and embedded source identity — so that the same obligation renumbered in B's proof table
/// still lines up with A's. The `status` field is the mutable label that, when
/// it differs for a matched claim, is reported as a status change. Certificates
/// are matched by their claim's obligation key plus prover and evidence.
fn proof_state_diff(a: &Module, b: &Module) -> Vec<ProofStateChange> {
    let mut out = Vec::new();

    // --- Obligations: match by claim key, compare status -----------------
    // Map claim -> status for each side. Duplicates keep the first occurrence
    // (a module should not carry two obligations with an identical claim, but
    // if it does the match is still deterministic by declaration order).
    let mut a_obl: HashMap<String, &ProofObligation> = HashMap::new();
    for o in &a.proof_obligations {
        a_obl.entry(fp_obligation_claim(a, o)).or_insert(o);
    }
    let mut b_obl: HashMap<String, &ProofObligation> = HashMap::new();
    for o in &b.proof_obligations {
        b_obl.entry(fp_obligation_claim(b, o)).or_insert(o);
    }

    let mut obl_keys: Vec<&str> = a_obl.keys().map(String::as_str).collect();
    for k in b_obl.keys() {
        if !a_obl.contains_key(k) {
            obl_keys.push(k);
        }
    }
    obl_keys.sort();
    for k in obl_keys {
        match (a_obl.get(k), b_obl.get(k)) {
            (Some(oa), None) => out.push(ProofStateChange::ObligationRemoved {
                obligation: k.to_string(),
                status: oa.status.to_string(),
            }),
            (None, Some(ob)) => out.push(ProofStateChange::ObligationAdded {
                obligation: k.to_string(),
                status: ob.status.to_string(),
            }),
            (Some(oa), Some(ob)) => {
                if oa.status != ob.status {
                    out.push(ProofStateChange::ObligationStatusChanged {
                        obligation: k.to_string(),
                        before: oa.status.to_string(),
                        after: ob.status.to_string(),
                    });
                }
            }
            (None, None) => unreachable!(),
        }
    }

    // --- Certificates: match by full structural fingerprint --------------
    let a_certs: Vec<String> = a
        .proof_certificates
        .iter()
        .map(|c| fp_certificate(a, c))
        .collect();
    let b_certs: Vec<String> = b
        .proof_certificates
        .iter()
        .map(|c| fp_certificate(b, c))
        .collect();
    let a_cert_set: std::collections::HashSet<&str> = a_certs.iter().map(String::as_str).collect();
    let b_cert_set: std::collections::HashSet<&str> = b_certs.iter().map(String::as_str).collect();

    let mut removed: Vec<&str> = a_certs
        .iter()
        .map(String::as_str)
        .filter(|k| !b_cert_set.contains(k))
        .collect();
    removed.sort();
    removed.dedup();
    for r in removed {
        out.push(ProofStateChange::CertificateRemoved {
            certificate: r.to_string(),
        });
    }
    let mut added: Vec<&str> = b_certs
        .iter()
        .map(String::as_str)
        .filter(|k| !a_cert_set.contains(k))
        .collect();
    added.sort();
    added.dedup();
    for a in added {
        out.push(ProofStateChange::CertificateAdded {
            certificate: a.to_string(),
        });
    }

    out
}

/// Stable, id-renumbering-insensitive key for the *claim* an obligation makes:
/// its kind, scope (resolved to the function name), description, formula (all
/// five fields, the v41 clause `bindings` included), embedded source/public
/// identity, the IR `site` it states a check about (v34), and the temporal
/// `spec` property it discharges (v46).
/// Deliberately excludes `id` (arena index) and `status` (the mutable label
/// whose changes `proof_state_diff` reports separately).
fn fp_obligation_claim(m: &Module, o: &ProofObligation) -> String {
    // Compile-time coverage (roadmap WS4.13): every field is read or named.
    let ProofObligation {
        id: _,     // arena index: renumbering
        kind,      // claim
        status: _, // reported as `ObligationStatusChanged`, never part of the key
        description,
        formula,
        function,
        source,
        site,
        spec,
    } = o;
    let mut s = String::new();
    let _ = write!(s, "kind={kind}");
    let func = function.and_then(|fid| function_by_id(m, fid));
    match (function, func) {
        (_, Some(f)) => {
            let _ = write!(s, ";fn={}", f.name);
        }
        (None, None) => s.push_str(";fn=_"),
        // A scope naming no function keeps its raw index under a distinct
        // spelling: it must never collapse onto the unscoped `_` (a scope
        // gained or dropped moves `Module::stable_digest`, so the claim key
        // must move too — this API does not validate its inputs).
        (Some(fid), None) => {
            let _ = write!(s, ";fn=#dangling {}", fid.index());
        }
    }
    let _ = write!(s, ";desc={description}");
    match formula {
        Some(f) => {
            let crate::ProofFormula {
                schema,
                payload,
                smtlib,
                sort,
                bindings,
            } = f;
            let _ = write!(s, ";formula[{schema}]={payload}");
            if let Some(smt) = smtlib {
                let _ = write!(s, ";smt={smt}");
            }
            if let Some(sort) = sort {
                let _ = write!(s, ";sort={sort}");
            }
            // A `Value` place names an SSA value of the obligation's own
            // function (its `site` function when it names no scope).
            let owner = func.or_else(|| site.and_then(|site| function_by_id(m, site.function)));
            s.push_str(&fp_formula_bindings(bindings, owner, ";"));
        }
        None => s.push_str(";formula=_"),
    }
    let mut source_bytes = Vec::new();
    write_proof_obligation_source_identity_stable(&mut source_bytes, source.as_ref());
    s.push_str(";source=");
    for byte in source_bytes {
        let _ = write!(s, "{byte:02x}");
    }
    // v34: WHICH instruction a per-check obligation is about. Twelve bounds
    // checks in one function differ ONLY here, so a site moved from one check
    // to another is a different claim. Rendered like the body: the function by
    // symbol, the block by DFS visit index, the instruction by position; a
    // `None` site renders as nothing, so an unsited obligation keeps the key it
    // had before sites were compared.
    if let Some(site) = site {
        let crate::proof::ObligationSite {
            function,
            block,
            inst_index,
        } = *site;
        // Only the block walk is needed here, not the value numbering.
        let block = function_by_id(m, function)
            .and_then(|f| walk_blocks(f).iter().position(|&b| b == block))
            .map_or_else(|| format!("bb?{}", block.index()), |i| format!("bb{i}"));
        let _ = write!(
            s,
            ";site={}/{block}#{inst_index}",
            spec_func_ref(m, function)
        );
    }
    // v46: WHICH temporal property the obligation discharges is part of its
    // claim — two liveness rows that differ only here are different claims.
    match spec {
        Some(spec) => {
            // Compile-time coverage (roadmap WS4.13): every field is read.
            let crate::proof::SpecObligationRef { machine, temporal } = spec;
            let _ = write!(s, ";spec={machine:?}/{temporal:?}");
        }
        None => s.push_str(";spec=_"),
    }
    s
}

/// Resolve a `ProofId` to the claim key of the obligation it names within `m`,
/// or a renumber-stable placeholder when the id has no matching obligation.
fn obligation_claim_by_id(m: &Module, id: ProofId) -> String {
    match m.proof_obligations.iter().find(|o| o.id == id) {
        Some(o) => fp_obligation_claim(m, o),
        // Dangling reference: fall back to the raw index so a difference still
        // surfaces, but keep it visibly distinct from a resolved claim.
        None => format!("obl#{}", id.index()),
    }
}

/// Structural fingerprint of a certificate. The obligation is referenced by
/// its claim key (so renumbering the proof table does not surface here), and
/// the prover and evidence are compared structurally.
fn fp_certificate(m: &Module, c: &ProofCertificate) -> String {
    // Compile-time coverage (roadmap WS4.13): every field is read.
    let ProofCertificate {
        obligation,
        prover,
        evidence,
        assurance,
    } = c;
    let mut s = format!(
        "obl={};prover={};ev={}",
        obligation_claim_by_id(m, *obligation),
        prover,
        fp_evidence(m, evidence)
    );
    // v41 coverage projection. NON-AUTHORITATIVE for a consumer (it derives
    // coverage from evidence it re-checks), but it is carried content: a row
    // claiming `Unbounded` where it said `UnwindBounded { depth: 1 }`, or citing
    // another bundle, moves `Module::stable_digest` and a reviewer must see it.
    // Absent renders as nothing, so every certificate without one keeps its
    // pre-WS4.13 fingerprint.
    if let Some(crate::proof::CoverageAssurance {
        bound,
        request_digest,
    }) = assurance
    {
        let _ = write!(s, ";assurance={bound:?}@{request_digest}");
    }
    s
}

/// Resolve an [`crate::ImportId`] to its CONTENT for fingerprinting.
///
/// A raw index would make two modules whose import tables differ compare equal
/// wherever the index happened to line up — the diff's whole job is to be blind
/// to renumbering and sensitive to meaning, and an import's meaning is the
/// artifact it pins. Falls back to `import#N` for a dangling id so the
/// fingerprint stays total.
fn fp_import_ref(m: &Module, id: crate::ImportId) -> String {
    match m.import(id) {
        Some(imp) => format!(
            "{}@{}[{}]",
            imp.name,
            imp.digest,
            match &imp.producer {
                None => "-".to_string(),
                Some(producer) => producer.to_string(),
            }
        ),
        None => format!("import#{}", id.index()),
    }
}

fn fp_extern_ref(m: &Module, reference: &crate::ExternRef) -> String {
    // Compile-time coverage (roadmap WS4.13): every field is read. The
    // obligation id indexes the IMPORTED module's arena, whose identity the
    // import's digest pins, so its raw index IS its identity here.
    let crate::ExternRef {
        module,
        symbol,
        obligation,
    } = reference;
    format!(
        "{}::{}::{}",
        fp_import_ref(m, *module),
        symbol,
        match obligation {
            None => "-".to_string(),
            Some(obligation) => obligation.index().to_string(),
        }
    )
}

fn fp_evidence(m: &Module, e: &ProofEvidence) -> String {
    match e {
        ProofEvidence::SmtProof(bytes) => {
            let mut s = String::from("smt:");
            for byte in bytes {
                let _ = write!(s, "{byte:02x}");
            }
            s
        }
        ProofEvidence::LeanProof(term) => format!("lean:{term}"),
        ProofEvidence::KaniHarness(h) => format!("kani:{h}"),
        ProofEvidence::GammaCrownBound {
            epsilon,
            verified_layers,
        } => format!("gcrown:{}:{verified_layers}", epsilon.to_bits()),
        ProofEvidence::TranslationValidation {
            rule_name,
            smt_hash,
        } => {
            let mut s = format!("tv:{rule_name}:");
            for byte in smt_hash {
                let _ = write!(s, "{byte:02x}");
            }
            s
        }
        ProofEvidence::Trusted(reason) => format!("trusted:{reason}"),
        ProofEvidence::InheritedFromCallee {
            callee,
            obligation,
            external,
        } => {
            // Both references are LOCAL arena ids, resolved through `m` the way
            // the rest of the diff resolves them: the callee by its link-time
            // SYMBOL, the relied-upon obligation by its CLAIM key. A raw index
            // made FuncId / ProofId renumbering a spurious change and — worse —
            // hid a retarget onto whatever function or obligation came to
            // occupy the old index (roadmap WS4.13).
            let mut s = format!(
                "inherited:{}:{}",
                spec_func_ref(m, *callee),
                obligation_claim_by_id(m, *obligation)
            );
            // v41. MUST be fingerprinted: "discharged in this module" and
            // "discharged in crate X" are different claims, and a diff that
            // compared them equal would report no change when a producer
            // retargeted an inheritance across a crate boundary.
            if let Some(reference) = external {
                let _ = write!(s, ":extern:{}", fp_extern_ref(m, reference));
            }
            s
        }
        ProofEvidence::CleanCic {
            term,
            context,
            lineage,
            kernel_recheck,
        } => {
            let mut s = String::from("cleancic:");
            for byte in term {
                let _ = write!(s, "{byte:02x}");
            }
            s.push(':');
            for byte in context {
                let _ = write!(s, "{byte:02x}");
            }
            let _ = write!(s, ":{lineage}");
            // The kernel re-check directive is what makes the certificate
            // RE-CHECKABLE at all (without it a re-checking validator refuses
            // the row), and its binding is what the statement is bound to. It
            // used to be skipped here, so dropping it, re-anchoring it or
            // re-binding it diffed as no change (roadmap WS4.13). Absent
            // renders as nothing, keeping every directive-free certificate's
            // earlier fingerprint.
            if let Some(recheck) = kernel_recheck {
                let _ = write!(s, ":recheck{{{}}}", fp_kernel_recheck(recheck));
            }
            s
        }
    }
}

/// Every field of a `CleanCic` kernel re-check directive and of its
/// [`CertificateBinding`](crate::proof::CertificateBinding). An island's
/// declaration bytes are fingerprinted by their RECOMPUTED digest beside the
/// stored one — the `source_provenance` rule: a carrier whose stored digest
/// went stale must still be visible.
fn fp_kernel_recheck(r: &crate::proof::CleanCicKernelRecheck) -> String {
    let crate::proof::CleanCicKernelRecheck {
        module,
        theorems,
        anchor,
        allowed_axioms,
        binding,
    } = r;
    let mut s = format!(
        "module={module:?};anchor={anchor:?};theorems={theorems:?};axioms={allowed_axioms:?}"
    );
    if let Some(binding) = binding {
        let crate::proof::CertificateBinding {
            environment_digest,
            statement_digest,
            origin_module,
            source,
            callees,
            environment,
        } = &**binding;
        let _ = write!(
            s,
            ";binding{{environment={environment_digest};statement={statement_digest};origin={}",
            origin_module.map_or_else(|| "-".to_string(), |d| d.to_string())
        );
        match source {
            None => s.push_str(";source=-"),
            Some(crate::proof::SourceDefinitionRef {
                decl,
                closure_digest,
            }) => {
                let _ = write!(s, ";source={decl:?}@{closure_digest}");
            }
        }
        let _ = write!(s, ";callees={callees:?}");
        if let Some(crate::proof::IslandEnvironment {
            declarations,
            digest,
        }) = environment
        {
            let _ = write!(
                s,
                ";island{{stored={digest};content={};bytes={}}}",
                crate::proof::island_declarations_digest(declarations),
                declarations.len()
            );
        }
        s.push('}');
    }
    s
}

/// Stable fingerprint of a node's per-call `ProofContext`. Both `assumes` and
/// `establishes` reference module obligation ids; each is resolved to the
/// obligation's claim key within the node's own module so the comparison is
/// insensitive to proof-table renumbering. The two id lists are sorted so that
/// reordering the references alone does not register as a difference.
fn fp_proof_context(m: &Module, ctx: Option<&ProofContext>) -> String {
    let Some(ctx) = ctx else {
        return String::new();
    };
    // Compile-time coverage (roadmap WS4.13): every field is read.
    let ProofContext {
        assumes,
        establishes,
    } = ctx;
    let mut assumes: Vec<String> = assumes
        .iter()
        .map(|id| obligation_claim_by_id(m, *id))
        .collect();
    assumes.sort();
    let mut establishes: Vec<String> = establishes
        .iter()
        .map(|id| obligation_claim_by_id(m, *id))
        .collect();
    establishes.sort();
    format!(
        "assumes=[{}];establishes=[{}]",
        assumes.join("|"),
        establishes.join("|")
    )
}

/// Rendered producer-provenance value (v23) for a [`MetaChange`]; `-` marks an
/// absent tag so `None -> Some(...)` transitions render as `- -> trust`.
fn producer_fp(p: Option<&crate::Producer>) -> String {
    p.map_or_else(|| "-".to_string(), ToString::to_string)
}

/// Render a lexical scope tree for the opt-in `"scopes"` debug meta row:
/// one `#i parent=<p|root> at <f> <l> <c> inlined-at <f> <l> <c> callee <path>`
/// entry per scope. Scope indices are function-local and positional, so the
/// table is compared in order (a reorder IS a change to the tree).
fn scopes_fp(scopes: Option<&[crate::ScopeData]>) -> String {
    let Some(scopes) = scopes else {
        return "-".to_string();
    };
    let mut out = String::new();
    for (i, sc) in scopes.iter().enumerate() {
        if i > 0 {
            out.push_str("; ");
        }
        out.push_str(&format!("#{i} "));
        match sc.parent {
            None => out.push_str("root"),
            Some(p) => out.push_str(&format!("parent={p}")),
        }
        if let Some(span) = &sc.span {
            out.push_str(&format!(" at {} {} {}", span.file, span.line, span.col));
        }
        if let Some(link) = &sc.inlined_at {
            out.push_str(&format!(
                " inlined-at {} {} {} callee {:?}",
                link.span.file, link.span.line, link.span.col, link.callee
            ));
        }
    }
    out
}

/// Render the complete proof-relevant source carrier in deterministic order.
/// Do not fingerprint only its stored binding digest: a forged carrier that
/// leaves that digest stale must still be visible in an audit diff.
fn source_provenance_fp(p: Option<&crate::SourceProvenance>) -> String {
    let Some(p) = p else {
        return "-".to_string();
    };
    let mut out = format!(
        "schema={};compiler={};semantic={};binding={};loops=[",
        p.schema, p.compiler_source_digest, p.semantic_body_digest, p.binding_digest,
    );
    for (loop_index, source_loop) in p.loops.iter().enumerate() {
        if loop_index != 0 {
            out.push('|');
        }
        let _ = write!(
            out,
            "{}:{}:bb{}:(",
            source_loop.source_loop_id,
            source_loop.hir_local_id,
            source_loop.header.index(),
        );
        for (binding_index, binding) in source_loop.bindings.iter().enumerate() {
            if binding_index != 0 {
                out.push(',');
            }
            let (place, index) = match binding.place {
                crate::SourcePlace::FunctionParameter { index } => ("fn", index),
                crate::SourcePlace::LoopParameter { index } => ("loop", index),
            };
            let _ = write!(
                out,
                "{:?}:{}:{place}{index}",
                binding.name, binding.hir_local_id,
            );
        }
        out.push(')');
    }
    out.push(']');
    out
}

/// Order-stable structural fingerprint of a function's separate-compilation
/// contract. `None` and an empty summary both fingerprint to the empty marker so
/// only a real contract change is reported. `owner` is the function the
/// summary belongs to: a clause binding's `Value` place is resolved through
/// its body ([`fp_formula_bindings`]).
fn summary_fp(m: &Module, owner: Option<&Function>, s: Option<&crate::FunctionSummary>) -> String {
    // R3 #8: `proved` is part of the contract — fold it into the triviality test, so
    // a `None -> Some(proved, empty)` or `proved=false -> true` transition on an
    // otherwise-empty summary is still fingerprinted (was collapsing to the same `∅`
    // marker as `None`). Only a genuinely empty, param-less, UNPROVED summary is ≡ None.
    // v41: `decreases` and `backed_by` are contract content too. A summary
    // carrying only a termination measure, or only the cross-crate reference
    // that authenticates `proved`, is NOT equivalent to no summary at all — so
    // both join the triviality test rather than collapsing to the `∅` marker.
    let Some(s) = s.filter(|s| {
        !(s.is_empty()
            && s.params.is_empty()
            && !s.proved
            && s.decreases.is_empty()
            && s.backed_by.is_none()
            && s.effects.is_none())
    }) else {
        return "∅".to_string();
    };
    // Compile-time coverage (roadmap WS4.13): every contract field is read.
    let crate::FunctionSummary {
        requires,
        ensures,
        params,
        proved,
        decreases,
        backed_by,
        effects,
    } = s;
    // Fingerprint ALL five ProofFormula fields: smtlib/sort are what the verifier
    // dispatches/solves on (independent of the opaque payload), so a changed SMT
    // rendering of a published contract must be reported (audit 2026-06-25 F3);
    // the v41 `bindings` say what each free name DENOTES (its sort and IR
    // place), so re-binding `x` from parameter 0 to parameter 1, or widening
    // its sort, changes the contract even when its text is untouched (roadmap
    // WS4.13).
    let clause = |c: &crate::ProofFormula| {
        let crate::ProofFormula {
            schema,
            payload,
            smtlib,
            sort,
            bindings,
        } = c;
        format!(
            "{}|{}|{}|{}{}",
            schema,
            payload,
            smtlib.as_deref().unwrap_or(""),
            sort.as_deref().unwrap_or(""),
            fp_formula_bindings(bindings, owner, "|"),
        )
    };
    let req: Vec<String> = requires.iter().map(clause).collect();
    let ens: Vec<String> = ensures.iter().map(clause).collect();
    // v41. `decreases` was landed with no fingerprint at all, so changing a
    // function's termination measure diffed as no change; `backed_by` is what
    // authenticates `proved`, and retargeting it at a different crate is
    // exactly the kind of change a reviewer must see.
    let dec: Vec<String> = decreases.iter().map(clause).collect();
    format!(
        "proved={};params=[{}];requires=[{}];ensures=[{}];decreases=[{}];backed_by={};effects={}",
        proved,
        params.join(","),
        req.join(";"),
        ens.join(";"),
        dec.join(";"),
        match backed_by {
            None => "-".to_string(),
            Some(reference) => fp_extern_ref(m, reference),
        },
        // v59: the effect frame is contract content — widening a callee's
        // `writes` is exactly the change a reviewer of a published contract
        // must see. `None` (UNRECORDED) keeps its own spelling.
        match effects {
            None => "-".to_string(),
            Some(effects) => fp_effect_summary(m, effects),
        },
    )
}

/// v59: order-stable fingerprint of an [`crate::EffectSummary`]. A `Global`
/// place is fingerprinted by its link-time SYMBOL, like `GlobalAddr`, so
/// reordering `Module.globals` stays cosmetic.
fn fp_effect_summary(m: &Module, effects: &crate::EffectSummary) -> String {
    let set = |set: &crate::EffectSet| match set {
        crate::EffectSet::Nothing => "nothing".to_string(),
        crate::EffectSet::Everything => "everything".to_string(),
        crate::EffectSet::Places(places) => {
            let mut rendered: Vec<String> = places
                .iter()
                .map(|place| match place {
                    crate::EffectPlace::ParamPointee { index } => format!("*param{index}"),
                    crate::EffectPlace::Global(global) => match m.globals.get(global.as_usize()) {
                        Some(g) => format!("@{}", g.name),
                        None => format!("#dangling {}", global.index()),
                    },
                })
                .collect();
            rendered.sort();
            format!("[{}]", rendered.join(","))
        }
    };
    format!(
        "reads={};writes={};allocates={};frees={};may_unwind={};io={}",
        set(&effects.reads),
        set(&effects.writes),
        effects.allocates,
        effects.frees,
        effects.may_unwind,
        effects.io,
    )
}

/// An SSA value numbering resolved to the canonical walk indices the body
/// comparison uses ([`walk_blocks`], [`build_value_map`]), so a proof-channel
/// row that names an SSA value is exactly as blind to renumbering as the body
/// it points into. (A block reference resolves to its DFS visit index, the
/// position in [`walk_blocks`].)
struct LocalIds {
    values: HashMap<ValueId, u32>,
}

impl LocalIds {
    fn of(f: &Function) -> Self {
        let walk = walk_blocks(f);
        LocalIds {
            values: build_value_map(f, &walk),
        }
    }
}

/// The function `id` names in `m`, if exactly the arena row with that id.
fn function_by_id(m: &Module, id: FuncId) -> Option<&Function> {
    m.functions.iter().find(|f| f.id == id)
}

/// A clause's v41 typed bindings (`name:sort@place`, in declaration order —
/// the order is the producer's and is part of the carried value). Empty
/// bindings render as NOTHING, so every formula that carries none keeps the
/// exact fingerprint it had before bindings were compared; a non-empty list is
/// appended after `sep`. A `Value` place is resolved through `owner`'s body
/// ([`LocalIds`]); without an owner, or for an id the body does not define, it
/// keeps its raw index under a distinct `%?` spelling.
fn fp_formula_bindings(
    bindings: &[(String, crate::proof::ClauseBinding)],
    owner: Option<&Function>,
    sep: &str,
) -> String {
    if bindings.is_empty() {
        return String::new();
    }
    let needs_body = bindings
        .iter()
        .any(|(_, b)| matches!(b.place, crate::proof::ClausePlace::Value(_)));
    let ids = if needs_body {
        owner.map(LocalIds::of)
    } else {
        None
    };
    let rows: Vec<String> = bindings
        .iter()
        .map(|(name, binding)| {
            let crate::proof::ClauseBinding { sort, place } = binding;
            use crate::proof::ClausePlace;
            let place = match *place {
                ClausePlace::Param { index } => format!("param{index}"),
                ClausePlace::ResultSlot { index } => format!("result{index}"),
                ClausePlace::MutParamExit { index } => format!("exit{index}"),
                ClausePlace::World => "world".to_string(),
                ClausePlace::Unwind => "unwind".to_string(),
                ClausePlace::Value(v) => match ids.as_ref().and_then(|ids| ids.values.get(&v)) {
                    Some(canon) => format!("%{canon}"),
                    None => format!("%?{}", v.index()),
                },
                ClausePlace::SpecVar { index } => format!("specvar{index}"),
                ClausePlace::SpecVarNext { index } => format!("specvar{index}'"),
                // v59 (WS1.14): the world epochs, each its own spelling.
                ClausePlace::WorldPre => "world_pre".to_string(),
                ClausePlace::WorldPost => "world_post".to_string(),
                ClausePlace::ParamPointeeEntry { index } => format!("*param{index}"),
            };
            format!("{name:?}:{sort:?}@{place}")
        })
        .collect();
    format!("{sep}bindings=[{}]", rows.join(","))
}

/// One annotation's fingerprint. Every payload is a value except
/// `ProofRef`'s, which is a module-local `ProofId`: it is resolved through
/// `m` to the CLAIM of the obligation it names ([`obligation_claim_by_id`]),
/// the way a certificate's and a proof context's references are, so
/// renumbering the proof table is cosmetic while re-pointing the backref —
/// including by renumbering the table UNDER an unchanged index — is reported.
fn fp_proof(m: &Module, p: &ProofAnnotation) -> String {
    match p {
        ProofAnnotation::InBounds => "InBounds".to_string(),
        ProofAnnotation::NotNull => "NotNull".to_string(),
        ProofAnnotation::ValidBorrow => "ValidBorrow".to_string(),
        ProofAnnotation::UniqueBorrow => "UniqueBorrow".to_string(),
        ProofAnnotation::SharedBorrow => "SharedBorrow".to_string(),
        ProofAnnotation::ValidDealloc => "ValidDealloc".to_string(),
        ProofAnnotation::NoOverflow => "NoOverflow".to_string(),
        ProofAnnotation::NoWrap => "NoWrap".to_string(),
        ProofAnnotation::DivNonZero => "DivNonZero".to_string(),
        ProofAnnotation::ShiftInRange => "ShiftInRange".to_string(),
        ProofAnnotation::Pure => "Pure".to_string(),
        ProofAnnotation::Terminates => "Terminates".to_string(),
        ProofAnnotation::Deterministic => "Deterministic".to_string(),
        ProofAnnotation::Associative => "Associative".to_string(),
        ProofAnnotation::Commutative => "Commutative".to_string(),
        ProofAnnotation::DataRaceFree => "DataRaceFree".to_string(),
        ProofAnnotation::Tainted => "Tainted".to_string(),
        ProofAnnotation::TrustedSink => "TrustedSink".to_string(),
        ProofAnnotation::FreshSymbolicHavoc => "FreshSymbolicHavoc".to_string(),
        ProofAnnotation::RegionHavocStore => "RegionHavocStore".to_string(),
        ProofAnnotation::AtomicOrdering(o) => format!("AtomicOrdering({:?})", o),
        ProofAnnotation::BoundedOutput { lo, hi } => {
            format!("BoundedOutput({},{})", lo.to_bits(), hi.to_bits())
        }
        ProofAnnotation::Monotonic => "Monotonic".to_string(),
        ProofAnnotation::NoAlias => "NoAlias".to_string(),
        ProofAnnotation::Aligned(n) => format!("Aligned({n})"),
        ProofAnnotation::NoPanic => "NoPanic".to_string(),
        ProofAnnotation::NoUndef => "NoUndef".to_string(),
        ProofAnnotation::ReadonlyTable => "ReadonlyTable".to_string(),
        ProofAnnotation::AppendOnlyBuffer => "AppendOnlyBuffer".to_string(),
        ProofAnnotation::AtomicSetInsert => "AtomicSetInsert".to_string(),
        ProofAnnotation::ParallelMap => "ParallelMap".to_string(),
        ProofAnnotation::BoundedLoop(n) => format!("BoundedLoop({n})"),
        ProofAnnotation::DivergenceClass(d) => match d {
            Divergence::Uniform => "DivergenceClass(Uniform)".to_string(),
            Divergence::Low => "DivergenceClass(Low)".to_string(),
            Divergence::High => "DivergenceClass(High)".to_string(),
        },
        // Fusion obligation carrier (clean-expr): fingerprint structurally via
        // its Debug form so semantic diff can detect a changed goal/hypotheses.
        #[cfg(feature = "clean-expr")]
        ProofAnnotation::Goal(ob) => format!("Goal({ob:?})"),
        ProofAnnotation::ProofRef(id) => format!("ProofRef({})", obligation_claim_by_id(m, *id)),
        ProofAnnotation::ValueRange { lo, hi } => format!("ValueRange({lo},{hi})"),
        ProofAnnotation::KnownBits { zeros, ones } => format!("KnownBits({zeros},{ones})"),
        ProofAnnotation::BranchWeights(w) => format!(
            "BranchWeights({})",
            w.iter()
                .map(|x| x.to_string())
                .collect::<Vec<_>>()
                .join(",")
        ),
        ProofAnnotation::Custom(ProofTag(t)) => format!("Custom({t})"),
        ProofAnnotation::Wrapping => "Wrapping".to_string(),
    }
}

// -----------------------------------------------------------------------------
// Fingerprinting
// -----------------------------------------------------------------------------

/// Fingerprint an `Inst` to a canonical string. The fingerprint ignores
/// raw `ValueId` / `BlockId` / type-table-id numbering by substituting
/// the canonical visit-order indices from the supplied maps.
/// The kind (plan item P) and panic site (amendment P) of an assert's
/// fingerprint. The site is IDENTITY: its entry is resolved by function
/// name and a `Global` location by global symbol (as `Call` callees and
/// `GlobalAddr` are), so renumbering stays cosmetic while retargeting either
/// is a body change.
fn fp_assert_kind_and_site(
    m: &Module,
    s: &mut String,
    kind: &crate::inst::AssertKind,
    site: Option<&crate::inst::PanicSite>,
    vv: &dyn Fn(&ValueId) -> String,
) {
    if !kind.is_unspecified() {
        let _ = write!(s, ",{}", kind.keyword());
        if let crate::inst::AssertKind::Overflow(op) = kind {
            let _ = write!(s, ":{}", op.name());
        }
        if let Some([a, b]) = kind.operands() {
            let _ = write!(s, ",{},{}", vv(&a), vv(&b));
        }
    }
    if let Some(site) = site {
        let entry = m
            .functions
            .iter()
            .find(|f| f.id == site.entry)
            .map(|f| f.name.as_str())
            .unwrap_or("<unknown>");
        let _ = write!(s, ",panic {entry} at ");
        match site.location {
            crate::inst::PanicLocation::Global(global) => match m.globals.get(global.as_usize()) {
                Some(g) => {
                    let _ = write!(s, "@{}", g.name);
                }
                None => {
                    let _ = write!(s, "#dangling {}", global.index());
                }
            },
            crate::inst::PanicLocation::Value(value) => s.push_str(&vv(&value)),
        }
    }
}

/// A tensor contraction's axis-pair list, in order, as `a:b` items joined by
/// `separator`: `,` in the fingerprint, `, ` in the rendering (the text
/// spelling's). Axes are positions, not ids, so a changed axis or a reordered
/// pair is a body change.
fn axis_pairs(pairs: &[(u32, u32)], separator: &str) -> String {
    pairs
        .iter()
        .map(|(lhs_axis, rhs_axis)| format!("{lhs_axis}:{rhs_axis}"))
        .collect::<Vec<_>>()
        .join(separator)
}

/// A tensor map body (PKG-U13c), node by node, each as its scalar
/// instruction's operator, its types through `ty` (the fingerprint's or the
/// rendering's spelling) and its lanes. Lanes are positions, not ids, so a
/// changed lane or a reordered node is a body change.
fn map_body(
    m: &Module,
    body: &[crate::TensorMapNode<crate::level::NoExt>],
    ty: fn(&Module, &Ty) -> String,
) -> String {
    body.iter()
        .map(|node| match node {
            crate::TensorMapNode::BinOp {
                op,
                ty: t,
                lhs,
                rhs,
            } => {
                format!("binop {op:?} {} ${lhs} ${rhs}", ty(m, t))
            }
            crate::TensorMapNode::UnOp { op, ty: t, operand } => {
                format!("unop {op:?} {} ${operand}", ty(m, t))
            }
            crate::TensorMapNode::ICmp {
                op,
                ty: t,
                lhs,
                rhs,
            } => {
                format!("icmp {op:?} {} ${lhs} ${rhs}", ty(m, t))
            }
            crate::TensorMapNode::Select {
                ty: t,
                cond,
                then_lane,
                else_lane,
            } => format!("select {} ${cond} ${then_lane} ${else_lane}", ty(m, t)),
            crate::TensorMapNode::Cast {
                op,
                src_ty,
                dst_ty,
                operand,
            } => format!(
                "cast {op:?} {} -> {} ${operand}",
                ty(m, src_ty),
                ty(m, dst_ty)
            ),
        })
        .collect::<Vec<_>>()
        .join("; ")
}

/// A tensor view's node list and node references (PKG-U13c), in order: node
/// ids and axes are positions, so every change is a body change.
fn view_nodes(exprs: &[crate::TensorIndexExpr], shape: &[u32], index: &[u32]) -> String {
    let refs = |nodes: &[u32]| {
        nodes
            .iter()
            .map(|n| format!("${n}"))
            .collect::<Vec<_>>()
            .join(", ")
    };
    format!(
        "exprs [{}] shape [{}] index [{}]",
        exprs
            .iter()
            .map(ToString::to_string)
            .collect::<Vec<_>>()
            .join(", "),
        refs(shape),
        refs(index)
    )
}

fn fp_inst(
    m: &Module,
    inst: &Inst,
    vm: &HashMap<ValueId, u32>,
    bm: &HashMap<BlockId, u32>,
) -> String {
    let mut s = String::new();
    let vv = |v: &ValueId| -> String {
        match vm.get(v) {
            Some(i) => format!("v{i}"),
            None => format!("v?{}", v.0),
        }
    };
    let vb = |b: &BlockId| -> String {
        match bm.get(b) {
            Some(i) => format!("b{i}"),
            None => format!("b?{}", b.0),
        }
    };

    match inst {
        // Crystal lane (wave-DS): the dropped type and the place are both part of the
        // instruction's identity.
        Inst::Drop { ty, ptr } => {
            let _ = write!(s, "Drop({},{})", fp_ty(m, ty), vv(ptr));
        }
        // Amendment D: the drop's identity, then its edges (as `Invoke`'s).
        Inst::DropInvoke {
            ty,
            ptr,
            normal_dest,
            normal_args,
            unwind_dest,
        } => {
            let na = normal_args.iter().map(vv).collect::<Vec<_>>().join(",");
            let _ = write!(
                s,
                "DropInvoke({},{},[{na}],{},{})",
                fp_ty(m, ty),
                vv(ptr),
                vb(normal_dest),
                vb(unwind_dest)
            );
        }
        // Amendment D, Part 2: `CallIndirect`'s identity, then the edges.
        Inst::InvokeIndirect {
            callee,
            sig,
            args,
            calling_conv,
            normal_dest,
            normal_args,
            unwind_dest,
        } => {
            let a = args.iter().map(vv).collect::<Vec<_>>().join(",");
            let na = normal_args.iter().map(vv).collect::<Vec<_>>().join(",");
            let _ = write!(
                s,
                "InvokeIndirect({},{},[{a}],{calling_conv},[{na}],{},{})",
                vv(callee),
                fp_func_ty_ref(m, *sig),
                vb(normal_dest),
                vb(unwind_dest)
            );
        }
        Inst::BinOp { op, ty, lhs, rhs } => {
            let _ = write!(s, "BinOp({op:?},{},{},{})", fp_ty(m, ty), vv(lhs), vv(rhs));
        }
        Inst::SeqMapAddK { ty, seq, k } => {
            let _ = write!(s, "SeqMapAddK({},{},{k})", fp_ty(m, ty), vv(seq));
        }
        Inst::SeqMapNot { ty, seq } => {
            let _ = write!(s, "SeqMapNot({},{})", fp_ty(m, ty), vv(seq));
        }
        Inst::SeqMap { ty, seq, fwd } => {
            // The element function is a FuncId; resolve it by NAME (like Call)
            // so id renumbering does not surface in the fingerprint.
            let name = m
                .functions
                .iter()
                .find(|f| f.id == *fwd)
                .map(|f| f.name.as_str())
                .unwrap_or("<unknown>");
            let _ = write!(s, "SeqMap({},{},{name})", fp_ty(m, ty), vv(seq));
        }
        Inst::UnOp { op, ty, operand } => {
            let _ = write!(s, "UnOp({op:?},{},{})", fp_ty(m, ty), vv(operand));
        }
        Inst::Overflow { op, ty, lhs, rhs } => {
            let _ = write!(
                s,
                "Overflow({op:?},{},{},{})",
                fp_ty(m, ty),
                vv(lhs),
                vv(rhs)
            );
        }
        Inst::ICmp { op, ty, lhs, rhs } => {
            let _ = write!(s, "ICmp({op:?},{},{},{})", fp_ty(m, ty), vv(lhs), vv(rhs));
        }
        Inst::FCmp { op, ty, lhs, rhs } => {
            let _ = write!(s, "FCmp({op:?},{},{},{})", fp_ty(m, ty), vv(lhs), vv(rhs));
        }
        Inst::Cast {
            op,
            src_ty,
            dst_ty,
            operand,
        } => {
            let _ = write!(
                s,
                "Cast({op:?},{},{},{})",
                fp_ty(m, src_ty),
                fp_ty(m, dst_ty),
                vv(operand)
            );
        }
        Inst::PtrData { ptr_ty, ptr } => {
            let _ = write!(s, "PtrData({},{})", fp_ty(m, ptr_ty), vv(ptr));
        }
        Inst::PtrMetadata {
            ptr_ty,
            metadata_ty,
            ptr,
        } => {
            let _ = write!(
                s,
                "PtrMetadata({},{},{})",
                fp_ty(m, ptr_ty),
                fp_ty(m, metadata_ty),
                vv(ptr)
            );
        }
        Inst::PtrFromParts {
            ptr_ty,
            metadata_ty,
            data,
            metadata,
        } => {
            let _ = write!(
                s,
                "PtrFromParts({},{},{},{})",
                fp_ty(m, ptr_ty),
                fp_ty(m, metadata_ty),
                vv(data),
                vv(metadata)
            );
        }
        Inst::Load {
            ty,
            ptr,
            volatile,
            align,
        } => {
            let _ = write!(
                s,
                "Load({},{},{volatile},{:?})",
                fp_ty(m, ty),
                vv(ptr),
                align
            );
        }
        Inst::Store {
            ty,
            ptr,
            value,
            volatile,
            align,
        } => {
            let _ = write!(
                s,
                "Store({},{},{},{volatile},{:?})",
                fp_ty(m, ty),
                vv(ptr),
                vv(value),
                align
            );
        }
        Inst::Alloca { ty, count, align } => {
            let cnt = count.map(|c| vv(&c)).unwrap_or_else(|| "_".to_string());
            let _ = write!(s, "Alloca({},{cnt},{:?})", fp_ty(m, ty), align);
        }
        Inst::HeapAlloc {
            ty,
            count,
            align,
            origin,
        } => {
            let cnt = count.map(|c| vv(&c)).unwrap_or_else(|| "_".to_string());
            let _ = write!(
                s,
                "HeapAlloc({},{cnt},{:?},{:?})",
                fp_ty(m, ty),
                align,
                origin
            );
        }
        Inst::GEP {
            pointee_ty,
            base,
            indices,
            inbounds,
        } => {
            let idx = indices.iter().map(vv).collect::<Vec<_>>().join(",");
            let _ = write!(
                s,
                "GEP({},{},[{idx}],{inbounds})",
                fp_ty(m, pointee_ty),
                vv(base)
            );
        }
        Inst::AtomicLoad { ty, ptr, ordering } => {
            let _ = write!(s, "AtomicLoad({},{},{ordering:?})", fp_ty(m, ty), vv(ptr));
        }
        Inst::AtomicStore {
            ty,
            ptr,
            value,
            ordering,
        } => {
            let _ = write!(
                s,
                "AtomicStore({},{},{},{ordering:?})",
                fp_ty(m, ty),
                vv(ptr),
                vv(value)
            );
        }
        Inst::AtomicRMW {
            op,
            ty,
            ptr,
            value,
            ordering,
        } => {
            let _ = write!(
                s,
                "AtomicRMW({op:?},{},{},{},{ordering:?})",
                fp_ty(m, ty),
                vv(ptr),
                vv(value)
            );
        }
        Inst::CmpXchg {
            ty,
            ptr,
            expected,
            desired,
            success,
            failure,
            weak,
        } => {
            // Trust (crystal D3): strength is part of the instruction's identity; a strong
            // compare-exchange fingerprints exactly as before.
            let _ = write!(
                s,
                "{}({},{},{},{},{success:?},{failure:?})",
                if *weak { "CmpXchgWeak" } else { "CmpXchg" },
                fp_ty(m, ty),
                vv(ptr),
                vv(expected),
                vv(desired)
            );
        }
        Inst::Fence { ordering } => {
            let _ = write!(s, "Fence({ordering:?})");
        }
        Inst::Br { target, args } => {
            let argstr = args.iter().map(vv).collect::<Vec<_>>().join(",");
            let _ = write!(s, "Br({},[{argstr}])", vb(target));
        }
        Inst::CondBr {
            cond,
            then_target,
            then_args,
            else_target,
            else_args,
        } => {
            let t = then_args.iter().map(vv).collect::<Vec<_>>().join(",");
            let e = else_args.iter().map(vv).collect::<Vec<_>>().join(",");
            let _ = write!(
                s,
                "CondBr({},{},[{t}],{},[{e}])",
                vv(cond),
                vb(then_target),
                vb(else_target)
            );
        }
        Inst::Switch {
            value,
            default,
            default_args,
            cases,
            ..
        } => {
            let d = default_args.iter().map(vv).collect::<Vec<_>>().join(",");
            let mut cs = String::new();
            for (ci, c) in cases.iter().enumerate() {
                if ci > 0 {
                    cs.push(',');
                }
                let a = c.args.iter().map(vv).collect::<Vec<_>>().join(",");
                let _ = write!(cs, "{{{},{}", fp_constant(m, &c.value), vb(&c.target));
                let _ = write!(cs, ",[{a}]}}");
            }
            let _ = write!(s, "Switch({},{},[{d}],[{cs}])", vv(value), vb(default));
        }
        Inst::Call { callee, args } | Inst::CallCannotUnwind { callee, args } => {
            // Callee is a FuncId; resolve it by the callee function's *name*
            // when possible so that id renumbering does not surface here.
            let name = m
                .functions
                .iter()
                .find(|f| f.id == *callee)
                .map(|f| f.name.as_str())
                .unwrap_or("<unknown>");
            let a = args.iter().map(vv).collect::<Vec<_>>().join(",");
            let opcode = if matches!(inst, Inst::CallCannotUnwind { .. }) {
                "CallCannotUnwind"
            } else {
                "Call"
            };
            let _ = write!(s, "{opcode}({name},[{a}])");
        }
        Inst::CallIndirect {
            callee,
            sig,
            args,
            calling_conv,
        }
        | Inst::CallIndirectCannotUnwind {
            callee,
            sig,
            args,
            calling_conv,
        } => {
            let opcode = if matches!(inst, Inst::CallIndirectCannotUnwind { .. }) {
                "CallIndirectCannotUnwind"
            } else {
                "CallIndirect"
            };
            let a = args.iter().map(vv).collect::<Vec<_>>().join(",");
            let _ = write!(
                s,
                "{opcode}({},{},[{a}],{calling_conv})",
                vv(callee),
                fp_func_ty_ref(m, *sig)
            );
        }
        Inst::Return { values } => {
            let vs = values.iter().map(vv).collect::<Vec<_>>().join(",");
            let _ = write!(s, "Return([{vs}])");
        }
        Inst::ExtractField {
            ty,
            aggregate,
            field,
        } => {
            let _ = write!(
                s,
                "ExtractField({},{},{field})",
                fp_ty(m, ty),
                vv(aggregate)
            );
        }
        Inst::MakeAggregate {
            ty,
            variant,
            fields,
        } => {
            // The variant clause is part of the identity: two constructions of
            // the SAME enum type differing only in variant are different
            // instructions, and `-` (absent) is a third, distinct spelling.
            let variant = match variant {
                Some(variant) => variant.to_string(),
                None => "-".to_string(),
            };
            let lanes: Vec<String> = fields.iter().map(vv).collect();
            let _ = write!(
                s,
                "MakeAggregate({},{variant},[{}])",
                fp_ty(m, ty),
                lanes.join(",")
            );
        }
        Inst::MakeClosure { ty, func, captures } => {
            let lanes = captures.iter().map(vv).collect::<Vec<_>>().join(",");
            let _ = write!(
                s,
                "MakeClosure({},{},[{}])",
                fp_ty(m, &Ty::Closure(*ty)),
                spec_func_ref(m, *func),
                lanes
            );
        }
        // v50: the lane count is part of the type fingerprint; one operand.
        Inst::ArraySplat { ty, value } => {
            let _ = write!(s, "ArraySplat({},{})", fp_ty(m, ty), vv(value));
        }
        // PKG-U13a: both axis-pair lists are part of the identity, in order
        // (the batch order is the result's axis order).
        Inst::TensorContract {
            ty,
            lhs,
            rhs,
            batch,
            contract,
        } => {
            let _ = write!(
                s,
                "TensorContract({},{},{},[{}],[{}])",
                fp_ty(m, ty),
                vv(lhs),
                vv(rhs),
                axis_pairs(batch, ","),
                axis_pairs(contract, ",")
            );
        }
        // PKG-U13c: the operands by value, the body node by node.
        Inst::TensorMap { ty, args, body } => {
            let a = args.iter().map(vv).collect::<Vec<_>>().join(",");
            let _ = write!(
                s,
                "TensorMap({},[{a}],[{}])",
                fp_ty(m, ty),
                map_body(m, body, fp_ty)
            );
        }
        Inst::TensorReduce {
            ty,
            src,
            op,
            axes,
            order,
        } => {
            let _ = write!(
                s,
                "TensorReduce({},{},{op:?},{axes:?},{order:?})",
                fp_ty(m, ty),
                vv(src)
            );
        }
        Inst::TensorView {
            ty,
            src,
            params,
            exprs,
            shape,
            index,
            fill,
        } => {
            let p = params.iter().map(vv).collect::<Vec<_>>().join(",");
            let fill = fill.as_ref().map_or_else(|| "-".to_string(), vv);
            let _ = write!(
                s,
                "TensorView({},{},[{p}],{},{fill})",
                fp_ty(m, ty),
                vv(src),
                view_nodes(exprs, shape, index)
            );
        }
        // PKG-U13d: the operands by value, the coordinates in axis order.
        Inst::TensorGather { ty, data, coords } => {
            let c = coords.iter().map(vv).collect::<Vec<_>>().join(",");
            let _ = write!(s, "TensorGather({},{},[{c}])", fp_ty(m, ty), vv(data));
        }
        Inst::TensorScatter {
            ty,
            init,
            src,
            coords,
        } => {
            let c = coords.iter().map(vv).collect::<Vec<_>>().join(",");
            let _ = write!(
                s,
                "TensorScatter({},{},{},[{c}])",
                fp_ty(m, ty),
                vv(init),
                vv(src)
            );
        }
        Inst::InsertField {
            ty,
            aggregate,
            field,
            value,
        } => {
            let _ = write!(
                s,
                "InsertField({},{},{field},{})",
                fp_ty(m, ty),
                vv(aggregate),
                vv(value)
            );
        }
        Inst::ExtractElement { ty, array, index } => {
            let _ = write!(
                s,
                "ExtractElement({},{},{})",
                fp_ty(m, ty),
                vv(array),
                vv(index)
            );
        }
        Inst::InsertElement {
            ty,
            array,
            index,
            value,
        } => {
            let _ = write!(
                s,
                "InsertElement({},{},{},{})",
                fp_ty(m, ty),
                vv(array),
                vv(index),
                vv(value)
            );
        }
        Inst::Const { ty, value } => {
            let _ = write!(s, "Const({},{})", fp_ty(m, ty), fp_constant(m, value));
        }
        Inst::NullPtr => s.push_str("NullPtr"),
        Inst::GlobalAddr { global } => {
            // Resolved to the global's link-time SYMBOL, the key its
            // `global @<name>` row is matched by, so reordering
            // `Module.globals` stays cosmetic while retargeting the address to
            // a different global is still a body change. A dangling id keeps
            // its raw index (distinct spelling, never a panic).
            match m.globals.get(global.as_usize()) {
                Some(g) => {
                    let _ = write!(s, "GlobalAddr(@{})", g.name);
                }
                None => {
                    let _ = write!(s, "GlobalAddr(#dangling {})", global.index());
                }
            }
        }
        Inst::Undef { ty } => {
            let _ = write!(s, "Undef({})", fp_ty(m, ty));
        }
        Inst::Assume { cond } => {
            let _ = write!(s, "Assume({})", vv(cond));
        }
        Inst::Assert { cond, kind, site } => {
            let _ = write!(s, "Assert({}", vv(cond));
            // An `Unspecified` kind and an absent site keep the historical
            // fingerprint.
            fp_assert_kind_and_site(m, &mut s, kind, site.as_ref(), &vv);
            s.push(')');
        }
        Inst::AssertInvoke {
            cond,
            kind,
            site,
            normal_dest,
            normal_args,
            unwind_dest,
        } => {
            let _ = write!(s, "AssertInvoke({}", vv(cond));
            fp_assert_kind_and_site(m, &mut s, kind, Some(site), &vv);
            let na = normal_args.iter().map(vv).collect::<Vec<_>>().join(",");
            let _ = write!(s, ",[{na}],{},{})", vb(normal_dest), vb(unwind_dest));
        }
        Inst::Unreachable => s.push_str("Unreachable"),
        Inst::Copy { ty, operand } => {
            let _ = write!(s, "Copy({},{})", fp_ty(m, ty), vv(operand));
        }
        Inst::Select {
            ty,
            cond,
            then_val,
            else_val,
        } => {
            let _ = write!(
                s,
                "Select({},{},{},{})",
                fp_ty(m, ty),
                vv(cond),
                vv(then_val),
                vv(else_val)
            );
        }
        Inst::Borrow { ptr } => {
            let _ = write!(s, "Borrow({})", vv(ptr));
        }
        Inst::BorrowMut { ptr } => {
            let _ = write!(s, "BorrowMut({})", vv(ptr));
        }
        Inst::EndBorrow { borrow_ptr } => {
            let _ = write!(s, "EndBorrow({})", vv(borrow_ptr));
        }
        Inst::Retain { ptr } => {
            let _ = write!(s, "Retain({})", vv(ptr));
        }
        Inst::Release { ptr } => {
            let _ = write!(s, "Release({})", vv(ptr));
        }
        Inst::IsUnique { ptr } => {
            let _ = write!(s, "IsUnique({})", vv(ptr));
        }
        Inst::Dealloc { ptr } => {
            let _ = write!(s, "Dealloc({})", vv(ptr));
        }
        Inst::MemCopy {
            dst,
            src,
            bytes,
            overlap,
        } => {
            let _ = write!(
                s,
                "MemCopy({},{},{},{overlap})",
                vv(dst),
                vv(src),
                vv(bytes)
            );
        }
        Inst::MemSet { dst, byte, bytes } => {
            let _ = write!(s, "MemSet({},{},{})", vv(dst), vv(byte), vv(bytes));
        }
        Inst::OpenFrame { def } => {
            let _ = write!(s, "OpenFrame({})", fp_binding_frame_def(m, def));
        }
        Inst::BindSlot { frame, slot, value } => {
            let _ = write!(s, "BindSlot({},{slot},{})", vv(frame), vv(value));
        }
        Inst::LoadSlot { frame, slot, ty } => {
            let _ = write!(s, "LoadSlot({},{slot},{})", vv(frame), fp_ty(m, ty));
        }
        Inst::CloseFrame { frame } => {
            let _ = write!(s, "CloseFrame({})", vv(frame));
        }
        Inst::CoroSuspend {
            frame,
            state_slot,
            next_state,
            value,
        } => {
            let _ = write!(
                s,
                "CoroSuspend({},{state_slot},{next_state},{})",
                vv(frame),
                vv(value)
            );
        }
        Inst::Invoke {
            callee,
            args,
            normal_dest,
            normal_args,
            unwind_dest,
        } => {
            // Resolve callee by name so id renumbering does not surface (same
            // rationale as the `Call` arm above).
            let name = m
                .functions
                .iter()
                .find(|f| f.id == *callee)
                .map(|f| f.name.as_str())
                .unwrap_or("<unknown>");
            let a = args.iter().map(vv).collect::<Vec<_>>().join(",");
            let na = normal_args.iter().map(vv).collect::<Vec<_>>().join(",");
            let _ = write!(
                s,
                "Invoke({name},[{a}],{},[{na}],{})",
                vb(normal_dest),
                vb(unwind_dest)
            );
        }
        Inst::LandingPad {
            is_cleanup,
            catch_type_indices,
        } => {
            let c = catch_type_indices
                .iter()
                .map(|i| i.to_string())
                .collect::<Vec<_>>()
                .join(",");
            let _ = write!(s, "LandingPad({is_cleanup},[{c}])");
        }
        Inst::Resume { exn } => {
            let _ = write!(s, "Resume({})", vv(exn));
        }
        Inst::DialectOp(d) => {
            let _ = write!(s, "DialectOp({})", fp_dialect(m, d, vm));
        }
    }
    s
}

fn fp_binding_frame_def(m: &Module, def: &BindingFrameDef) -> String {
    let mut s = String::new();
    // Do not include the frame id — it's function-local and may renumber.
    let _ = write!(s, "{{name={}", def.name);
    for (i, slot) in def.slots.iter().enumerate() {
        let _ = write!(s, ",slot{i}:{}:{}", slot.name, fp_ty(m, &slot.ty));
        // silence BindingSlot unused import if no tests touch it
        let _: &BindingSlot = slot;
    }
    s.push('}');
    s
}

fn fp_dialect(m: &Module, d: &DialectInst, vm: &HashMap<ValueId, u32>) -> String {
    let mut s = String::new();
    let _ = write!(s, "{}.{}:v{}", d.dialect, d.op, d.version);
    for v in &d.operands {
        let key = match vm.get(v) {
            Some(i) => format!("v{i}"),
            None => format!("v?{}", v.0),
        };
        let _ = write!(s, ";op={key}");
    }
    for t in &d.result_tys {
        let _ = write!(s, ";rt={}", fp_ty(m, t));
    }
    let mut attrs: Vec<&AttrEntry> = d.attrs.iter().collect();
    attrs.sort_by(|a, b| a.name.cmp(&b.name));
    for a in attrs {
        let _ = write!(s, ";a[{}]={}", a.name, fp_attr(m, &a.value));
    }
    s
}

fn fp_attr(m: &Module, v: &AttrValue) -> String {
    match v {
        AttrValue::I64(x) => format!("i64:{x}"),
        AttrValue::U64(x) => format!("u64:{x}"),
        AttrValue::F64(x) => format!("f64:{}", x.to_bits()),
        AttrValue::Bool(x) => format!("bool:{x}"),
        AttrValue::Str(x) => format!("str:{x}"),
        AttrValue::Bytes(x) => {
            let mut h = String::from("bytes:");
            for b in x {
                let _ = write!(h, "{b:02x}");
            }
            h
        }
        AttrValue::Ty(t) => format!("ty:{}", fp_ty(m, t)),
    }
}

/// Structural fingerprint of a `Ty`. Table references (`Struct`, `Enum`,
/// `Record`, `Closure`, `Func`, `Array`) are resolved against `m` and
/// rendered by definition rather than by id index.
fn fp_ty(m: &Module, t: &Ty) -> String {
    TypeFingerprint::new(m).ty(t)
}

fn fp_tyid_ref(m: &Module, id: TyId) -> String {
    TypeFingerprint::new(m).tyid_ref(id)
}

fn fp_func_ty_ref(m: &Module, id: FuncTyId) -> String {
    TypeFingerprint::new(m).func_ty_ref(id)
}

/// Resolve recursive type graphs without leaking arena ids into the spelling.
/// Back-references use positions in the current structural traversal stack.
struct TypeFingerprint<'a> {
    module: &'a Module,
    active: Vec<(u8, u32)>,
}

impl<'a> TypeFingerprint<'a> {
    fn new(module: &'a Module) -> Self {
        Self {
            module,
            active: Vec::new(),
        }
    }

    fn reference(&mut self, key: (u8, u32), body: impl FnOnce(&mut Self) -> String) -> String {
        if let Some(position) = self.active.iter().position(|entry| *entry == key) {
            return format!("recursive@{position}");
        }
        self.active.push(key);
        let result = body(self);
        self.active.pop();
        result
    }

    fn func_ty_ref(&mut self, id: FuncTyId) -> String {
        self.reference((5, id.0), |this| this.func_ty_ref_definition(id))
    }

    fn closure_ref(&mut self, id: ClosureTyId) -> String {
        self.reference((4, id.0), |this| this.closure_ref_definition(id))
    }

    fn record_ref(&mut self, id: RecordId) -> String {
        self.reference((3, id.0), |this| this.record_ref_definition(id))
    }

    fn enum_ref(&mut self, id: EnumId) -> String {
        self.reference((2, id.0), |this| this.enum_ref_definition(id))
    }

    fn struct_ref(&mut self, id: StructId) -> String {
        self.reference((1, id.0), |this| this.struct_ref_definition(id))
    }

    fn tyid_ref(&mut self, id: TyId) -> String {
        self.reference((0, id.0), |this| this.tyid_ref_definition(id))
    }

    fn ty(&mut self, t: &Ty) -> String {
        let m = self.module;
        match t {
            Ty::Storage(layout) => format!("storage<{},{}>", layout.size_bytes, layout.align_bytes),
            Ty::I8 => "i8".into(),
            Ty::I16 => "i16".into(),
            Ty::I32 => "i32".into(),
            Ty::I64 => "i64".into(),
            Ty::I128 => "i128".into(),
            Ty::U8 => "u8".into(),
            Ty::U16 => "u16".into(),
            Ty::U32 => "u32".into(),
            Ty::U64 => "u64".into(),
            Ty::U128 => "u128".into(),
            Ty::Isize => "isize".into(),
            Ty::Usize => "usize".into(),
            Ty::Char => "char".into(),
            Ty::Error => "error".into(),
            Ty::F16 => "f16".into(),
            Ty::F32 => "f32".into(),
            Ty::F64 => "f64".into(),
            Ty::Bool => "bool".into(),
            Ty::Ptr => "ptr".into(),
            Ty::FatPtr(kind) => format!("fatptr<{}>", self.fat_ptr_kind(kind)),
            Ty::Unit => "unit".into(),
            Ty::Never => "never".into(),
            Ty::Struct(id) => self.struct_ref(*id),
            Ty::Array(elem, n) => format!("arr[{};{}]", self.tyid_ref(*elem), n),
            Ty::Vector(elem, lanes) => format!("vec<{lanes}x{}>", self.ty(elem)),
            // The element is inline (as `Vector`'s); the rank is the type's
            // only other content, so both are in the key.
            Ty::Tensor(elem, rank) => format!("tensor<{}, {rank}>", self.ty(elem)),
            Ty::Tuple(ts) => {
                let mut s = String::from("tuple(");
                for (i, t) in ts.iter().enumerate() {
                    if i > 0 {
                        s.push(',');
                    }
                    s.push_str(&self.ty(t));
                }
                s.push(')');
                s
            }
            Ty::Enum(id) => self.enum_ref(*id),
            Ty::Func(id) => self.func_ty_ref(*id),
            Ty::Ref(inner) => format!("&{}", self.ty(inner)),
            Ty::RefMut(inner) => format!("&mut {}", self.ty(inner)),
            Ty::PtrConst(inner) => format!("*const {}", self.ty(inner)),
            Ty::PtrMut(inner) => format!("*mut {}", self.ty(inner)),
            Ty::Rc(inner) => format!("Rc<{}>", self.ty(inner)),
            Ty::Set(elem, repr) => format!(
                "set<{},{}>",
                self.tyid_ref(*elem),
                match repr {
                    SetRepr::Bitset => "bitset",
                    SetRepr::Boxed => "boxed",
                }
            ),
            Ty::Sequence(elem) => format!("seq<{}>", self.tyid_ref(*elem)),
            Ty::Record(id) => self.record_ref(*id),
            Ty::Closure(id) => self.closure_ref(*id),
            // The predicate is resolved into the fingerprint rather than cited by
            // id: two structurally identical refinements must fingerprint the same
            // even if their modules interned in a different order.
            Ty::Refine(base, pred) => format!(
                "refine<{},{}>",
                self.tyid_ref(*base),
                match m.predicates.get(pred.as_usize()) {
                    Some(p) => format!("{p}"),
                    None => format!("pred#{}", pred.index()),
                }
            ),
            Ty::Dialect(ty) => format!("dialect<{:?},{:?},{}>", ty.namespace, ty.name, ty.version),
            // v43: nominal identity is the pair; nothing to resolve.
            Ty::Handle(ty) => format!("handle<{:?},{:?}>", ty.name, ty.runtime),
            Ty::Ext(e) => e.unreachable(),
        }
    }

    fn fat_ptr_kind(&mut self, kind: &FatPtrKind) -> String {
        match kind {
            FatPtrKind::Slice(elem) => format!("slice {}", self.tyid_ref(*elem)),
            FatPtrKind::Str => "str".to_string(),
            FatPtrKind::TraitObject { trait_id } => format!("dyn.{trait_id}"),
            // Spelled exactly as `Display for FatPtrKind` spells it, and distinct
            // from every other arm: a `ContainerLen` pointer addresses the
            // container header rather than slice content, so fingerprinting it as
            // `str` or `slice` would make two ABI-different fat pointers compare
            // identical in `trust-ir-diff`.
            FatPtrKind::ContainerLen => "container_len".to_string(),
            // v40, the `dyn`-tail sibling, on the same terms: spelled as `Display`
            // spells it and distinct from `dyn.N` -- it addresses the container
            // header rather than the dispatched object, and carries no trait id,
            // so fingerprinting it as any `dyn.N` would make two ABI-different
            // fat pointers compare identical.
            FatPtrKind::ContainerVtable => "container_vtable".to_string(),
        }
    }

    fn tyid_ref_definition(&mut self, id: TyId) -> String {
        let m = self.module;
        match m.types.get(id.as_usize()) {
            Some(t) => self.ty(t),
            None => format!("ty#{}", id.0),
        }
    }

    fn struct_ref_definition(&mut self, id: StructId) -> String {
        let m = self.module;
        let sd: Option<&StructDef> = m.structs.iter().find(|s| s.id == id);
        match sd {
            Some(sd) => {
                // Compile-time coverage (roadmap WS4.13): every field is read.
                let StructDef {
                    id: _, // renumbering: a definition is fingerprinted at every use
                    name,
                    fields,
                    size,
                    align,
                    repr,
                    origin,
                } = sd;
                // `repr` is part of the ABI contract (Rust vs C vs transparent vs
                // packed(N)) — two structs identical in name/size/align/fields but
                // differing in repr are ABI-incompatible, so it MUST participate in
                // the fingerprint or `trust-ir-diff` would report them as identical.
                let mut s = format!("struct({name},size={size:?},align={align:?},repr={repr:?}");
                for f in fields {
                    let _ = write!(s, ",{}", self.field(f));
                }
                // The v58 nominal key SPLITS type identity (two structurally
                // identical defs under different keys are two types), so a
                // re-keyed or un-keyed def is a real change and MUST be seen
                // here; a diff blind to it would call the split "no change".
                // `None` fingerprints as its own spelling, distinct from every
                // key, so gaining or losing a key is a change too.
                let _ = write!(s, ";origin={}", origin_fp(origin.as_ref()));
                s.push(')');
                s
            }
            None => format!("struct#{}", id.0),
        }
    }

    fn enum_ref_definition(&mut self, id: EnumId) -> String {
        let m = self.module;
        let ed: Option<&EnumDef> = m.enums.iter().find(|e| e.id == id);
        match ed {
            Some(ed) => {
                // Compile-time coverage (roadmap WS4.13): every field is read.
                let EnumDef {
                    id: _,            // renumbering: a definition is fingerprinted at every use
                    name: _,          // `enum(<name>`
                    variants: _,      // one fingerprint per variant
                    discriminants: _, // the EFFECTIVE values (raw when ill-formed)
                    repr: _,          // the RESOLVED tag repr (the hint when unavailable)
                    layout: _,        // `layout=` (`canonical` when absent)
                    origin: _,        // the v58 nominal key
                } = ed;
                let mut s = format!("enum({}", ed.name);
                for v in &ed.variants {
                    let _ = write!(s, ",{}", self.variant(v));
                }
                // Canonical-layout identity, not spelling: fingerprint the
                // EFFECTIVE discriminants and the RESOLVED tag repr, so an
                // explicit `A = 0, B = 1` spelling of the implicit default (and a
                // `repr(u8)` hint naming the tag the canonical rule picks anyway)
                // fingerprints equal. An ill-formed assignment (duplicates /
                // overflow / unfittable hint) falls back to the raw fields so two
                // differently-broken defs still compare unequal.
                match ed.effective_discriminants() {
                    Some(discs) => {
                        let _ = write!(s, ";discs{discs:?}");
                    }
                    None => {
                        let _ = write!(s, ";raw_discs{:?}", ed.discriminants);
                    }
                }
                match ed.canonical_tag_repr() {
                    Some(tag) => {
                        let _ = write!(s, ";tag={tag}");
                    }
                    None => {
                        let _ = write!(s, ";tag=unavailable(hint={:?})", ed.repr);
                    }
                }
                match &ed.layout {
                    None => s.push_str(";layout=canonical"),
                    Some(layout) => {
                        let _ = write!(s, ";layout={}:{}:", layout.size, layout.align);
                        match &layout.encoding {
                            // Distinct from the `layout=canonical` spelling above:
                            // that one means NO descriptor, this one is a declared
                            // tag-free image. Confusing them would make an enum
                            // that gained a descriptor look unchanged.
                            crate::ty::EnumTagEncoding::Untagged => {
                                s.push_str("untagged");
                            }
                            crate::ty::EnumTagEncoding::SingleInhabited { variant } => {
                                let _ = write!(s, "single-inhabited@{variant}");
                            }
                            crate::ty::EnumTagEncoding::Direct { tag_offset } => {
                                let _ = write!(s, "direct@{tag_offset}");
                            }
                            crate::ty::EnumTagEncoding::Niche {
                                untagged_variant,
                                niche_variants_start,
                                niche_variants_end,
                                niche_start,
                                niche_offset,
                                niche_ty,
                            } => {
                                let _ = write!(
                                    s,
                                    "niche:{untagged_variant}:{niche_variants_start}:{niche_variants_end}:{niche_start}@{niche_offset}:{niche_ty}"
                                );
                            }
                        }
                        let _ = write!(s, ":offsets={:?}", layout.variant_field_offsets);
                    }
                }
                // v58 nominal key: see `struct_ref_definition`.
                let _ = write!(s, ";origin={}", origin_fp(ed.origin.as_ref()));
                s.push(')');
                s
            }
            None => format!("enum#{}", id.0),
        }
    }

    fn variant(&mut self, v: &EnumVariant) -> String {
        let mut s = format!("[{}", v.name);
        for t in &v.fields {
            let _ = write!(s, ",{}", self.ty(t));
        }
        s.push(']');
        s
    }

    fn record_ref_definition(&mut self, id: RecordId) -> String {
        let m = self.module;
        let rd: Option<&RecordDef> = m.records.iter().find(|r| r.id == id);
        match rd {
            Some(rd) => {
                let mut s = format!("record({}", rd.name);
                for f in &rd.fields {
                    let _ = write!(s, ",{}", self.field(f));
                }
                s.push(')');
                s
            }
            None => format!("record#{}", id.0),
        }
    }

    fn field(&mut self, f: &FieldDef) -> String {
        format!("{}:{}:{:?}", f.name, self.ty(&f.ty), f.offset)
    }

    fn closure_ref_definition(&mut self, id: ClosureTyId) -> String {
        let m = self.module;
        let ct: Option<&ClosureTy> = m.closure_types.get(id.as_usize());
        match ct {
            Some(ct) => {
                let mut s = format!("closure({}", self.func_ty_ref(ct.func));
                for t in &ct.captures {
                    let _ = write!(s, ",{}", self.ty(t));
                }
                s.push(')');
                s
            }
            None => format!("closure#{}", id.0),
        }
    }

    fn func_ty_ref_definition(&mut self, id: FuncTyId) -> String {
        let m = self.module;
        let ft: Option<&FuncTy> = m.func_types.get(id.as_usize());
        match ft {
            Some(ft) => {
                let mut s = String::from("functy(");
                for (i, p) in ft.params.iter().enumerate() {
                    if i > 0 {
                        s.push(',');
                    }
                    s.push_str(&self.ty(p));
                }
                s.push(';');
                for (i, r) in ft.returns.iter().enumerate() {
                    if i > 0 {
                        s.push(',');
                    }
                    s.push_str(&self.ty(r));
                }
                if ft.is_vararg {
                    s.push_str(";vararg");
                }
                if let Some(abi) = &ft.abi {
                    let text = abi.to_canonical_text();
                    use core::fmt::Write;
                    write!(s, ";abi:{}:{text}", text.len()).expect("String write");
                }
                s.push(')');
                s
            }
            None => format!("functy#{}", id.0),
        }
    }
}

fn fp_constant(m: &Module, c: &Constant) -> String {
    match c {
        Constant::Int(x) => format!("i:{x}"),
        // v24: distinct fingerprint prefix — a canonical U128 never collides
        // with an Int value, and the prefix keeps the fingerprint honest.
        Constant::U128(x) => format!("u:{x}"),
        // v25 Bytes: hex fingerprint with the utf8 claim spelled in.
        Constant::Bytes { data, utf8 } => {
            let hex: String = data.iter().map(|b| format!("{b:02x}")).collect();
            format!("by:{}:{hex}", if *utf8 { "u" } else { "r" })
        }
        Constant::Float(x) => format!("f:{}", x.to_bits()),
        Constant::Bool(x) => format!("b:{x}"),
        Constant::Aggregate(cs) => {
            let mut s = String::from("agg(");
            for (i, c) in cs.iter().enumerate() {
                if i > 0 {
                    s.push(',');
                }
                s.push_str(&fp_constant(m, c));
            }
            s.push(')');
            s
        }
        Constant::Array(cs) => {
            let mut s = String::from("array(");
            for (i, c) in cs.iter().enumerate() {
                if i > 0 {
                    s.push(',');
                }
                s.push_str(&fp_constant(m, c));
            }
            s.push(')');
            s
        }
        // v50: the element fingerprint once, then the length — never `len`
        // copies (a splat and the equal list are different SPELLINGS, and the
        // §3 rule keeps a valid module to one of them).
        Constant::Splat { elem, len } => format!("splat({};{len})", fp_constant(m, elem)),
        Constant::Vector(cs) => {
            let mut s = String::from("vec(");
            for (i, c) in cs.iter().enumerate() {
                if i > 0 {
                    s.push(',');
                }
                s.push_str(&fp_constant(m, c));
            }
            s.push(')');
            s
        }
        Constant::Sequence(cs) => {
            let mut s = String::from("seq(");
            for (i, c) in cs.iter().enumerate() {
                if i > 0 {
                    s.push(',');
                }
                s.push_str(&fp_constant(m, c));
            }
            s.push(')');
            s
        }
        Constant::Set(cs) => {
            let mut s = String::from("set(");
            for (i, c) in cs.iter().enumerate() {
                if i > 0 {
                    s.push(',');
                }
                s.push_str(&fp_constant(m, c));
            }
            s.push(')');
            s
        }
        Constant::Record(fs) => {
            let mut s = String::from("rec(");
            for (i, (n, c)) in fs.iter().enumerate() {
                if i > 0 {
                    s.push(',');
                }
                let _ = write!(s, "{n}={}", fp_constant(m, c));
            }
            s.push(')');
            s
        }
        Constant::Closure { func, captures } => {
            // Resolve FuncId via the module's function table when possible,
            // for the same reason calls do.
            let name = m
                .functions
                .iter()
                .find(|f| f.id == *func)
                .map(|f| f.name.as_str())
                .unwrap_or("<unknown>");
            let mut s = format!("cls({name}");
            for c in captures {
                let _ = write!(s, ",{}", fp_constant(m, c));
            }
            s.push(')');
            s
        }
        Constant::FnDef(func) => {
            let name = m
                .functions
                .iter()
                .find(|f| f.id == *func)
                .map(|f| f.name.as_str())
                .unwrap_or("<unknown>");
            format!("fndef({name})")
        }
        Constant::SymbolAddr { symbol, addend } => {
            format!("symaddr({symbol},{addend})")
        }
        Constant::PhantomData => "phantomdata".to_string(),
        Constant::Uninit => "uninit".to_string(),
        Constant::Ext(e) => e.unreachable(),
        // v70: the digest and the shape, never the bytes (the blob table is
        // its own `blobs` row).
        Constant::TensorBlob { digest, dims } => format!("tensor_blob({digest};{dims:?})"),
    }
}

// `FuncId` is referenced in `Call` by id, but fingerprinted by name above.
// Import kept explicit so a tighter follow-up doesn't drop it.
const _FN_ID_REF: fn(&FuncId) -> u32 = |f| f.0;

// -----------------------------------------------------------------------------
// Rendering (for `Replaced.before/after` strings and `to_text`)
// -----------------------------------------------------------------------------

fn render_inst(m: &Module, node: &InstrNode, opts: DiffOptions) -> String {
    // Deliberately concise; we render the same structural shape used for
    // fingerprinting but through the module's display/debug in a way that
    // humans can scan. For stability across platforms we go through our
    // own formatter, not `Debug`.
    let mut s = render_inst_core(m, &node.inst);
    if !opts.ignore_proofs && !node.proofs.is_empty() {
        s.push_str(" !{");
        for (i, p) in node.proofs.iter().enumerate() {
            if i > 0 {
                s.push(',');
            }
            s.push_str(&fp_proof(m, p));
        }
        s.push('}');
    }
    if !opts.ignore_proofs && node.proof_context.is_some() {
        let _ = write!(
            s,
            " ctx{{{}}}",
            fp_proof_context(m, node.proof_context.as_ref())
        );
    }
    s
}

/// The rendered `, KIND` and `, panic @<entry> at LOC` clauses of an assert.
fn render_assert_kind_and_site(
    m: &Module,
    s: &mut String,
    kind: &crate::inst::AssertKind,
    site: Option<&crate::inst::PanicSite>,
) {
    if let crate::inst::AssertKind::Overflow(op) = kind {
        let _ = write!(s, ", overflow {}", op.name());
    } else if let Some([a, b]) = kind.operands() {
        let _ = write!(s, ", {} %{}, %{}", kind.keyword(), a.0, b.0);
    } else if !kind.is_unspecified() {
        let _ = write!(s, ", {}", kind.keyword());
    }
    if let Some(site) = site {
        let entry = m
            .functions
            .iter()
            .find(|f| f.id == site.entry)
            .map(|f| f.name.as_str())
            .unwrap_or("<unknown>");
        let _ = write!(s, ", panic @{entry} at ");
        match site.location {
            crate::inst::PanicLocation::Global(global) => {
                let _ = write!(s, "@global.{}", global.index());
            }
            crate::inst::PanicLocation::Value(value) => {
                let _ = write!(s, "%{}", value.0);
            }
        }
    }
}

fn render_inst_core(m: &Module, inst: &Inst) -> String {
    // Use our structural format (without canonical renumbering maps).
    // Operand ValueIds / BlockIds are rendered as raw indices here since
    // the maps only make sense inside a diffing pass.
    let mut s = String::new();
    match inst {
        // Crystal lane (wave-DS): see the fingerprint twin above.
        Inst::Drop { ty, ptr } => {
            let _ = write!(s, "drop {} %{}", render_ty(m, ty), ptr.0);
        }
        Inst::DropInvoke {
            ty,
            ptr,
            normal_dest,
            normal_args,
            unwind_dest,
        } => {
            let mut na = String::new();
            for (i, arg) in normal_args.iter().enumerate() {
                let _ = write!(na, "{}%{}", if i > 0 { ", " } else { "" }, arg.0);
            }
            let _ = write!(
                s,
                "drop_invoke {} %{} to bb{}({na}) unwind bb{}",
                render_ty(m, ty),
                ptr.0,
                normal_dest.index(),
                unwind_dest.index()
            );
        }
        Inst::InvokeIndirect {
            callee,
            sig,
            args,
            calling_conv,
            normal_dest,
            normal_args,
            unwind_dest,
        } => {
            let mut rest = String::new();
            for a in args {
                let _ = write!(rest, " %{}", a.0);
            }
            let mut na = String::new();
            for (i, arg) in normal_args.iter().enumerate() {
                let _ = write!(na, "{}%{}", if i > 0 { ", " } else { "" }, arg.0);
            }
            let _ = write!(
                s,
                "invoke_indirect %{} sig={} cc={calling_conv}{rest} to bb{}({na}) unwind bb{}",
                callee.0,
                fp_func_ty_ref(m, *sig),
                normal_dest.index(),
                unwind_dest.index()
            );
        }
        Inst::BinOp { op, ty, lhs, rhs } => {
            let _ = write!(
                s,
                "binop {:?} {} %{} %{}",
                op,
                render_ty(m, ty),
                lhs.0,
                rhs.0
            );
        }
        Inst::SeqMapAddK { ty, seq, k } => {
            let _ = write!(s, "seq_map_add_k {} %{} {k}", render_ty(m, ty), seq.0);
        }
        Inst::SeqMapNot { ty, seq } => {
            let _ = write!(s, "seq_map_not {} %{}", render_ty(m, ty), seq.0);
        }
        Inst::SeqMap { ty, seq, fwd } => {
            let name = m
                .functions
                .iter()
                .find(|f| f.id == *fwd)
                .map(|f| f.name.as_str())
                .unwrap_or("<unknown>");
            let _ = write!(s, "seq_map {} %{} @{name}", render_ty(m, ty), seq.0);
        }
        Inst::UnOp { op, ty, operand } => {
            let _ = write!(s, "unop {:?} {} %{}", op, render_ty(m, ty), operand.0);
        }
        Inst::Overflow { op, ty, lhs, rhs } => {
            let _ = write!(
                s,
                "overflow {:?} {} %{} %{}",
                op,
                render_ty(m, ty),
                lhs.0,
                rhs.0
            );
        }
        Inst::ICmp { op, ty, lhs, rhs } => {
            let _ = write!(
                s,
                "icmp {:?} {} %{} %{}",
                op,
                render_ty(m, ty),
                lhs.0,
                rhs.0
            );
        }
        Inst::FCmp { op, ty, lhs, rhs } => {
            let _ = write!(
                s,
                "fcmp {:?} {} %{} %{}",
                op,
                render_ty(m, ty),
                lhs.0,
                rhs.0
            );
        }
        Inst::Cast {
            op,
            src_ty,
            dst_ty,
            operand,
        } => {
            let _ = write!(
                s,
                "cast {:?} {} -> {} %{}",
                op,
                render_ty(m, src_ty),
                render_ty(m, dst_ty),
                operand.0
            );
        }
        Inst::Load { ty, ptr, .. } => {
            let _ = write!(s, "load {} %{}", render_ty(m, ty), ptr.0);
        }
        Inst::Store { ty, ptr, value, .. } => {
            let _ = write!(s, "store {} %{} %{}", render_ty(m, ty), ptr.0, value.0);
        }
        Inst::Alloca { ty, .. } => {
            let _ = write!(s, "alloca {}", render_ty(m, ty));
        }
        Inst::HeapAlloc { ty, origin, .. } => {
            let _ = write!(s, "heap_alloc {:?} {}", origin, render_ty(m, ty));
        }
        Inst::GEP {
            pointee_ty,
            base,
            indices,
            inbounds,
        } => {
            let mut rest = String::new();
            for i in indices {
                let _ = write!(rest, " %{}", i.0);
            }
            let ib = if *inbounds { " inbounds" } else { "" };
            let _ = write!(
                s,
                "gep{} {} %{}{}",
                ib,
                render_ty(m, pointee_ty),
                base.0,
                rest
            );
        }
        Inst::PtrData { ptr_ty, ptr } => {
            let _ = write!(s, "ptr.data {} %{}", render_ty(m, ptr_ty), ptr.0);
        }
        Inst::PtrMetadata {
            ptr_ty,
            metadata_ty,
            ptr,
        } => {
            let _ = write!(
                s,
                "ptr.metadata {} %{} -> {}",
                render_ty(m, ptr_ty),
                ptr.0,
                render_ty(m, metadata_ty)
            );
        }
        Inst::PtrFromParts {
            ptr_ty,
            metadata_ty,
            data,
            metadata,
        } => {
            let _ = write!(
                s,
                "ptr.from_parts {} ptr %{} {} %{}",
                render_ty(m, ptr_ty),
                data.0,
                render_ty(m, metadata_ty),
                metadata.0
            );
        }
        Inst::AtomicLoad { ty, ptr, ordering } => {
            let _ = write!(
                s,
                "atomic.load {} %{} {:?}",
                render_ty(m, ty),
                ptr.0,
                ordering
            );
        }
        Inst::AtomicStore {
            ty,
            ptr,
            value,
            ordering,
        } => {
            let _ = write!(
                s,
                "atomic.store {} %{} %{} {:?}",
                render_ty(m, ty),
                ptr.0,
                value.0,
                ordering
            );
        }
        Inst::AtomicRMW {
            op,
            ty,
            ptr,
            value,
            ordering,
        } => {
            let _ = write!(
                s,
                "atomic.rmw {:?} {} %{} %{} {:?}",
                op,
                render_ty(m, ty),
                ptr.0,
                value.0,
                ordering
            );
        }
        Inst::CmpXchg {
            ty,
            ptr,
            expected,
            desired,
            success,
            failure,
            weak,
        } => {
            let _ = write!(
                s,
                "cmpxchg {}{} %{} %{} %{} {:?} {:?}",
                if *weak { "weak " } else { "" },
                render_ty(m, ty),
                ptr.0,
                expected.0,
                desired.0,
                success,
                failure
            );
        }
        Inst::Fence { ordering } => {
            let _ = write!(s, "fence {:?}", ordering);
        }
        Inst::Br { target, args } => {
            let mut rest = String::new();
            for a in args {
                let _ = write!(rest, " %{}", a.0);
            }
            let _ = write!(s, "br b{}{}", target.0, rest);
        }
        Inst::CondBr {
            cond,
            then_target,
            then_args,
            else_target,
            else_args,
        } => {
            let mut ts = String::new();
            for a in then_args {
                let _ = write!(ts, " %{}", a.0);
            }
            let mut es = String::new();
            for a in else_args {
                let _ = write!(es, " %{}", a.0);
            }
            let _ = write!(
                s,
                "cond_br %{} b{}{} b{}{}",
                cond.0, then_target.0, ts, else_target.0, es
            );
        }
        Inst::Switch {
            value,
            default,
            default_args,
            cases,
            ..
        } => {
            let mut da = String::new();
            for a in default_args {
                let _ = write!(da, " %{}", a.0);
            }
            let _ = write!(s, "switch %{} default b{}{}", value.0, default.0, da);
            for c in cases {
                let mut cs = String::new();
                for a in &c.args {
                    let _ = write!(cs, " %{}", a.0);
                }
                let _ = write!(
                    s,
                    ", case {} b{}{}",
                    render_constant(m, &c.value),
                    c.target.0,
                    cs
                );
                let _: &SwitchCase = c;
            }
        }
        Inst::Call { callee, args } | Inst::CallCannotUnwind { callee, args } => {
            let name = m
                .functions
                .iter()
                .find(|f| f.id == *callee)
                .map(|f| f.name.as_str())
                .unwrap_or("<unknown>");
            let mut rest = String::new();
            for a in args {
                let _ = write!(rest, " %{}", a.0);
            }
            let opcode = if matches!(inst, Inst::CallCannotUnwind { .. }) {
                "call_cannot_unwind"
            } else {
                "call"
            };
            let _ = write!(s, "{opcode} @{name}{rest}");
        }
        Inst::CallIndirect {
            callee,
            sig,
            args,
            calling_conv,
        }
        | Inst::CallIndirectCannotUnwind {
            callee,
            sig,
            args,
            calling_conv,
        } => {
            let opcode = if matches!(inst, Inst::CallIndirectCannotUnwind { .. }) {
                "call_indirect_cannot_unwind"
            } else {
                "call_indirect"
            };
            let mut rest = String::new();
            for a in args {
                let _ = write!(rest, " %{}", a.0);
            }
            let _ = write!(
                s,
                "{opcode} %{} sig={} cc={calling_conv}{rest}",
                callee.0,
                fp_func_ty_ref(m, *sig)
            );
        }
        Inst::Return { values } => {
            let mut rest = String::new();
            for v in values {
                let _ = write!(rest, " %{}", v.0);
            }
            let _ = write!(s, "return{rest}");
        }
        Inst::ExtractField {
            ty,
            aggregate,
            field,
        } => {
            let _ = write!(
                s,
                "extractfield {} %{} .{}",
                render_ty(m, ty),
                aggregate.0,
                field
            );
        }
        Inst::MakeAggregate {
            ty,
            variant,
            fields,
        } => {
            let _ = write!(s, "make_aggregate {}", render_ty(m, ty));
            if let Some(variant) = variant {
                let _ = write!(s, " variant {variant}");
            }
            let lanes: Vec<String> = fields.iter().map(|f| format!("%{}", f.0)).collect();
            let _ = write!(s, " ({})", lanes.join(", "));
        }
        Inst::MakeClosure { ty, func, captures } => {
            let lanes = captures
                .iter()
                .map(|v| format!("%{}", v.0))
                .collect::<Vec<_>>()
                .join(", ");
            let _ = write!(
                s,
                "make_closure {} {} ({})",
                render_ty(m, &Ty::Closure(*ty)),
                spec_func_ref(m, *func),
                lanes
            );
        }
        Inst::ArraySplat { ty, value } => {
            let _ = write!(s, "array_splat {} %{}", render_ty(m, ty), value.0);
        }
        // The text spelling, every field: `tensor_contract TY %a, %b batch
        // [a:b, ...] contract [a:b, ...]`.
        Inst::TensorContract {
            ty,
            lhs,
            rhs,
            batch,
            contract,
        } => {
            let _ = write!(
                s,
                "tensor_contract {} %{}, %{} batch [{}] contract [{}]",
                render_ty(m, ty),
                lhs.0,
                rhs.0,
                axis_pairs(batch, ", "),
                axis_pairs(contract, ", ")
            );
        }
        // PKG-U13c: every field, the body node by node.
        Inst::TensorMap { ty, args, body } => {
            let a = args
                .iter()
                .map(|v| format!("%{}", v.0))
                .collect::<Vec<_>>()
                .join(", ");
            let _ = write!(
                s,
                "tensor_map {} ({a}) {{ {} }}",
                render_ty(m, ty),
                map_body(m, body, render_ty)
            );
        }
        Inst::TensorReduce {
            ty,
            src,
            op,
            axes,
            order,
        } => {
            let _ = write!(
                s,
                "tensor_reduce {op} {} %{} axes {axes:?} order {order}",
                render_ty(m, ty),
                src.0
            );
        }
        Inst::TensorView {
            ty,
            src,
            params,
            exprs,
            shape,
            index,
            fill,
        } => {
            let p = params
                .iter()
                .map(|v| format!("%{}", v.0))
                .collect::<Vec<_>>()
                .join(", ");
            let _ = write!(
                s,
                "tensor_view {} %{} params [{p}] {}",
                render_ty(m, ty),
                src.0,
                view_nodes(exprs, shape, index)
            );
            if let Some(fill) = fill {
                let _ = write!(s, " fill %{}", fill.0);
            }
        }
        // PKG-U13d: every field, the coordinates in axis order.
        Inst::TensorGather { ty, data, coords } => {
            let c = coords
                .iter()
                .map(|v| format!("%{}", v.0))
                .collect::<Vec<_>>()
                .join(", ");
            let _ = write!(
                s,
                "tensor_gather {} %{} coords [{c}]",
                render_ty(m, ty),
                data.0
            );
        }
        Inst::TensorScatter {
            ty,
            init,
            src,
            coords,
        } => {
            let c = coords
                .iter()
                .map(|v| format!("%{}", v.0))
                .collect::<Vec<_>>()
                .join(", ");
            let _ = write!(
                s,
                "tensor_scatter {} %{}, %{} coords [{c}]",
                render_ty(m, ty),
                init.0,
                src.0
            );
        }
        Inst::InsertField {
            ty,
            aggregate,
            field,
            value,
        } => {
            let _ = write!(
                s,
                "insertfield {} %{} .{} %{}",
                render_ty(m, ty),
                aggregate.0,
                field,
                value.0
            );
        }
        Inst::ExtractElement { ty, array, index } => {
            let _ = write!(
                s,
                "extractelem {} %{} %{}",
                render_ty(m, ty),
                array.0,
                index.0
            );
        }
        Inst::InsertElement {
            ty,
            array,
            index,
            value,
        } => {
            let _ = write!(
                s,
                "insertelem {} %{} %{} %{}",
                render_ty(m, ty),
                array.0,
                index.0,
                value.0
            );
        }
        Inst::Const { ty, value } => {
            let _ = write!(
                s,
                "const {} = {}",
                render_ty(m, ty),
                render_constant(m, value)
            );
        }
        Inst::NullPtr => s.push_str("nullptr"),
        Inst::GlobalAddr { global } => {
            let _ = write!(s, "global_addr @global.{}", global.index());
        }
        Inst::Undef { ty } => {
            let _ = write!(s, "undef {}", render_ty(m, ty));
        }
        Inst::Assume { cond } => {
            let _ = write!(s, "assume %{}", cond.0);
        }
        Inst::Assert { cond, kind, site } => {
            let _ = write!(s, "assert %{}", cond.0);
            render_assert_kind_and_site(m, &mut s, kind, site.as_ref());
        }
        Inst::AssertInvoke {
            cond,
            kind,
            site,
            normal_dest,
            normal_args,
            unwind_dest,
        } => {
            let _ = write!(s, "assert_invoke %{}", cond.0);
            render_assert_kind_and_site(m, &mut s, kind, Some(site));
            let mut na = String::new();
            for (i, arg) in normal_args.iter().enumerate() {
                let _ = write!(na, "{}%{}", if i > 0 { ", " } else { "" }, arg.0);
            }
            let _ = write!(
                s,
                " to bb{}({na}) unwind bb{}",
                normal_dest.index(),
                unwind_dest.index()
            );
        }
        Inst::Unreachable => s.push_str("unreachable"),
        Inst::Copy { ty, operand } => {
            let _ = write!(s, "copy {} %{}", render_ty(m, ty), operand.0);
        }
        Inst::Select {
            ty,
            cond,
            then_val,
            else_val,
        } => {
            let _ = write!(
                s,
                "select {} %{} ? %{} : %{}",
                render_ty(m, ty),
                cond.0,
                then_val.0,
                else_val.0
            );
        }
        Inst::Borrow { ptr } => {
            let _ = write!(s, "borrow %{}", ptr.0);
        }
        Inst::BorrowMut { ptr } => {
            let _ = write!(s, "borrow_mut %{}", ptr.0);
        }
        Inst::EndBorrow { borrow_ptr } => {
            let _ = write!(s, "end_borrow %{}", borrow_ptr.0);
        }
        Inst::Retain { ptr } => {
            let _ = write!(s, "retain %{}", ptr.0);
        }
        Inst::Release { ptr } => {
            let _ = write!(s, "release %{}", ptr.0);
        }
        Inst::IsUnique { ptr } => {
            let _ = write!(s, "is_unique %{}", ptr.0);
        }
        Inst::Dealloc { ptr } => {
            let _ = write!(s, "dealloc %{}", ptr.0);
        }
        Inst::MemCopy {
            dst,
            src,
            bytes,
            overlap,
        } => {
            let ov = if *overlap { " overlap" } else { "" };
            let _ = write!(s, "memcopy{ov} %{} %{} %{}", dst.0, src.0, bytes.0);
        }
        Inst::MemSet { dst, byte, bytes } => {
            let _ = write!(s, "memset %{} %{} %{}", dst.0, byte.0, bytes.0);
        }
        Inst::OpenFrame { def } => {
            let _ = write!(s, "open_frame #{} {}", def.id.0, def.name);
        }
        Inst::BindSlot { frame, slot, value } => {
            let _ = write!(s, "bind_slot %{} .{} %{}", frame.0, slot, value.0);
        }
        Inst::LoadSlot { frame, slot, ty } => {
            let _ = write!(s, "load_slot %{} .{} {}", frame.0, slot, render_ty(m, ty));
        }
        Inst::CloseFrame { frame } => {
            let _ = write!(s, "close_frame %{}", frame.0);
        }
        Inst::CoroSuspend {
            frame,
            state_slot,
            next_state,
            value,
        } => {
            let _ = write!(
                s,
                "coro_suspend %{}, {state_slot}, {next_state}, %{}",
                frame.0, value.0
            );
        }
        Inst::Invoke {
            callee,
            args,
            normal_dest,
            normal_args,
            unwind_dest,
        } => {
            let name = m
                .functions
                .iter()
                .find(|f| f.id == *callee)
                .map(|f| f.name.as_str())
                .unwrap_or("<unknown>");
            let mut a = String::new();
            for (i, arg) in args.iter().enumerate() {
                let _ = write!(a, "{}%{}", if i > 0 { ", " } else { "" }, arg.0);
            }
            let mut na = String::new();
            for (i, arg) in normal_args.iter().enumerate() {
                let _ = write!(na, "{}%{}", if i > 0 { ", " } else { "" }, arg.0);
            }
            let _ = write!(
                s,
                "invoke @{name}({a}) to bb{}({na}) unwind bb{}",
                normal_dest.index(),
                unwind_dest.index()
            );
        }
        Inst::LandingPad {
            is_cleanup,
            catch_type_indices,
        } => {
            let _ = write!(s, "landingpad");
            if *is_cleanup {
                let _ = write!(s, " cleanup");
            }
            if !catch_type_indices.is_empty() {
                let _ = write!(s, " catch");
                for (i, idx) in catch_type_indices.iter().enumerate() {
                    let _ = write!(s, "{} {idx}", if i > 0 { "," } else { "" });
                }
            }
        }
        Inst::Resume { exn } => {
            let _ = write!(s, "resume %{}", exn.0);
        }
        Inst::DialectOp(d) => {
            let _ = write!(s, "dialect {}.{} v{}", d.dialect, d.op, d.version);
        }
    }
    s
}

fn render_ty(m: &Module, t: &Ty) -> String {
    // We use the structural fingerprint as the display form for diffs.
    // It's unambiguous and doesn't depend on arena ids.
    fp_ty(m, t)
}

fn render_constant(m: &Module, c: &Constant) -> String {
    fp_constant(m, c)
}

// -----------------------------------------------------------------------------
// Output formatting
// -----------------------------------------------------------------------------

impl Diff {
    /// Render the diff as human-readable unified-diff-style text.
    ///
    /// Empty output when `self.is_empty()`.
    pub fn to_text(&self) -> String {
        if self.is_empty() {
            return String::new();
        }
        let mut s = String::new();
        let _ = writeln!(s, "--- {}\n+++ {}", self.module_name_a, self.module_name_b);
        for c in &self.changes {
            match c {
                FuncChange::Added { name } => {
                    let _ = writeln!(s, "+ function @{name}");
                }
                FuncChange::Removed { name } => {
                    let _ = writeln!(s, "- function @{name}");
                }
                FuncChange::Changed {
                    name,
                    proof_changes,
                    block_changes,
                    meta_changes,
                } => {
                    let _ = writeln!(s, "~ function @{name}");
                    for mc in meta_changes {
                        let _ = writeln!(s, "    ~ {}: {} -> {}", mc.field, mc.before, mc.after);
                    }
                    for pc in proof_changes {
                        match pc {
                            ProofChange::Added { name } => {
                                let _ = writeln!(s, "    + proof {name}");
                            }
                            ProofChange::Removed { name } => {
                                let _ = writeln!(s, "    - proof {name}");
                            }
                        }
                    }
                    for bc in block_changes {
                        match bc {
                            BlockChange::Added { visit } => {
                                let _ = writeln!(s, "    + block (visit {visit})");
                            }
                            BlockChange::Removed { visit } => {
                                let _ = writeln!(s, "    - block (visit {visit})");
                            }
                            BlockChange::StructureDiffers { visit, detail } => {
                                let _ = writeln!(s, "    ~ block (visit {visit}): {detail}");
                            }
                            BlockChange::InstrDiff {
                                visit,
                                instr_changes,
                            } => {
                                let _ = writeln!(s, "    ~ block (visit {visit})");
                                for ic in instr_changes {
                                    match ic {
                                        InstrChange::Added { index, summary } => {
                                            let _ = writeln!(s, "        + [{index}] {summary}");
                                        }
                                        InstrChange::Removed { index, summary } => {
                                            let _ = writeln!(s, "        - [{index}] {summary}");
                                        }
                                        InstrChange::Replaced {
                                            index,
                                            before,
                                            after,
                                        } => {
                                            let _ = writeln!(s, "        - [{index}] {before}");
                                            let _ = writeln!(s, "        + [{index}] {after}");
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        for mc in &self.module_meta_changes {
            let _ = writeln!(s, "~ module {}: {} -> {}", mc.field, mc.before, mc.after);
        }
        for psc in &self.proof_state_changes {
            match psc {
                ProofStateChange::ObligationAdded { obligation, status } => {
                    let _ = writeln!(s, "+ obligation {obligation} [{status}]");
                }
                ProofStateChange::ObligationRemoved { obligation, status } => {
                    let _ = writeln!(s, "- obligation {obligation} [{status}]");
                }
                ProofStateChange::ObligationStatusChanged {
                    obligation,
                    before,
                    after,
                } => {
                    let _ = writeln!(s, "~ obligation {obligation}: {before} -> {after}");
                }
                ProofStateChange::CertificateAdded { certificate } => {
                    let _ = writeln!(s, "+ certificate {certificate}");
                }
                ProofStateChange::CertificateRemoved { certificate } => {
                    let _ = writeln!(s, "- certificate {certificate}");
                }
            }
        }
        s
    }

    /// Render the diff as JSON.
    ///
    /// # Schema (version 1)
    ///
    /// ```text
    /// {
    ///   "schema_version": 1,
    ///   "module_a": "<name>",
    ///   "module_b": "<name>",
    ///   "changes": [
    ///     { "kind": "func_added",   "name": "<fn>" },
    ///     { "kind": "func_removed", "name": "<fn>" },
    ///     { "kind": "func_changed",
    ///       "name": "<fn>",
    ///       "meta": [
    ///         { "field": "producer", "before": "...", "after": "..." },
    ///         { "field": "body_gate", "before": "gated \"clean-kernel-tv\"",
    ///           "after": "ungated" }
    ///       ],
    ///       "proofs": [
    ///         { "kind": "proof_added",   "name": "..." },
    ///         { "kind": "proof_removed", "name": "..." }
    ///       ],
    ///       "blocks": [
    ///         { "kind": "block_added",   "visit": <n> },
    ///         { "kind": "block_removed", "visit": <n> },
    ///         { "kind": "block_structure", "visit": <n>, "detail": "..." },
    ///         { "kind": "block_instrs",  "visit": <n>,
    ///           "instrs": [
    ///             { "kind": "added",    "index": <n>, "summary": "..." },
    ///             { "kind": "removed",  "index": <n>, "summary": "..." },
    ///             { "kind": "replaced", "index": <n>,
    ///               "before": "...", "after": "..." }
    ///           ]
    ///         }
    ///       ]
    ///     }
    ///   ],
    ///   "module_meta": [
    ///     { "field": "tuple_layouts", "before": "...", "after": "..." },
    ///     { "field": "target_info", "before": "...", "after": "..." },
    ///     { "field": "global @G", "before": "...", "after": "..." },
    ///     { "field": "spec_module M", "before": "...", "after": "..." }
    ///   ],
    ///   "proof_state": [
    ///     { "kind": "obligation_added",   "obligation": "...", "status": "..." },
    ///     { "kind": "obligation_removed", "obligation": "...", "status": "..." },
    ///     { "kind": "obligation_status_changed",
    ///       "obligation": "...", "before": "...", "after": "..." },
    ///     { "kind": "certificate_added",   "certificate": "..." },
    ///     { "kind": "certificate_removed", "certificate": "..." }
    ///   ]
    /// }
    /// ```
    pub fn to_json(&self) -> String {
        let mut s = String::new();
        s.push('{');
        let _ = write!(s, "\"schema_version\":1,");
        let _ = write!(s, "\"module_a\":{},", json_string(&self.module_name_a));
        let _ = write!(s, "\"module_b\":{},", json_string(&self.module_name_b));
        s.push_str("\"changes\":[");
        for (i, c) in self.changes.iter().enumerate() {
            if i > 0 {
                s.push(',');
            }
            match c {
                FuncChange::Added { name } => {
                    let _ = write!(
                        s,
                        "{{\"kind\":\"func_added\",\"name\":{}}}",
                        json_string(name)
                    );
                }
                FuncChange::Removed { name } => {
                    let _ = write!(
                        s,
                        "{{\"kind\":\"func_removed\",\"name\":{}}}",
                        json_string(name)
                    );
                }
                FuncChange::Changed {
                    name,
                    proof_changes,
                    block_changes,
                    meta_changes,
                } => {
                    let _ = write!(
                        s,
                        "{{\"kind\":\"func_changed\",\"name\":{},\"meta\":[",
                        json_string(name)
                    );
                    for (mi, mc) in meta_changes.iter().enumerate() {
                        if mi > 0 {
                            s.push(',');
                        }
                        let _ = write!(
                            s,
                            "{{\"field\":{},\"before\":{},\"after\":{}}}",
                            json_string(&mc.field),
                            json_string(&mc.before),
                            json_string(&mc.after)
                        );
                    }
                    s.push_str("],\"proofs\":[");
                    for (pi, pc) in proof_changes.iter().enumerate() {
                        if pi > 0 {
                            s.push(',');
                        }
                        match pc {
                            ProofChange::Added { name } => {
                                let _ = write!(
                                    s,
                                    "{{\"kind\":\"proof_added\",\"name\":{}}}",
                                    json_string(name)
                                );
                            }
                            ProofChange::Removed { name } => {
                                let _ = write!(
                                    s,
                                    "{{\"kind\":\"proof_removed\",\"name\":{}}}",
                                    json_string(name)
                                );
                            }
                        }
                    }
                    s.push_str("],\"blocks\":[");
                    for (bi, bc) in block_changes.iter().enumerate() {
                        if bi > 0 {
                            s.push(',');
                        }
                        match bc {
                            BlockChange::Added { visit } => {
                                let _ = write!(s, "{{\"kind\":\"block_added\",\"visit\":{visit}}}");
                            }
                            BlockChange::Removed { visit } => {
                                let _ =
                                    write!(s, "{{\"kind\":\"block_removed\",\"visit\":{visit}}}");
                            }
                            BlockChange::StructureDiffers { visit, detail } => {
                                let _ = write!(
                                    s,
                                    "{{\"kind\":\"block_structure\",\"visit\":{visit},\"detail\":{}}}",
                                    json_string(detail)
                                );
                            }
                            BlockChange::InstrDiff {
                                visit,
                                instr_changes,
                            } => {
                                let _ = write!(
                                    s,
                                    "{{\"kind\":\"block_instrs\",\"visit\":{visit},\"instrs\":["
                                );
                                for (ii, ic) in instr_changes.iter().enumerate() {
                                    if ii > 0 {
                                        s.push(',');
                                    }
                                    match ic {
                                        InstrChange::Added { index, summary } => {
                                            let _ = write!(
                                                s,
                                                "{{\"kind\":\"added\",\"index\":{index},\"summary\":{}}}",
                                                json_string(summary)
                                            );
                                        }
                                        InstrChange::Removed { index, summary } => {
                                            let _ = write!(
                                                s,
                                                "{{\"kind\":\"removed\",\"index\":{index},\"summary\":{}}}",
                                                json_string(summary)
                                            );
                                        }
                                        InstrChange::Replaced {
                                            index,
                                            before,
                                            after,
                                        } => {
                                            let _ = write!(
                                                s,
                                                "{{\"kind\":\"replaced\",\"index\":{index},\"before\":{},\"after\":{}}}",
                                                json_string(before),
                                                json_string(after)
                                            );
                                        }
                                    }
                                }
                                s.push_str("]}");
                            }
                        }
                    }
                    s.push_str("]}");
                }
            }
        }
        s.push_str("],\"module_meta\":[");
        for (i, mc) in self.module_meta_changes.iter().enumerate() {
            if i > 0 {
                s.push(',');
            }
            let _ = write!(
                s,
                "{{\"field\":{},\"before\":{},\"after\":{}}}",
                json_string(&mc.field),
                json_string(&mc.before),
                json_string(&mc.after)
            );
        }
        s.push_str("],\"proof_state\":[");
        for (i, psc) in self.proof_state_changes.iter().enumerate() {
            if i > 0 {
                s.push(',');
            }
            match psc {
                ProofStateChange::ObligationAdded { obligation, status } => {
                    let _ = write!(
                        s,
                        "{{\"kind\":\"obligation_added\",\"obligation\":{},\"status\":{}}}",
                        json_string(obligation),
                        json_string(status)
                    );
                }
                ProofStateChange::ObligationRemoved { obligation, status } => {
                    let _ = write!(
                        s,
                        "{{\"kind\":\"obligation_removed\",\"obligation\":{},\"status\":{}}}",
                        json_string(obligation),
                        json_string(status)
                    );
                }
                ProofStateChange::ObligationStatusChanged {
                    obligation,
                    before,
                    after,
                } => {
                    let _ = write!(
                        s,
                        "{{\"kind\":\"obligation_status_changed\",\"obligation\":{},\"before\":{},\"after\":{}}}",
                        json_string(obligation),
                        json_string(before),
                        json_string(after)
                    );
                }
                ProofStateChange::CertificateAdded { certificate } => {
                    let _ = write!(
                        s,
                        "{{\"kind\":\"certificate_added\",\"certificate\":{}}}",
                        json_string(certificate)
                    );
                }
                ProofStateChange::CertificateRemoved { certificate } => {
                    let _ = write!(
                        s,
                        "{{\"kind\":\"certificate_removed\",\"certificate\":{}}}",
                        json_string(certificate)
                    );
                }
            }
        }
        s.push(']');
        s.push('}');
        s
    }
}

fn json_string(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    out.push('"');
    for ch in s.chars() {
        match ch {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 => {
                let _ = write!(out, "\\u{:04x}", c as u32);
            }
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

// -----------------------------------------------------------------------------
// Tests
// -----------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        Block, CallingConv, Function, Linkage, Module,
        inst::{BinOp, Inst, SwitchCase},
        node::InstrNode,
        ty::{
            EnumDef, EnumLayoutDescriptor, EnumTagEncoding, EnumVariant, FieldDef, FuncTy,
            RecordDef, StructDef, StructRepr, Ty,
        },
        value::{BlockId, EnumId, FuncId, FuncTyId, RecordId, StructId, ValueId},
    };

    /// Amendment D (§20): the drop-glue table decides what a drop executes,
    /// so a row appearing or re-pointing is a module row even when no body
    /// changed; renumbering the glue function is cosmetic.
    #[test]
    fn drop_glue_change_is_a_module_row() {
        let base = |glue_name: &str, glue_id: u32| {
            let mut m = Module::new("drop_glue_diff");
            let sig = m
                .add_func_type(FuncTy {
                    abi: None,
                    params: vec![Ty::Ptr],
                    returns: vec![],
                    is_vararg: false,
                })
                .expect("Module::add_func_type: test fixture");
            let mut glue = Function::new(FuncId::new(glue_id), glue_name, sig, BlockId::new(0));
            let mut block = Block::new(BlockId::new(0));
            block.params.push((ValueId::new(0), Ty::Ptr));
            block
                .body
                .push(InstrNode::new(Inst::Return { values: vec![] }));
            glue.blocks.push(block);
            m.functions.push(glue);
            m
        };
        let owned = Ty::Struct(StructId::new(0));
        let without = base("drop_owned", 0);
        let mut with = base("drop_owned", 0);
        with.set_drop_glue(owned.clone(), FuncId::new(0)).unwrap();
        let rows = |d: &Diff| -> Vec<String> {
            d.module_meta_changes
                .iter()
                .filter(|mc| mc.field == "drop_glue")
                .map(|mc| format!("{} -> {}", mc.before, mc.after))
                .collect()
        };
        assert_eq!(rows(&diff(&without, &with)).len(), 1, "a row appearing");
        let mut renumbered = base("drop_owned", 9);
        renumbered
            .set_drop_glue(owned.clone(), FuncId::new(9))
            .unwrap();
        assert!(
            rows(&diff(&with, &renumbered)).is_empty(),
            "renumbering is cosmetic"
        );
        let mut repointed = base("drop_other", 0);
        repointed.set_drop_glue(owned, FuncId::new(0)).unwrap();
        let changed = rows(&diff(&with, &repointed));
        assert_eq!(changed.len(), 1, "re-pointing the row");
        assert!(changed[0].contains("@drop_other"), "{changed:?}");
    }

    /// R3 #8: a proved-but-empty summary must NOT fingerprint to the same `∅` marker
    /// as `None` (or as an UNPROVED empty summary), so a `None -> Some(proved)` or a
    /// `proved=false -> true` transition is reported by the diff.
    #[test]
    fn summary_fp_distinguishes_proved_empty_from_none() {
        let m = Module::new("summary_fp");
        let none_fp = summary_fp(&m, None, None);
        let unproved_empty = crate::FunctionSummary::default();
        let proved_empty = crate::FunctionSummary {
            proved: true,
            ..Default::default()
        };
        assert_eq!(
            summary_fp(&m, None, Some(&unproved_empty)),
            none_fp,
            "unproved empty ≡ None"
        );
        assert_ne!(
            summary_fp(&m, None, Some(&proved_empty)),
            none_fp,
            "a proved (empty) summary must be distinguishable from None"
        );
    }

    /// v41: the two fields appended to `FunctionSummary` are contract content,
    /// so an otherwise-empty summary carrying either must NOT collapse to the
    /// `∅` marker — and a retargeted `backed_by` must not diff as no change.
    /// `decreases` landed in v41 with no fingerprint at all, which made a
    /// changed termination measure invisible to `trust-ir-diff`.
    #[test]
    fn summary_fp_reports_decreases_and_backed_by() {
        let mut m = Module::new("summary_fp_v41");
        let a = m
            .intern_import(crate::ModuleImport::new(
                "crate_a",
                crate::proof::ProofDigest::sha256([1u8; 32]),
            ))
            .expect("Module::intern_import: test fixture");
        let b = m
            .intern_import(crate::ModuleImport::new(
                "crate_b",
                crate::proof::ProofDigest::sha256([2u8; 32]),
            ))
            .expect("Module::intern_import: test fixture");

        let none_fp = summary_fp(&m, None, None);

        let only_decreases = crate::FunctionSummary {
            decreases: vec![crate::ProofFormula::new("schema", "n")],
            ..Default::default()
        };
        assert_ne!(
            summary_fp(&m, None, Some(&only_decreases)),
            none_fp,
            "a summary whose only content is a termination measure is not ≡ None"
        );

        let measure_changed = crate::FunctionSummary {
            decreases: vec![crate::ProofFormula::new("schema", "n - 1")],
            ..Default::default()
        };
        assert_ne!(
            summary_fp(&m, None, Some(&only_decreases)),
            summary_fp(&m, None, Some(&measure_changed)),
            "changing the termination measure must be reported"
        );

        let backed_a = crate::FunctionSummary {
            proved: true,
            backed_by: Some(crate::ExternRef::new(a, "foo")),
            ..Default::default()
        };
        let backed_b = crate::FunctionSummary {
            proved: true,
            backed_by: Some(crate::ExternRef::new(b, "foo")),
            ..Default::default()
        };
        assert_ne!(
            summary_fp(&m, None, Some(&backed_a)),
            summary_fp(&m, None, Some(&backed_b)),
            "retargeting `proved`'s authority at a different crate must be reported"
        );
    }

    /// v59 (WS1.14): the world epochs are distinct places — re-binding a
    /// clause name from the entry world to the exit world (or to the legacy
    /// un-epoched `World`) changes what the clause states, so it is reported.
    #[test]
    fn summary_fp_tells_the_world_epochs_apart() {
        use crate::proof::{ClauseBinding, ClausePlace, ClauseSort};
        let m = Module::new("summary_fp_epochs");
        let bound = |place: ClausePlace| {
            let mut clause = crate::ProofFormula::smtlib2("(= h h)", "Bool");
            clause.bindings = vec![(
                "h".to_string(),
                ClauseBinding {
                    sort: ClauseSort::Int,
                    place,
                },
            )];
            summary_fp(
                &m,
                None,
                Some(&crate::FunctionSummary::new().ensuring(clause)),
            )
        };
        let pre = bound(ClausePlace::WorldPre);
        let post = bound(ClausePlace::WorldPost);
        let legacy = bound(ClausePlace::World);
        assert_ne!(pre, post);
        assert_ne!(pre, legacy);
        assert_ne!(post, legacy);
    }

    /// v59 (WS1.14): the effect frame is contract content. A summary whose
    /// only content is `effects` is not ≡ None, `Some(pure)` is not ≡ None
    /// (UNRECORDED), and widening `writes` is reported.
    #[test]
    fn summary_fp_reports_effects() {
        let m = Module::new("summary_fp_effects");
        let none_fp = summary_fp(&m, None, None);
        let pure = crate::FunctionSummary::new().with_effects(crate::EffectSummary::pure());
        assert_ne!(summary_fp(&m, None, Some(&pure)), none_fp);
        let writer =
            crate::FunctionSummary::new().with_effects(crate::EffectSummary::pure().writing(
                crate::EffectSet::of([crate::EffectPlace::ParamPointee { index: 0 }]),
            ));
        assert_ne!(
            summary_fp(&m, None, Some(&pure)),
            summary_fp(&m, None, Some(&writer))
        );
        assert_eq!(
            summary_fp(&m, None, Some(&writer)),
            summary_fp(&m, None, Some(&writer.clone()))
        );
    }

    /// v23: a producer-provenance flip on an otherwise-identical function is a
    /// real change — reported via `meta_changes`, and NOT suppressed by
    /// `--ignore-proofs` (provenance is metadata, not proof coverage).
    #[test]
    fn producer_change_is_reported_and_survives_ignore_proofs() {
        let a = single_return_module("m", 0, 0);
        let mut b_mod = single_return_module("m", 0, 0);
        b_mod.functions[0].producer = Some(crate::Producer::Clean);

        for opts in [
            DiffOptions::default(),
            DiffOptions {
                ignore_proofs: true,
                ..DiffOptions::default()
            },
        ] {
            let d = diff_with(&a, &b_mod, opts);
            assert!(
                !d.is_empty(),
                "producer flip must surface (ignore_proofs={})",
                opts.ignore_proofs
            );
            match &d.changes[0] {
                FuncChange::Changed {
                    name, meta_changes, ..
                } => {
                    assert_eq!(name, "main");
                    assert_eq!(meta_changes.len(), 1);
                    assert_eq!(meta_changes[0].field, "producer");
                    assert_eq!(meta_changes[0].before, "-");
                    assert_eq!(meta_changes[0].after, "clean");
                }
                other => panic!("expected Changed, got {other:?}"),
            }
            let text = d.to_text();
            assert!(text.contains("~ producer: - -> clean"), "{text}");
            let json = d.to_json();
            assert!(
                json.contains(
                    "\"meta\":[{\"field\":\"producer\",\"before\":\"-\",\"after\":\"clean\"}]"
                ),
                "{json}"
            );
        }

        // Same producer on both sides: no change.
        let mut a2 = single_return_module("m", 0, 0);
        a2.functions[0].producer = Some(crate::Producer::Clean);
        assert!(diff(&a2, &b_mod).is_empty());
    }

    #[test]
    fn source_provenance_change_is_reported_and_survives_ignore_proofs() {
        let a = single_return_module("m", 0, 0);
        let mut b_mod = a.clone();
        b_mod.functions[0].source_provenance = Some(crate::SourceProvenance::new(
            crate::proof::ProofDigest::sha256([1; 32]),
            crate::proof::ProofDigest::sha256([2; 32]),
            Vec::new(),
        ));

        for opts in [
            DiffOptions::default(),
            DiffOptions {
                ignore_proofs: true,
                ..DiffOptions::default()
            },
        ] {
            let result = diff_with(&a, &b_mod, opts);
            assert_eq!(result.changes.len(), 1);
            let FuncChange::Changed { meta_changes, .. } = &result.changes[0] else {
                panic!("expected changed function");
            };
            assert_eq!(meta_changes.len(), 1);
            assert_eq!(meta_changes[0].field, "source_provenance");
            assert_eq!(meta_changes[0].before, "-");
            assert!(meta_changes[0].after.contains("schema=1"));
        }
    }

    /// v32/v33 debug names and lexical scopes are claim-style diagnostics,
    /// like source spans. They do not change execution or proof authority and
    /// therefore stay outside the semantic diff.
    #[test]
    fn debug_metadata_is_ignored_as_cosmetic() {
        // The file table is interned on BOTH sides: its LENGTH is compared
        // (the `files` row, WS4.13, mirroring the V3 identity), so a file
        // entering the table is a reported change of its own
        // (`diff_fields::files_count_is_reported_and_strings_are_not`); what
        // stays cosmetic is the debug metadata that indexes it.
        let mut a = single_return_module("m", 0, 0);
        let file = a
            .intern_file("src/main.rs")
            .expect("Module::intern_file: test fixture");
        let mut b_mod = a.clone();
        b_mod.files[file as usize] = "/elsewhere/src/main.rs".into();
        let function = &mut b_mod.functions[0];
        function.value_names = Some(vec![(v(0), "unit value".to_string())]);
        function.scopes = Some(vec![crate::ScopeData {
            parent: None,
            span: Some(crate::SourceSpan {
                file,
                line: 1,
                col: 0,
            }),
            inlined_at: None,
        }]);
        function.blocks[0].body[0].span = Some(crate::SourceSpan {
            file,
            line: 1,
            col: 4,
        });
        function.blocks[0].body[0].scope = Some(0);

        for opts in [
            DiffOptions::default(),
            DiffOptions {
                ignore_proofs: true,
                ..DiffOptions::default()
            },
        ] {
            let d = diff_with(&a, &b_mod, opts);
            assert!(
                d.is_empty(),
                "debug metadata must stay cosmetic (ignore_proofs={}): {}",
                opts.ignore_proofs,
                d.to_text()
            );
        }
    }

    // Helpers --------------------------------------------------------------

    fn make_unit_ft(m: &mut Module) -> FuncTyId {
        m.add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::Unit],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture")
    }

    fn v(n: u32) -> ValueId {
        ValueId::new(n)
    }

    fn b(n: u32) -> BlockId {
        BlockId::new(n)
    }

    /// Build a module with a single `@main` function that returns unit.
    fn single_return_module(name: &str, value_base: u32, block_base: u32) -> Module {
        let mut m = Module::new(name);
        let ft = make_unit_ft(&mut m);
        let entry = b(block_base);
        let mut f = Function::new(FuncId::new(0), "main", ft, entry);
        f.calling_conv = CallingConv::C;
        f.linkage = Linkage::External;
        let mut blk = Block::new(entry);
        // %N = const Unit = Unit
        blk.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::Unit,
                value: Constant::Aggregate(vec![]),
            })
            .with_result(v(value_base)),
        );
        blk.body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        f.blocks.push(blk);
        m.try_add_function(f)
            .expect("Module::try_add_function: test fixture");
        m
    }

    // 1. same module produces empty diff ------------------------------------

    #[test]
    fn same_module_diffs_empty() {
        let a = single_return_module("m", 0, 0);
        let d = diff(&a, &a);
        assert!(d.is_empty(), "{}", d.to_text());
        assert_eq!(d.exit_code(), 0);
    }

    // 2. id renumbering produces no diff ------------------------------------

    #[test]
    fn id_renumbering_produces_no_diff() {
        let a = single_return_module("m", 0, 0);
        let b = single_return_module("m", 42, 17);
        let d = diff(&a, &b);
        assert!(d.is_empty(), "{}", d.to_text());
    }

    // 2b. a changed separate-compilation contract is reported (and suppressed
    //     under ignore_proofs) -------------------------------------------------

    #[test]
    fn function_summary_change_is_a_proof_change() {
        use crate::{FunctionSummary, ProofFormula};
        let a = single_return_module("m", 0, 0);
        let mut b = single_return_module("m", 0, 0);
        b.functions[0].summary = Some(
            FunctionSummary::new()
                .ensuring(ProofFormula::smtlib2("(> result 0)", "Bool"))
                .proved(),
        );
        // Default options: the contract change shows up as a function change.
        let d = diff(&a, &b);
        assert!(!d.is_empty(), "a contract change must be reported");
        // ignore_proofs suppresses it (the contract is proof-ish).
        let d2 = diff_with(
            &a,
            &b,
            DiffOptions {
                ignore_proofs: true,
                ..DiffOptions::default()
            },
        );
        assert!(
            d2.is_empty(),
            "ignore_proofs must suppress the contract change: {}",
            d2.to_text()
        );
    }

    // 3. declaration-order-only difference in functions --------------------

    #[test]
    fn declaration_order_produces_no_diff() {
        let mut m_a = Module::new("m");
        let ft = make_unit_ft(&mut m_a);
        // A declares foo then bar.
        for (idx, name) in [(0u32, "foo"), (1u32, "bar")].iter() {
            let mut f = Function::new(FuncId::new(*idx), *name, ft, b(0));
            let mut blk = Block::new(b(0));
            blk.body
                .push(InstrNode::new(Inst::Return { values: vec![] }));
            f.blocks.push(blk);
            m_a.try_add_function(f)
                .expect("Module::try_add_function: test fixture");
        }

        let mut m_b = Module::new("m");
        let ft = make_unit_ft(&mut m_b);
        // B declares bar then foo (and also renumbers ids).
        for (idx, name) in [(5u32, "bar"), (99u32, "foo")].iter() {
            let mut f = Function::new(FuncId::new(*idx), *name, ft, b(7));
            let mut blk = Block::new(b(7));
            blk.body
                .push(InstrNode::new(Inst::Return { values: vec![] }));
            f.blocks.push(blk);
            m_b.try_add_function(f)
                .expect("Module::try_add_function: test fixture");
        }

        let d = diff(&m_a, &m_b);
        assert!(d.is_empty(), "{}", d.to_text());
    }

    // 4. added instruction is reported ------------------------------------

    #[test]
    fn added_instruction_reports_exactly_that_instruction() {
        let mut a = Module::new("m");
        let ft_i = a
            .add_func_type(FuncTy {
                params: vec![],
                returns: vec![Ty::I32],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut fa = Function::new(FuncId::new(0), "main", ft_i, b(0));
        let mut blk = Block::new(b(0));
        blk.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(1),
            })
            .with_result(v(0)),
        );
        blk.body
            .push(InstrNode::new(Inst::Return { values: vec![v(0)] }));
        fa.blocks.push(blk);
        a.try_add_function(fa)
            .expect("Module::try_add_function: test fixture");

        let mut b_mod = Module::new("m");
        let ft_i = b_mod
            .add_func_type(FuncTy {
                params: vec![],
                returns: vec![Ty::I32],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut fb = Function::new(FuncId::new(0), "main", ft_i, b(0));
        let mut blk = Block::new(b(0));
        blk.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(1),
            })
            .with_result(v(0)),
        );
        blk.body.push(
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I32,
                lhs: v(0),
                rhs: v(0),
            })
            .with_result(v(1)),
        );
        blk.body
            .push(InstrNode::new(Inst::Return { values: vec![v(1)] }));
        fb.blocks.push(blk);
        b_mod
            .try_add_function(fb)
            .expect("Module::try_add_function: test fixture");

        let d = diff(&a, &b_mod);
        assert_eq!(d.changes.len(), 1);
        match &d.changes[0] {
            FuncChange::Changed {
                name,
                block_changes,
                ..
            } => {
                assert_eq!(name, "main");
                assert_eq!(block_changes.len(), 1);
                match &block_changes[0] {
                    BlockChange::InstrDiff {
                        visit,
                        instr_changes,
                    } => {
                        assert_eq!(*visit, 0);
                        // We expect the add inserted at position 1 AND the
                        // return to shift — so Replaced at index 1 + Added
                        // at index 2 (the return), OR an Added at index 1
                        // and a Replaced at index 2. Because the diff is
                        // positional, the most natural report is:
                        //   [1] Const is now BinOp (Replaced)
                        //   [2] nothing -> Return (Added)
                        // The first-block-instr-case is reported as either
                        // Replaced or Added; check the aggregate is sound.
                        assert!(
                            !instr_changes.is_empty(),
                            "expected instruction changes, got none"
                        );
                        // There must be exactly one extra instruction in B.
                        let mut added = 0i32;
                        let mut removed = 0i32;
                        let mut replaced = 0i32;
                        for ic in instr_changes {
                            match ic {
                                InstrChange::Added { .. } => added += 1,
                                InstrChange::Removed { .. } => removed += 1,
                                InstrChange::Replaced { .. } => replaced += 1,
                            }
                        }
                        assert_eq!(added - removed, 1, "net change should be +1 instruction");
                        assert!(added + replaced >= 1);
                    }
                    other => panic!("expected InstrDiff, got {other:?}"),
                }
            }
            other => panic!("expected Changed, got {other:?}"),
        }
        assert_eq!(d.exit_code(), 1);
    }

    // 5. JSON output is valid JSON ----------------------------------------

    #[test]
    fn json_output_is_valid_json() {
        let a = single_return_module("m", 0, 0);
        let mut b_mod = single_return_module("m", 0, 0);
        // Force a difference: add a second function.
        let ft = make_unit_ft(&mut b_mod);
        let mut f = Function::new(FuncId::new(99), "extra", ft, b(0));
        let mut blk = Block::new(b(0));
        blk.body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        f.blocks.push(blk);
        b_mod
            .try_add_function(f)
            .expect("Module::try_add_function: test fixture");

        let d = diff(&a, &b_mod);
        let j = d.to_json();
        // Round-trip through serde_json to prove it parses.
        let _v: serde_json::Value = serde_json::from_str(&j).expect("to_json must emit valid JSON");
    }

    // 6. struct id renumbering produces no diff ----------------------------

    #[test]
    fn struct_id_renumbering_produces_no_diff() {
        // Module A: one struct { x: i32, y: i32 }; main returns unit.
        let mut a = Module::new("m");
        let sa = a.add_struct(StructDef {
            id: StructId::new(3),
            name: "P".into(),
            fields: vec![
                FieldDef {
                    name: "x".into(),
                    ty: Ty::I32,
                    offset: None,
                },
                FieldDef {
                    name: "y".into(),
                    ty: Ty::I32,
                    offset: None,
                },
            ],
            size: None,
            align: None,
            repr: Default::default(),
            origin: None,
        });
        let ft = a
            .add_func_type(FuncTy {
                params: vec![Ty::Struct(sa)],
                returns: vec![Ty::Unit],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut f = Function::new(FuncId::new(0), "main", ft, b(0));
        let mut blk = Block::new(b(0));
        blk.params.push((v(0), Ty::Struct(sa)));
        blk.body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        f.blocks.push(blk);
        a.try_add_function(f)
            .expect("Module::try_add_function: test fixture");

        // Module B: same struct with id=17 instead of 3.
        let mut b_mod = Module::new("m");
        let sb = b_mod.add_struct(StructDef {
            id: StructId::new(17),
            name: "P".into(),
            fields: vec![
                FieldDef {
                    name: "x".into(),
                    ty: Ty::I32,
                    offset: None,
                },
                FieldDef {
                    name: "y".into(),
                    ty: Ty::I32,
                    offset: None,
                },
            ],
            size: None,
            align: None,
            repr: Default::default(),
            origin: None,
        });
        let ft = b_mod
            .add_func_type(FuncTy {
                params: vec![Ty::Struct(sb)],
                returns: vec![Ty::Unit],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut f = Function::new(FuncId::new(0), "main", ft, b(0));
        let mut blk = Block::new(b(0));
        blk.params.push((v(0), Ty::Struct(sb)));
        blk.body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        f.blocks.push(blk);
        b_mod
            .try_add_function(f)
            .expect("Module::try_add_function: test fixture");

        let d = diff(&a, &b_mod);
        assert!(d.is_empty(), "{}", d.to_text());
    }

    // 6b. struct repr difference IS a diff --------------------------------

    #[test]
    fn struct_repr_difference_produces_diff() {
        // Two modules whose only difference is a struct's ABI repr (C vs Rust).
        // size/align/name/fields all identical, but repr is part of the ABI
        // contract, so `trust-ir-diff` MUST report a change.
        fn module_with_repr(repr: StructRepr) -> Module {
            let mut m = Module::new("m");
            let s = m.add_struct(StructDef {
                id: StructId::new(0),
                name: "P".into(),
                fields: vec![FieldDef {
                    name: "x".into(),
                    ty: Ty::I32,
                    offset: None,
                }],
                size: Some(4),
                align: Some(4),
                repr,
                origin: None,
            });
            let ft = m
                .add_func_type(FuncTy {
                    params: vec![Ty::Struct(s)],
                    returns: vec![Ty::Unit],
                    abi: None,
                    is_vararg: false,
                })
                .expect("Module::add_func_type: test fixture");
            let mut f = Function::new(FuncId::new(0), "main", ft, b(0));
            let mut blk = Block::new(b(0));
            blk.params.push((v(0), Ty::Struct(s)));
            blk.body
                .push(InstrNode::new(Inst::Return { values: vec![] }));
            f.blocks.push(blk);
            m.try_add_function(f)
                .expect("Module::try_add_function: test fixture");
            m
        }

        let a = module_with_repr(StructRepr::C);
        let b_mod = module_with_repr(StructRepr::Rust);
        let d = diff(&a, &b_mod);
        assert!(
            !d.is_empty(),
            "differing struct repr (C vs Rust) must produce a diff"
        );
    }

    // 6c. the v58 nominal key IS a diff ------------------------------------

    /// A definition's `origin` splits type identity (WS3.9), so a diff that
    /// ignored it would report a re-keyed, newly keyed or un-keyed definition
    /// as "no change". Pinned for both tables, with the control that an
    /// EQUAL key on both sides is not a change.
    #[test]
    fn type_origin_difference_produces_diff() {
        use crate::proof::ProofDigest;
        use crate::ty::TypeOrigin;

        fn key(path: u8) -> TypeOrigin {
            TypeOrigin::Rust {
                stable_crate_id: 7,
                def_path_hash: [path; 16],
                args_digest: ProofDigest::sha256([1; 32]),
            }
        }
        fn module_with_keys(
            struct_origin: Option<TypeOrigin>,
            enum_origin: Option<TypeOrigin>,
        ) -> Module {
            let mut m = Module::new("m");
            let s = m.add_struct(StructDef {
                id: StructId::new(0),
                name: "P".into(),
                fields: vec![FieldDef {
                    name: "x".into(),
                    ty: Ty::I32,
                    offset: None,
                }],
                size: Some(4),
                align: Some(4),
                repr: StructRepr::Rust,
                origin: struct_origin,
            });
            let mut e = EnumDef::new(
                EnumId::new(0),
                "E",
                vec![EnumVariant {
                    name: "A".into(),
                    fields: vec![],
                    field_names: vec![],
                }],
            );
            e.origin = enum_origin;
            let e = m.add_enum(e);
            let ft = m
                .add_func_type(FuncTy {
                    abi: None,
                    params: vec![Ty::Struct(s), Ty::Enum(e)],
                    returns: vec![Ty::Unit],
                    is_vararg: false,
                })
                .expect("Module::add_func_type: test fixture");
            let mut f = Function::new(FuncId::new(0), "main", ft, b(0));
            let mut blk = Block::new(b(0));
            blk.params.push((v(0), Ty::Struct(s)));
            blk.params.push((v(1), Ty::Enum(e)));
            blk.body
                .push(InstrNode::new(Inst::Return { values: vec![] }));
            f.blocks.push(blk);
            m.try_add_function(f)
                .expect("Module::try_add_function: test fixture");
            m
        }

        // Control: equal keys on both sides are not a change.
        let keyed = module_with_keys(Some(key(0xa1)), Some(key(0xb2)));
        let same = module_with_keys(Some(key(0xa1)), Some(key(0xb2)));
        let d = diff(&keyed, &same);
        assert!(d.is_empty(), "{}", d.to_text());

        // A re-keyed struct (one source entity swapped for another).
        let rekeyed_struct = module_with_keys(Some(key(0xa2)), Some(key(0xb2)));
        assert!(
            !diff(&keyed, &rekeyed_struct).is_empty(),
            "a struct under a different origin is a different type"
        );
        // A re-keyed enum.
        let rekeyed_enum = module_with_keys(Some(key(0xa1)), Some(key(0xb3)));
        assert!(
            !diff(&keyed, &rekeyed_enum).is_empty(),
            "an enum under a different origin is a different type"
        );
        // Losing the key entirely: `None` is its own spelling, never equal to
        // a key, so un-keying is visible too (and so is keying, by symmetry).
        let unkeyed = module_with_keys(None, None);
        assert!(
            !diff(&keyed, &unkeyed).is_empty(),
            "dropping the origin is a change"
        );
        assert!(
            !diff(&unkeyed, &keyed).is_empty(),
            "gaining the origin is a change"
        );
        let d = diff(&unkeyed, &module_with_keys(None, None));
        assert!(d.is_empty(), "{}", d.to_text());
    }

    // 6d. closure layout rows are keyed by STRUCTURE, not ClosureTyId ------

    /// A `closure_layouts` row names its closure type by arena id on the wire,
    /// but the diff must key it structurally, exactly as `tuple_layouts_fp`
    /// keys a tuple row: renumbering the closure types is no change, while
    /// moving a frame from one closure type to another IS one — and an
    /// index-keyed row gets both of those backwards.
    #[test]
    fn closure_layout_rows_are_keyed_by_closure_structure() {
        use crate::ty::ClosureTy;
        use crate::{ClosureLayoutDescriptor, Endianness, TargetInfo};

        // Two closure types with the SAME capture shape (one `U64`) and
        // different apparent signatures, so their frames are interchangeable
        // in arity and distinguishable only by which type they belong to.
        fn module(reverse_ids: bool, swap_frames: bool) -> Module {
            let mut m = Module::new("closure_layouts");
            m.target_info = Some(TargetInfo {
                triple: "aarch64-apple-darwin".into(),
                pointer_size: 8,
                endianness: Endianness::Little,
                abi: None,
                struct_passing: Default::default(),
            });
            let wide = m
                .add_func_type(FuncTy {
                    abi: None,
                    params: vec![Ty::U64],
                    returns: vec![Ty::U64],
                    is_vararg: false,
                })
                .expect("Module::add_func_type: test fixture");
            let narrow = m
                .add_func_type(FuncTy {
                    abi: None,
                    params: vec![Ty::U32],
                    returns: vec![Ty::U32],
                    is_vararg: false,
                })
                .expect("Module::add_func_type: test fixture");
            let wide_closure = ClosureTy {
                func: wide,
                captures: vec![Ty::U64],
            };
            let narrow_closure = ClosureTy {
                func: narrow,
                captures: vec![Ty::U64],
            };
            let (wide_id, narrow_id) = if reverse_ids {
                let n = m
                    .add_closure_type(narrow_closure)
                    .expect("Module::add_closure_type: test fixture");
                let w = m
                    .add_closure_type(wide_closure)
                    .expect("Module::add_closure_type: test fixture");
                (w, n)
            } else {
                let w = m
                    .add_closure_type(wide_closure)
                    .expect("Module::add_closure_type: test fixture");
                let n = m
                    .add_closure_type(narrow_closure)
                    .expect("Module::add_closure_type: test fixture");
                (w, n)
            };
            // The wide closure's frame is 8 bytes; the narrow one's is a
            // 16-byte frame with its capture at offset 8.
            let (wide_frame, narrow_frame) = if swap_frames {
                (narrow_id, wide_id)
            } else {
                (wide_id, narrow_id)
            };
            m.closure_layouts.push(ClosureLayoutDescriptor {
                origin: None,
                closure: wide_frame,
                size: 8,
                align: 8,
                capture_offsets: vec![0],
            });
            m.closure_layouts.push(ClosureLayoutDescriptor {
                origin: None,
                closure: narrow_frame,
                size: 16,
                align: 8,
                capture_offsets: vec![8],
            });
            let ft = m
                .add_func_type(FuncTy {
                    abi: None,
                    params: vec![Ty::Closure(wide_id), Ty::Closure(narrow_id)],
                    returns: vec![Ty::Unit],
                    is_vararg: false,
                })
                .expect("Module::add_func_type: test fixture");
            let mut f = Function::new(FuncId::new(0), "main", ft, b(0));
            let mut blk = Block::new(b(0));
            blk.params.push((v(0), Ty::Closure(wide_id)));
            blk.params.push((v(1), Ty::Closure(narrow_id)));
            blk.body
                .push(InstrNode::new(Inst::Return { values: vec![] }));
            f.blocks.push(blk);
            m.try_add_function(f)
                .expect("Module::try_add_function: test fixture");
            assert!(m.validate_closure_layouts().is_ok());
            m
        }

        let base = module(false, false);
        // Renumbered closure types, every frame still on its own type: NO
        // change. (An index-keyed row would report `closure.0` and
        // `closure.1` as having swapped sizes.)
        let renumbered = module(true, false);
        let d = diff(&base, &renumbered);
        assert!(d.is_empty(), "{}", d.to_text());

        // The frames MOVED between the two closure types: a change, and it is
        // the closure-layout row that reports it.
        let moved = module(false, true);
        let d = diff(&base, &moved);
        assert!(
            d.module_meta_changes
                .iter()
                .any(|change| change.field == "closure_layouts"),
            "{}",
            d.to_text()
        );
        // Renumbered AND moved: still a change. (An index-keyed row would
        // read `closure.0 size=8` on both sides and call it no change.)
        let renumbered_and_moved = module(true, true);
        let d = diff(&base, &renumbered_and_moved);
        assert!(
            d.module_meta_changes
                .iter()
                .any(|change| change.field == "closure_layouts"),
            "{}",
            d.to_text()
        );
    }

    // 7. record id renumbering produces no diff ---------------------------

    #[test]
    fn record_id_renumbering_produces_no_diff() {
        let mut a = Module::new("m");
        let ra = a.add_record(RecordDef {
            id: RecordId::new(2),
            name: "R".into(),
            fields: vec![FieldDef {
                name: "a".into(),
                ty: Ty::I32,
                offset: None,
            }],
        });
        let ft = a
            .add_func_type(FuncTy {
                params: vec![Ty::Record(ra)],
                returns: vec![Ty::Unit],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut f = Function::new(FuncId::new(0), "main", ft, b(0));
        let mut blk = Block::new(b(0));
        blk.params.push((v(0), Ty::Record(ra)));
        blk.body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        f.blocks.push(blk);
        a.try_add_function(f)
            .expect("Module::try_add_function: test fixture");

        let mut b_mod = Module::new("m");
        let rb = b_mod.add_record(RecordDef {
            id: RecordId::new(99),
            name: "R".into(),
            fields: vec![FieldDef {
                name: "a".into(),
                ty: Ty::I32,
                offset: None,
            }],
        });
        let ft = b_mod
            .add_func_type(FuncTy {
                params: vec![Ty::Record(rb)],
                returns: vec![Ty::Unit],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut f = Function::new(FuncId::new(0), "main", ft, b(0));
        let mut blk = Block::new(b(0));
        blk.params.push((v(0), Ty::Record(rb)));
        blk.body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        f.blocks.push(blk);
        b_mod
            .try_add_function(f)
            .expect("Module::try_add_function: test fixture");

        let d = diff(&a, &b_mod);
        assert!(d.is_empty(), "{}", d.to_text());
    }

    // 8. block id renumbering produces no diff ----------------------------

    #[test]
    fn block_id_renumbering_produces_no_diff() {
        fn mk(name: &str, entry_id: u32, other_id: u32) -> Module {
            let mut m = Module::new(name);
            let ft = make_unit_ft(&mut m);
            let mut f = Function::new(FuncId::new(0), "main", ft, b(entry_id));
            // entry -> other -> return
            let mut entry = Block::new(b(entry_id));
            entry.body.push(InstrNode::new(Inst::Br {
                target: b(other_id),
                args: vec![],
            }));
            let mut other = Block::new(b(other_id));
            other
                .body
                .push(InstrNode::new(Inst::Return { values: vec![] }));
            f.blocks.push(entry);
            f.blocks.push(other);
            m.try_add_function(f)
                .expect("Module::try_add_function: test fixture");
            m
        }

        let a = mk("m", 0, 1);
        let b1 = mk("m", 50, 99);
        let d = diff(&a, &b1);
        assert!(d.is_empty(), "{}", d.to_text());
    }

    // 9. proof annotation with/without --ignore-proofs --------------------

    #[test]
    fn proof_added_without_flag_produces_diff() {
        let a = single_return_module("m", 0, 0);
        let mut b_mod = single_return_module("m", 0, 0);
        b_mod.functions[0].proofs.push(ProofAnnotation::Pure);

        let d = diff(&a, &b_mod);
        assert!(!d.is_empty(), "expected diff when proof differs");

        let d2 = diff_with(
            &a,
            &b_mod,
            DiffOptions {
                ignore_proofs: true,
                ..DiffOptions::default()
            },
        );
        assert!(d2.is_empty(), "{}", d2.to_text());
    }

    #[test]
    fn instruction_level_proof_added_without_flag_produces_diff() {
        let a = single_return_module("m", 0, 0);
        let mut b_mod = single_return_module("m", 0, 0);
        // Attach InBounds to the first instruction of the first block.
        b_mod.functions[0].blocks[0].body[0]
            .proofs
            .push(ProofAnnotation::InBounds);

        let d = diff(&a, &b_mod);
        assert!(!d.is_empty());
        match &d.changes[0] {
            FuncChange::Changed { block_changes, .. } => {
                assert!(!block_changes.is_empty());
            }
            other => panic!("expected Changed, got {other:?}"),
        }

        let d2 = diff_with(
            &a,
            &b_mod,
            DiffOptions {
                ignore_proofs: true,
                ..DiffOptions::default()
            },
        );
        assert!(d2.is_empty(), "{}", d2.to_text());
    }

    // 10. function added / removed are sorted -----------------------------

    #[test]
    fn function_added_and_removed_are_sorted() {
        // A has: aaa, bbb
        // B has: bbb, ccc
        // Expect: Removed("aaa") and Added("ccc") in sorted order.
        let mut a = Module::new("m");
        let ft = make_unit_ft(&mut a);
        for name in ["aaa", "bbb"] {
            let mut f = Function::new(FuncId::new(0), name, ft, b(0));
            let mut blk = Block::new(b(0));
            blk.body
                .push(InstrNode::new(Inst::Return { values: vec![] }));
            f.blocks.push(blk);
            a.try_add_function(f)
                .expect("Module::try_add_function: test fixture");
        }

        let mut b_mod = Module::new("m");
        let ft = make_unit_ft(&mut b_mod);
        for name in ["bbb", "ccc"] {
            let mut f = Function::new(FuncId::new(0), name, ft, b(0));
            let mut blk = Block::new(b(0));
            blk.body
                .push(InstrNode::new(Inst::Return { values: vec![] }));
            f.blocks.push(blk);
            b_mod
                .try_add_function(f)
                .expect("Module::try_add_function: test fixture");
        }

        let d = diff(&a, &b_mod);
        // Filter to names to check ordering.
        let names: Vec<&str> = d
            .changes
            .iter()
            .map(|c| match c {
                FuncChange::Added { name } => name.as_str(),
                FuncChange::Removed { name } => name.as_str(),
                FuncChange::Changed { name, .. } => name.as_str(),
            })
            .collect();
        assert_eq!(names, vec!["aaa", "ccc"]);
        // Confirm their kinds.
        assert!(matches!(&d.changes[0], FuncChange::Removed { .. }));
        assert!(matches!(&d.changes[1], FuncChange::Added { .. }));
    }

    // 11. block count mismatch reports block-level diff --------------------

    #[test]
    fn block_count_mismatch_reports_block_level_diff() {
        let mut a = Module::new("m");
        let ft = make_unit_ft(&mut a);
        let mut f = Function::new(FuncId::new(0), "main", ft, b(0));
        let mut blk = Block::new(b(0));
        blk.body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        f.blocks.push(blk);
        a.try_add_function(f)
            .expect("Module::try_add_function: test fixture");

        let mut b_mod = Module::new("m");
        let ft = make_unit_ft(&mut b_mod);
        let mut f = Function::new(FuncId::new(0), "main", ft, b(0));
        // Two blocks: entry branches to other, which returns.
        let mut entry = Block::new(b(0));
        entry.body.push(InstrNode::new(Inst::Br {
            target: b(1),
            args: vec![],
        }));
        let mut other = Block::new(b(1));
        other
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        f.blocks.push(entry);
        f.blocks.push(other);
        b_mod
            .try_add_function(f)
            .expect("Module::try_add_function: test fixture");

        let d = diff(&a, &b_mod);
        assert!(!d.is_empty());
        match &d.changes[0] {
            FuncChange::Changed { block_changes, .. } => {
                assert!(
                    block_changes
                        .iter()
                        .any(|bc| matches!(bc, BlockChange::Added { .. })),
                    "expected a BlockChange::Added for the extra block"
                );
            }
            other => panic!("expected Changed, got {other:?}"),
        }
    }

    // 12. different binop reports replaced ---------------------------------

    #[test]
    fn different_binop_reports_replaced() {
        let mk = |op: BinOp| -> Module {
            let mut m = Module::new("m");
            let ft = m
                .add_func_type(FuncTy {
                    params: vec![Ty::I32, Ty::I32],
                    returns: vec![Ty::I32],
                    abi: None,
                    is_vararg: false,
                })
                .expect("Module::add_func_type: test fixture");
            let mut f = Function::new(FuncId::new(0), "main", ft, b(0));
            let mut blk = Block::new(b(0));
            blk.params.push((v(0), Ty::I32));
            blk.params.push((v(1), Ty::I32));
            blk.body.push(
                InstrNode::new(Inst::BinOp {
                    op,
                    ty: Ty::I32,
                    lhs: v(0),
                    rhs: v(1),
                })
                .with_result(v(2)),
            );
            blk.body
                .push(InstrNode::new(Inst::Return { values: vec![v(2)] }));
            f.blocks.push(blk);
            m.try_add_function(f)
                .expect("Module::try_add_function: test fixture");
            m
        };

        let d = diff(&mk(BinOp::Add), &mk(BinOp::Sub));
        assert!(!d.is_empty());
        let mut found_replaced = false;
        if let FuncChange::Changed { block_changes, .. } = &d.changes[0] {
            for bc in block_changes {
                if let BlockChange::InstrDiff { instr_changes, .. } = bc {
                    for ic in instr_changes {
                        if let InstrChange::Replaced { .. } = ic {
                            found_replaced = true;
                        }
                    }
                }
            }
        }
        assert!(found_replaced, "expected Replaced for Add vs Sub");
    }

    // 13. icmp eq vs ne reports replaced -----------------------------------

    #[test]
    fn icmp_eq_vs_ne_reports_replaced() {
        use crate::inst::ICmpOp;
        let mk = |op: ICmpOp| -> Module {
            let mut m = Module::new("m");
            let ft = m
                .add_func_type(FuncTy {
                    params: vec![Ty::I32, Ty::I32],
                    returns: vec![Ty::Bool],
                    abi: None,
                    is_vararg: false,
                })
                .expect("Module::add_func_type: test fixture");
            let mut f = Function::new(FuncId::new(0), "main", ft, b(0));
            let mut blk = Block::new(b(0));
            blk.params.push((v(0), Ty::I32));
            blk.params.push((v(1), Ty::I32));
            blk.body.push(
                InstrNode::new(Inst::ICmp {
                    op,
                    ty: Ty::I32,
                    lhs: v(0),
                    rhs: v(1),
                })
                .with_result(v(2)),
            );
            blk.body
                .push(InstrNode::new(Inst::Return { values: vec![v(2)] }));
            f.blocks.push(blk);
            m.try_add_function(f)
                .expect("Module::try_add_function: test fixture");
            m
        };
        let d = diff(&mk(ICmpOp::Eq), &mk(ICmpOp::Ne));
        assert!(!d.is_empty());
    }

    // 14. fingerprint distinguishes primitive types ------------------------

    #[test]
    fn fp_primitive_types_distinct() {
        let m = Module::new("m");
        assert_ne!(fp_ty(&m, &Ty::I32), fp_ty(&m, &Ty::I64));
        assert_ne!(fp_ty(&m, &Ty::I32), fp_ty(&m, &Ty::U32));
        assert_ne!(fp_ty(&m, &Ty::F32), fp_ty(&m, &Ty::F64));
        assert_ne!(fp_ty(&m, &Ty::Ptr), fp_ty(&m, &Ty::Unit));
    }

    #[test]
    fn fp_vector_types_distinguish_lane_count_and_element_type() {
        let m = Module::new("m");
        let v4i32 = Ty::Vector(Box::new(Ty::I32), 4);
        let v8i32 = Ty::Vector(Box::new(Ty::I32), 8);
        let v4u32 = Ty::Vector(Box::new(Ty::U32), 4);

        assert_ne!(fp_ty(&m, &v4i32), fp_ty(&m, &v8i32));
        assert_ne!(fp_ty(&m, &v4i32), fp_ty(&m, &v4u32));
    }

    #[test]
    fn enum_fingerprint_binds_layout_but_not_field_names() {
        let build = |tag_offset, field_name: &str| {
            let mut module = Module::new("m");
            let mut def = EnumDef::new(
                EnumId::new(0),
                "E",
                vec![EnumVariant {
                    name: "V".into(),
                    fields: vec![Ty::I32],
                    field_names: vec![field_name.into()],
                }],
            );
            def.layout = Some(EnumLayoutDescriptor {
                encoding: EnumTagEncoding::Direct { tag_offset },
                size: 8,
                align: 4,
                variant_field_offsets: vec![vec![0]],
            });
            module.add_enum(def);
            module
        };
        let base = build(4, "left");
        let renamed = build(4, "right");
        let moved = build(0, "left");
        assert_eq!(
            fp_ty(&base, &Ty::Enum(EnumId::new(0))),
            fp_ty(&renamed, &Ty::Enum(EnumId::new(0)))
        );
        assert_ne!(
            fp_ty(&base, &Ty::Enum(EnumId::new(0))),
            fp_ty(&moved, &Ty::Enum(EnumId::new(0)))
        );
    }

    #[test]
    fn diff_reports_vector_lane_count_and_element_type_differences() {
        let vector_param_module = |ty: Ty| -> Module {
            let mut m = Module::new("m");
            let ft = m
                .add_func_type(FuncTy {
                    params: vec![ty.clone()],
                    returns: vec![],
                    abi: None,
                    is_vararg: false,
                })
                .expect("Module::add_func_type: test fixture");
            let mut f = Function::new(FuncId::new(0), "main", ft, b(0));
            let mut blk = Block::new(b(0));
            blk.params.push((v(0), ty));
            blk.body
                .push(InstrNode::new(Inst::Return { values: vec![] }));
            f.blocks.push(blk);
            m.try_add_function(f)
                .expect("Module::try_add_function: test fixture");
            m
        };

        let base = vector_param_module(Ty::Vector(Box::new(Ty::I32), 4));
        for (changed, expected) in [
            (
                vector_param_module(Ty::Vector(Box::new(Ty::I32), 8)),
                "vec<8xi32>",
            ),
            (
                vector_param_module(Ty::Vector(Box::new(Ty::U32), 4)),
                "vec<4xu32>",
            ),
        ] {
            let d = diff(&base, &changed);
            let text = d.to_text();
            assert!(!d.is_empty(), "{text}");
            assert!(text.contains("vec<4xi32>"), "{text}");
            assert!(text.contains(expected), "{text}");
        }
    }

    // 15. int vs float with same bits are distinct -------------------------

    #[test]
    fn fp_int_constant_distinct_from_float_with_same_bits() {
        let m = Module::new("m");
        let i = Constant::Int(0);
        let f = Constant::Float(0.0);
        assert_ne!(fp_constant(&m, &i), fp_constant(&m, &f));
    }

    // 16. SwitchCase reference is consumed (compile-time smoke)   ---------

    #[test]
    fn switch_case_type_is_used() {
        // Force the import path so a refactor that accidentally drops
        // `SwitchCase` from the imports breaks at compile time rather than
        // silently changing behavior.
        let _sc = SwitchCase {
            value: Constant::Int(0),
            target: b(0),
            args: vec![],
        };
    }

    // 17. to_text empty when no diff --------------------------------------

    #[test]
    fn to_text_empty_when_isomorphic() {
        let a = single_return_module("m", 0, 0);
        let d = diff(&a, &a);
        assert!(d.to_text().is_empty());
    }

    // 18. module proof-state diff: obligation status ----------------------

    #[test]
    fn obligation_status_change_is_reported_and_hidden_by_ignore_proofs() {
        use crate::proof::{ObligationKind, ProofStatus};

        let mk = |status: ProofStatus| -> Module {
            let mut m = single_return_module("m", 0, 0);
            m.proof_obligations.push(ProofObligation::new(
                ProofId::new(0),
                ObligationKind::Postcondition,
                status,
                "result is non-negative",
            ));
            m
        };

        let a = mk(ProofStatus::Pending);
        let b_mod = mk(ProofStatus::Discharged);

        let d = diff(&a, &b_mod);
        assert!(!d.is_empty(), "status change must surface");
        assert!(d.changes.is_empty(), "only proof state changed, not bodies");
        assert_eq!(d.proof_state_changes.len(), 1);
        match &d.proof_state_changes[0] {
            ProofStateChange::ObligationStatusChanged { before, after, .. } => {
                assert_eq!(before, "pending");
                assert_eq!(after, "discharged");
            }
            other => panic!("expected ObligationStatusChanged, got {other:?}"),
        }

        // --ignore-proofs hides it.
        let d2 = diff_with(
            &a,
            &b_mod,
            DiffOptions {
                ignore_proofs: true,
                ..DiffOptions::default()
            },
        );
        assert!(d2.is_empty(), "{}", d2.to_text());
    }

    // 19. obligation status diff is insensitive to ProofId renumbering -----

    #[test]
    fn obligation_match_ignores_proof_id_renumbering() {
        use crate::proof::{ObligationKind, ProofStatus};

        let mk = |id: u32| -> Module {
            let mut m = single_return_module("m", 0, 0);
            m.proof_obligations.push(ProofObligation::new(
                ProofId::new(id),
                ObligationKind::Precondition,
                ProofStatus::Discharged,
                "x > 0",
            ));
            m
        };

        // Same claim, same status, different arena id => no diff.
        let d = diff(&mk(0), &mk(42));
        assert!(d.is_empty(), "{}", d.to_text());
    }

    #[test]
    fn obligation_claim_fingerprint_binds_every_embedded_source_identity_field() {
        use crate::ProofDigest;
        use crate::proof::{
            ObligationKind, ProofObligationSourceIdentity, ProofObligationSourceRange, ProofStatus,
            PublicObligationIdentity,
        };

        let mut base = single_return_module("m", 0, 0);
        base.proof_obligations.push(
            ProofObligation::new(
                ProofId::new(0),
                ObligationKind::Precondition,
                ProofStatus::Pending,
                "x > 0",
            )
            .with_source(
                ProofObligationSourceIdentity::new("rust:crate::f", "assertion α")
                    .with_range(ProofObligationSourceRange {
                        file: 2,
                        start_line: 11,
                        start_col: 3,
                        end_line: 12,
                        end_col: 9,
                    })
                    .with_public(PublicObligationIdentity {
                        obligation_id: "vc:crate::f:0".to_string(),
                        semantic_digest: ProofDigest::sha256([7; 32]),
                    }),
            ),
        );
        let mutations: &[fn(&mut ProofObligationSourceIdentity)] = &[
            |source| source.source_id.push('!'),
            |source| source.assertion_id.push('!'),
            |source| source.range.as_mut().unwrap().file += 1,
            |source| source.range.as_mut().unwrap().start_line += 1,
            |source| source.range.as_mut().unwrap().start_col += 1,
            |source| source.range.as_mut().unwrap().end_line += 1,
            |source| source.range.as_mut().unwrap().end_col += 1,
            |source| source.public.as_mut().unwrap().obligation_id.push('!'),
            |source| source.public.as_mut().unwrap().semantic_digest.bytes[0] ^= 1,
        ];
        for mutate in mutations {
            let mut changed = base.clone();
            mutate(changed.proof_obligations[0].source.as_mut().unwrap());
            let result = diff(&base, &changed);
            assert_eq!(
                result.proof_state_changes.len(),
                2,
                "source mutation must remove the old claim and add the new claim: {}",
                result.to_text()
            );
            assert!(
                result
                    .proof_state_changes
                    .iter()
                    .any(|change| matches!(change, ProofStateChange::ObligationRemoved { .. }))
            );
            assert!(
                result
                    .proof_state_changes
                    .iter()
                    .any(|change| matches!(change, ProofStateChange::ObligationAdded { .. }))
            );
        }
    }

    // 20. missing certificate is reported ----------------------------------

    #[test]
    fn missing_certificate_is_reported() {
        use crate::proof::{ObligationKind, ProofStatus};

        let with_cert = |include: bool| -> Module {
            let mut m = single_return_module("m", 0, 0);
            m.proof_obligations.push(ProofObligation::new(
                ProofId::new(0),
                ObligationKind::MemorySafety,
                ProofStatus::Discharged,
                "no out-of-bounds access",
            ));
            if include {
                m.proof_certificates.push(ProofCertificate {
                    obligation: ProofId::new(0),
                    prover: "ay".into(),
                    evidence: ProofEvidence::SmtProof(vec![1, 2, 3]),

                    assurance: None,
                });
            }
            m
        };

        let a = with_cert(true);
        let b_mod = with_cert(false);

        let d = diff(&a, &b_mod);
        assert!(!d.is_empty());
        assert_eq!(d.proof_state_changes.len(), 1);
        assert!(matches!(
            &d.proof_state_changes[0],
            ProofStateChange::CertificateRemoved { .. }
        ));

        // The reverse direction reports it as added.
        let d_rev = diff(&b_mod, &a);
        assert!(matches!(
            &d_rev.proof_state_changes[0],
            ProofStateChange::CertificateAdded { .. }
        ));

        // --ignore-proofs hides the missing certificate.
        let d2 = diff_with(
            &a,
            &b_mod,
            DiffOptions {
                ignore_proofs: true,
                ..DiffOptions::default()
            },
        );
        assert!(d2.is_empty(), "{}", d2.to_text());
    }

    // 21. per-call proof_context difference is reported --------------------

    #[test]
    fn differing_proof_context_on_call_is_reported() {
        use crate::proof::{ObligationKind, ProofStatus};
        use crate::value::FuncTyId;

        // Build a module with a callee `g` and a caller `main` whose single
        // call node carries a `proof_context`. The two modules differ only in
        // which obligation the context `assumes`.
        let mk = |assume_id: u32| -> Module {
            let mut m = Module::new("m");
            m.add_func_type(FuncTy {
                params: vec![],
                returns: vec![Ty::Unit],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");

            // Two obligations so the context can reference either.
            m.proof_obligations.push(
                ProofObligation::new(
                    ProofId::new(0),
                    ObligationKind::Postcondition,
                    ProofStatus::Discharged,
                    "g returns even",
                )
                .with_function(FuncId::new(1)),
            );
            m.proof_obligations.push(
                ProofObligation::new(
                    ProofId::new(1),
                    ObligationKind::Postcondition,
                    ProofStatus::Discharged,
                    "g returns positive",
                )
                .with_function(FuncId::new(1)),
            );

            // Callee g (id 1).
            let mut g = Function::new(FuncId::new(1), "g", FuncTyId::new(0), b(0));
            let mut gblk = Block::new(b(0));
            gblk.body
                .push(InstrNode::new(Inst::Return { values: vec![] }));
            g.blocks.push(gblk);
            m.try_add_function(g)
                .expect("Module::try_add_function: test fixture");

            // Caller main (id 0) calls g with a proof_context.
            let mut f = Function::new(FuncId::new(0), "main", FuncTyId::new(0), b(0));
            let mut blk = Block::new(b(0));
            blk.body.push(
                InstrNode::new(Inst::Call {
                    callee: FuncId::new(1),
                    args: vec![],
                })
                .with_proof_context(ProofContext {
                    assumes: vec![ProofId::new(assume_id)],
                    establishes: vec![],
                }),
            );
            blk.body
                .push(InstrNode::new(Inst::Return { values: vec![] }));
            f.blocks.push(blk);
            m.try_add_function(f)
                .expect("Module::try_add_function: test fixture");
            m
        };

        // Context assumes obligation 0 vs obligation 1 — distinct claims.
        let a = mk(0);
        let b_mod = mk(1);

        let d = diff(&a, &b_mod);
        assert!(!d.is_empty(), "differing proof_context must surface");
        let mut found = false;
        for c in &d.changes {
            if let FuncChange::Changed {
                name,
                block_changes,
                ..
            } = c
                && name == "main"
            {
                for bc in block_changes {
                    if let BlockChange::InstrDiff { instr_changes, .. } = bc {
                        for ic in instr_changes {
                            if let InstrChange::Replaced { before, after, .. } = ic {
                                assert!(before.contains("ctx{"), "before: {before}");
                                assert!(after.contains("ctx{"), "after: {after}");
                                found = true;
                            }
                        }
                    }
                }
            }
        }
        assert!(found, "expected a Replaced call node citing proof context");

        // --ignore-proofs hides the proof_context difference.
        let d2 = diff_with(
            &a,
            &b_mod,
            DiffOptions {
                ignore_proofs: true,
                ..DiffOptions::default()
            },
        );
        assert!(d2.is_empty(), "{}", d2.to_text());
    }

    // 22. proof_context reference reordering alone is not a diff -----------

    #[test]
    fn proof_context_reference_order_is_insensitive() {
        use crate::proof::{ObligationKind, ProofStatus};
        use crate::value::FuncTyId;

        let mk = |assumes: Vec<u32>| -> Module {
            let mut m = Module::new("m");
            m.add_func_type(FuncTy {
                params: vec![],
                returns: vec![Ty::Unit],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
            for (i, desc) in ["a", "b"].iter().enumerate() {
                m.proof_obligations.push(ProofObligation::new(
                    ProofId::new(i as u32),
                    ObligationKind::Precondition,
                    ProofStatus::Discharged,
                    *desc,
                ));
            }
            let mut g = Function::new(FuncId::new(1), "g", FuncTyId::new(0), b(0));
            let mut gblk = Block::new(b(0));
            gblk.body
                .push(InstrNode::new(Inst::Return { values: vec![] }));
            g.blocks.push(gblk);
            m.try_add_function(g)
                .expect("Module::try_add_function: test fixture");

            let mut f = Function::new(FuncId::new(0), "main", FuncTyId::new(0), b(0));
            let mut blk = Block::new(b(0));
            blk.body.push(
                InstrNode::new(Inst::Call {
                    callee: FuncId::new(1),
                    args: vec![],
                })
                .with_proof_context(ProofContext {
                    assumes: assumes.into_iter().map(ProofId::new).collect(),
                    establishes: vec![],
                }),
            );
            blk.body
                .push(InstrNode::new(Inst::Return { values: vec![] }));
            f.blocks.push(blk);
            m.try_add_function(f)
                .expect("Module::try_add_function: test fixture");
            m
        };

        // Same reference set, different order => no diff.
        let d = diff(&mk(vec![0, 1]), &mk(vec![1, 0]));
        assert!(d.is_empty(), "{}", d.to_text());
    }

    // 23. proof-state JSON output round-trips ------------------------------

    #[test]
    fn proof_state_json_is_valid() {
        use crate::proof::{ObligationKind, ProofStatus};

        let mut a = single_return_module("m", 0, 0);
        a.proof_obligations.push(ProofObligation::new(
            ProofId::new(0),
            ObligationKind::Postcondition,
            ProofStatus::Pending,
            "p",
        ));
        let mut b_mod = single_return_module("m", 0, 0);
        b_mod.proof_obligations.push(ProofObligation::new(
            ProofId::new(0),
            ObligationKind::Postcondition,
            ProofStatus::Discharged,
            "p",
        ));

        let d = diff(&a, &b_mod);
        let j = d.to_json();
        let v: serde_json::Value = serde_json::from_str(&j).expect("to_json must emit valid JSON");
        let ps = v["proof_state"].as_array().expect("proof_state array");
        assert_eq!(ps.len(), 1);
        assert_eq!(ps[0]["kind"], "obligation_status_changed");
        assert_eq!(ps[0]["before"], "pending");
        assert_eq!(ps[0]["after"], "discharged");
    }

    /// The import-seam comparator (`trust_ir::imports::ty_structurally_eq_across`)
    /// and this file's type fingerprint must AGREE on every pair of resolvable
    /// types within one module: two types fingerprint equal iff the comparator
    /// says they are structurally equal. They are separate code because the
    /// fingerprint is not cycle-safe, so this is the guard that the second
    /// comparator did not quietly become a second opinion. Excluded by
    /// design: `Ty::Error` (fingerprints as "error", never equal at the seam)
    /// and dangling ids (fingerprint as `ty#N`, `false` at the seam).
    #[test]
    fn import_seam_comparator_agrees_with_fp_ty_over_fixture_types() {
        use crate::pred::Pred;
        use crate::ty::{ClosureTy, DialectTy, EnumTagRepr, FatPtrKind, SetRepr};

        let mut m = Module::new("agreement");
        let i64_ty = m.add_type(Ty::I64).expect("Module::add_type: test fixture");
        let bool_ty = m
            .add_type(Ty::Bool)
            .expect("Module::add_type: test fixture");
        let point = m.add_struct(StructDef {
            id: StructId::new(0),
            name: "Point".into(),
            fields: vec![
                FieldDef {
                    name: "x".into(),
                    ty: Ty::I64,
                    offset: Some(0),
                },
                FieldDef {
                    name: "y".into(),
                    ty: Ty::I64,
                    offset: Some(8),
                },
            ],
            size: Some(16),
            align: Some(8),
            repr: StructRepr::C,
            origin: None,
        });
        let point_rust = m.add_struct(StructDef {
            id: StructId::new(1),
            name: "Point".into(),
            fields: vec![
                FieldDef {
                    name: "x".into(),
                    ty: Ty::I64,
                    offset: Some(0),
                },
                FieldDef {
                    name: "y".into(),
                    ty: Ty::I64,
                    offset: Some(8),
                },
            ],
            size: Some(16),
            align: Some(8),
            repr: StructRepr::Rust,
            origin: None,
        });
        let point_again = m.add_struct(StructDef {
            id: StructId::new(2),
            name: "Point".into(),
            fields: vec![
                FieldDef {
                    name: "x".into(),
                    ty: Ty::I64,
                    offset: Some(0),
                },
                FieldDef {
                    name: "y".into(),
                    ty: Ty::I64,
                    offset: Some(8),
                },
            ],
            size: Some(16),
            align: Some(8),
            repr: StructRepr::C,
            origin: None,
        });
        let opt = m.add_enum(EnumDef::new(
            EnumId::new(0),
            "Opt",
            vec![
                EnumVariant {
                    name: "None".into(),
                    fields: vec![],
                    field_names: vec![],
                },
                EnumVariant {
                    name: "Some".into(),
                    fields: vec![Ty::I64],
                    field_names: vec![],
                },
            ],
        ));
        let opt_named = m.add_enum(EnumDef::new(
            EnumId::new(1),
            "Opt",
            vec![
                EnumVariant {
                    name: "None".into(),
                    fields: vec![],
                    field_names: vec![],
                },
                EnumVariant {
                    name: "Some".into(),
                    fields: vec![Ty::I64],
                    field_names: vec!["value".into()],
                },
            ],
        ));
        let opt_u32 = m.add_enum(
            EnumDef::new(
                EnumId::new(2),
                "Opt",
                vec![
                    EnumVariant {
                        name: "None".into(),
                        fields: vec![],
                        field_names: vec![],
                    },
                    EnumVariant {
                        name: "Some".into(),
                        fields: vec![Ty::I64],
                        field_names: vec![],
                    },
                ],
            )
            .with_repr(EnumTagRepr::U32),
        );
        let rec = m.add_record(RecordDef {
            id: RecordId::new(0),
            name: "R".into(),
            fields: vec![FieldDef {
                name: "k".into(),
                ty: Ty::Bool,
                offset: None,
            }],
        });
        let sig = m
            .add_func_type(FuncTy {
                params: vec![Ty::I64],
                returns: vec![Ty::Bool],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let sig_again = m
            .add_func_type(FuncTy {
                params: vec![Ty::I64],
                returns: vec![Ty::Bool],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let closure = m
            .add_closure_type(ClosureTy {
                func: sig,
                captures: vec![Ty::I64],
            })
            .expect("Module::add_closure_type: test fixture");
        let closure_again = m
            .add_closure_type(ClosureTy {
                func: sig_again,
                captures: vec![Ty::I64],
            })
            .expect("Module::add_closure_type: test fixture");
        let interval = m
            .intern_pred(Pred::Interval { lo: 0, hi: 10 })
            .expect("Module::intern_pred: test fixture")
            .unwrap();
        let nonzero = m
            .intern_pred(Pred::NonZero)
            .expect("Module::intern_pred: test fixture")
            .unwrap();

        let fixture: Vec<Ty> = vec![
            Ty::I8,
            Ty::I64,
            Ty::U64,
            Ty::Isize,
            Ty::Usize,
            Ty::Char,
            Ty::F32,
            Ty::Bool,
            Ty::Ptr,
            Ty::Unit,
            Ty::Never,
            Ty::Vector(Box::new(Ty::I32), 4),
            Ty::Vector(Box::new(Ty::I32), 8),
            Ty::FatPtr(FatPtrKind::Str),
            Ty::FatPtr(FatPtrKind::ContainerLen),
            Ty::FatPtr(FatPtrKind::ContainerVtable),
            Ty::FatPtr(FatPtrKind::TraitObject { trait_id: 1 }),
            Ty::FatPtr(FatPtrKind::TraitObject { trait_id: 2 }),
            Ty::FatPtr(FatPtrKind::Slice(i64_ty)),
            Ty::Struct(point),
            Ty::Struct(point_rust),
            Ty::Struct(point_again),
            Ty::Array(i64_ty, 3),
            Ty::Array(bool_ty, 3),
            Ty::Tuple(vec![Ty::I64, Ty::Bool]),
            Ty::Tuple(vec![Ty::Bool, Ty::I64]),
            Ty::Enum(opt),
            Ty::Enum(opt_named),
            Ty::Enum(opt_u32),
            Ty::Func(sig),
            Ty::Func(sig_again),
            Ty::Ref(Box::new(Ty::Struct(point))),
            Ty::RefMut(Box::new(Ty::Struct(point))),
            Ty::PtrConst(Box::new(Ty::I64)),
            Ty::PtrMut(Box::new(Ty::I64)),
            Ty::Rc(Box::new(Ty::I64)),
            Ty::Set(i64_ty, SetRepr::Bitset),
            Ty::Set(i64_ty, SetRepr::Boxed),
            Ty::Sequence(i64_ty),
            Ty::Record(rec),
            Ty::Closure(closure),
            Ty::Closure(closure_again),
            Ty::Refine(i64_ty, interval),
            Ty::Refine(i64_ty, nonzero),
            Ty::Dialect(Box::new(DialectTy::new("clean", "Nat", 1))),
            Ty::Dialect(Box::new(DialectTy::new("clean", "Nat", 2))),
        ];

        for a in &fixture {
            for b in &fixture {
                let by_fingerprint = fp_ty(&m, a) == fp_ty(&m, b);
                let at_the_seam = crate::imports::ty_structurally_eq_across(&m, a, &m, b);
                assert_eq!(
                    by_fingerprint, at_the_seam,
                    "fp_ty and ty_structurally_eq_across disagree on {a} vs {b}"
                );
            }
        }
    }
}
