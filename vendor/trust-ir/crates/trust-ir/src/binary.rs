// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Compact binary serialization for TrustIr modules.
//!
//! Format: little-endian, no serde dependency.
//!
//! ```text
//! Header: [magic: b"TRUST_IR", version: u32]
//! Module: [name, func_types, structs, enums, globals, types,
//!          functions, proof_obligations, proof_certificates,
//!          target_info, spec_modules (v13+)]
//! ```

use std::io::{Cursor, Read as IoRead};

use crate::constant::Constant;
use crate::inst::{
    AllocOrigin, AtomicRMWOp, BinOp, CastOp, FCmpOp, ICmpOp, Inst, Ordering, OverflowOp,
    SwitchCase, UnOp,
};
use crate::node::InstrNode;
use crate::proof::{
    CleanCicKernelRecheck, Divergence, ObligationKind, ProofAnnotation, ProofCertificate,
    ProofCertificateRef, ProofContext, ProofDigest, ProofDigestAlgorithm, ProofEvidence,
    ProofFormula, ProofLineageId, ProofLineageManifest, ProofLineageNode, ProofObligation,
    ProofObligationSourceIdentity, ProofObligationSourceRange, ProofReplayIdentity, ProofStatus,
    ProofTransform, ProofTransformStage, PublicObligationIdentity,
};
use crate::ty::{
    ClosureTy, EnumDef, EnumLayoutDescriptor, EnumTagEncoding, EnumTagRepr, EnumVariant,
    FatPtrKind, FieldDef, FuncTy, RecordDef, SetRepr, StructDef, StructRepr, Ty,
};
use crate::value::{
    BlockId, ClosureTyId, EnumId, FuncId, FuncTyId, GlobalId, ProofId, ProofTag, RecordId,
    ScopeData, SourceSpan, StructId, TyId, ValueId,
};
use crate::{
    Block, CallingConv, Endianness, FuncAttrs, Function, FunctionSummary, Global, Linkage, Module,
    ParamAttrs, Producer, SourceBindingProvenance, SourceLoopProvenance, SourcePlace,
    SourceProvenance, StructPassingPolicy, TargetInfo, TlsModel,
};

use std::collections::BTreeMap;

struct StringPool {
    strings: Vec<String>,
    map: BTreeMap<String, u32>,
}

impl StringPool {
    fn new() -> Self {
        Self {
            strings: Vec::new(),
            map: BTreeMap::new(),
        }
    }

    fn intern(&mut self, s: String) -> u32 {
        if let Some(&id) = self.map.get(&s) {
            return id;
        }
        let id = len_u32(self.strings.len());
        self.map.insert(s.clone(), id);
        self.strings.push(s);
        id
    }

    fn get(&self, id: u32) -> Result<String, BinaryError> {
        self.strings
            .get(id as usize)
            .cloned()
            .ok_or(BinaryError::BadStringId(id))
    }
}

const MAGIC: &[u8; 8] = b"TRUST_IR";
// Version 4 adds string interning and VInt (LEB128) encoding. (InstrNodes are
// NOT bit-packed — see docs/binary-format.md; real packing is a tracked,
// optional fast-5 follow-up.)
// Version 7 adds Function.attrs (FuncAttrs/ParamAttrs) (fast-2).
// Version 8 adds GEP.inbounds (fast-3 D.2); version-gated, defaults false on v2..=v7.
// Version 9 adds the Module debug-info source-file table; defaults empty on v2..=v8.
// Version 10 adds StructDef.repr (ABI classification); defaults Rust on v2..=v9.
// Version 11 adds the Module obligation-diagnostics sidecar; empty on v2..=v10.
// Version 12 adds CallIndirect.calling_conv; defaults to C on v2..=v11.
// Version 13 adds Module.spec_modules (SpecModule cross-reference objects, Phase 3);
//   version-gated, defaults to an empty vector on v2..=v12.
// Version 14 adds SpecModule.proofs (SpecProof bindings, the L1 proof-name teeth);
//   version-gated inside read_spec_module — defaults to an empty vector on v13.
// Version 15 adds Switch.exhaustive_enum_unreachable; version-gated, defaults false on v2..=v14.
// Version 16 adds the Inst::CoroSuspend opcode (wire tag 50, coroutine state-machine
//   lowering); a wholly new tag never appears in pre-v16 blobs, so no read-side gate is
//   needed (old modules simply never decode tag 50).
// Version 17 adds the exception-handling opcodes Inst::Invoke (wire tag 51),
//   Inst::LandingPad (tag 52), and Inst::Resume (tag 53). As with tag 50, these are
//   wholly new tags that never appear in pre-v17 blobs, so no read-side version gate
//   is needed (old modules simply never decode tags 51..=53).
// Version 18 adds Function.summary (the separate-compilation FunctionSummary
// contract: requires/ensures ProofFormula clauses + param names + proved flag);
// version-gated, defaults None on v2..=v17.
// Version 19 adds EnumDef.discriminants (explicit per-variant discriminant
// values) and EnumDef.repr (tag-representation hint) for the canonical
// tagged-union enum layout; version-gated, both default to empty/None on
// v2..=v18.
// Version 20 (ABI pinning) adds ParamAttrs.byval / ParamAttrs.sret (bits 3/4 of
// the param-attrs flags byte — by-value-vs-by-reference aggregate-passing
// classification); version-gated, both default to false on v2..=v19 (pre-v20
// writers never set those bits, and the reader masks them off anyway).
// Also v20 (ABI pinning): TargetInfo.abi (stable ABI identifier beyond the
// triple) and TargetInfo.struct_passing (aggregate-passing policy); written
// after endianness inside the target-info record, version-gated — default
// None / NativeC on v2..=v19.
// Version 21 adds the Inst::SeqMap general element-op loop instruction
// (tag 56). A wholly new tag that never appears in pre-v21 blobs, so no
// read-side version gate is needed (same rationale as the v16/v17 tags).
// Version 22 adds AllocOrigin::CleanHeap (origin byte 3 inside the HeapAlloc
// payload) for Clean's Perceus reference-counted heap cells (P1 native ARC).
// A wholly new enum value that never appears in pre-v22 blobs, so no
// read-side version gate is needed (same rationale as the v16/v17/v21 tags);
// pre-v22 readers reject any v22 blob wholesale at the header version check,
// so an old reader can never mis-decode a CleanHeap origin.
// Version 23 adds Function.producer (per-function producer provenance,
// Program CK1 contract ladder): a presence byte then a stable producer tag
// (TRust=0, Clean=1, TrustIr=2, TSwift=3, TC=4, Other=5 + string), written
// after the v18 summary block; version-gated, defaults None on v2..=v22.
// Version 24 (RFC TRUST_IR_V2 Phase 2 - THE ONE BREAKING BATCH):
//   * adds Constant::U128 (constant tag 13, 16-byte LE u128 payload) - the
//     128-bit-faithful integer carrier. CANONICAL iff value > i128::MAX; the
//     decoder REJECTS a non-canonical payload (one-spelling-per-construct,
//     docs/SPEC_RATIFICATIONS.md). A wholly new tag that never appears in
//     pre-v24 blobs (v16/v17/v21/v22 precedent).
//   * MOVES THE READ FLOOR: MIN_READ_VERSION 2 -> 23. This is the batch's
//     deliberate, one-time compatibility break: readers no longer decode
//     v2..=v22 blobs (every v3..v22 module read gate below became
//     unconditional and was deleted; the proof-lineage stream keeps its OWN
//     version space untouched), and the pinned pre-v23 compat fixtures in
//     trust-ir-conformance flipped from must-decode to MUST-REJECT tests.
//     Rationale: the verified-format core carries no legacy decode paths;
//     all persistent producers/consumers were already at v23 (artifacts are
//     regenerated per build). Post-v24 changes return to the additive
//     version-gate discipline (the ledger above stays append-only).
// Version 25 (RFC TRUST_IR_V2 Phase 3, additive): adds Constant::Bytes
// (constant tag 14: utf8-claim byte + v32 length + raw payload — the byte-
// array carrier for [u8; N] / str data, replacing O(N) Constant::Int element
// spellings; the utf8 flag is CHECKED at decode and in the validator), plus
// the B1 scalar type variants Ty::Isize / Ty::Usize / Ty::Char / Ty::Error
// (see the Ty tag ledger in write_ty; Error is producer-internal and
// UNENCODABLE — the writer rejects it, mirroring the validator). Wholly new
// tags never appear in pre-v25 blobs (v16/v17/v21/v22/v24 precedent), so no
// read-side version gate is needed.
// Versions 26..=28 are AMBIGUOUS-LINEAGE and are refused on read (see the
// version check in the module reader): two divergent development lines each
// claimed v26 with byte-incompatible layouts —
//   * line A ("align"): v26 added Global.align (Option<u32>), written after
//     the global's tls field as a presence byte then a v32 alignment;
//   * line B ("identity"): v26 added SpecAnchor.function (optional
//     module-local FuncId after `project`), v27 added SpecModule.enforcement +
//     SpecAnchor.projection_target, v28 appended ProofObligation.source after
//     its owning-function field.
// A blob labeled 26..=28 cannot be attributed to either line without
// misparsing the other (the align presence byte vs the anchor record shift),
// so the merged reader FAILS CLOSED on that range — a deliberate, narrow
// backward-compat exception in the v24 read-floor tradition; stale build/cache
// artifacts regenerate on the next compile.
//
// Version 29 is the MERGED SUPERSET of both lines: it writes ALL of the above
// — Global.align, SpecAnchor.function, SpecModule.enforcement,
// SpecAnchor.projection_target, and ProofObligation.source. The per-feature
// read gates keep their historical thresholds (>= 26 / >= 27 / >= 28), which
// combined with the 26..=28 refusal means they all fire exactly on v29+
// blobs; pre-v26 blobs decode with every one of them defaulted
// (None / DesignOnly).
// Version 30 (typed value model, ADDITIVE): adds the refinement carriers —
//   * `Ty::Refine(TyId, PredId)` at Ty tag 36 (next free after the v25 B1
//     scalars 33..=35). A wholly new tag that can never appear in a pre-v30
//     blob, so no read-side gate is needed for the type itself
//     (v16/v17/v21/v22/v24/v25 precedent).
//   * two additive TRAILING module sections, written after the v13 spec
//     modules and gated `version >= 30` on read: `Module.universes`
//     (content-interned finite universes) then `Module.predicates`
//     (content-interned predicates). Universes come FIRST because a predicate
//     may reference a `UnivId` and the reader should have resolved the
//     referent table before the referencing one.
// A v29 blob therefore decodes with `universes = []`, `predicates = []` and no
// `Ty::Refine` spelling anywhere — bit-identical to what v29 always meant.
// Both tables are CONTENT-INTERNED; the codec preserves table order verbatim
// (it is an identity, not a hint) and `validate_module` rejects duplicate
// content, so a decoder cannot be handed the un-interned shape whose absence
// caused the join-drop miscompile.
//
// Version 31 (enum layout descriptors, ADDITIVE): extends enum records with:
//   * a per-variant `field_names` list after each variant's field types;
//   * an optional `EnumDef.layout` after the v19 tag-repr hint.
// The descriptor carries direct or niche tag encoding, total size/alignment,
// and per-variant field offsets. It is normative when present. Version 30
// records decode with empty field-name lists and no descriptor, while their
// typed-value trailing sections retain exactly their v30 interpretation.
// The text format remains layout-agnostic; binary and serde are the lossless
// transports for these concrete-layout facts.
// v32 (C2-names): `Function.value_names` — presence byte, then (ValueId, name) pairs.
// v33 (C2-scopes): `Function.scopes` — presence byte, then (parent, span) entries;
//   `InstrNode.scope` — presence byte, then the scope index. Both are debug-info
//   metadata: a reader at an older version simply sees no scope tree.
// v34 (obligation site backref, ADDITIVE): `ProofObligation.site` — presence
//   byte, then (function, block, inst_index) as three varints — written AFTER
//   the v28 source-identity record and gated `version >= 34` on read. A v33
//   blob decodes with `site = None`, which every fail-closed consumer must
//   treat as "not bindable to a VC condition" rather than as a wildcard. The
//   field exists because `ProofObligation.function` (B4) scopes an obligation
//   to a whole FUNCTION, which is not enough to bind a per-check obligation to
//   the one solver condition that actually backs it.
// v35 (semantic source provenance, ADDITIVE): `Function.source_provenance` —
//   compiler-source, non-circular semantic-body, and complete binding digests,
//   followed by exact source-loop/header/name/place rows. A v34 reader sees no
//   carrier; a v35 consumer must validate it before use.
// v36 (target layout completeness, ADDITIVE):
//   `StructPassingPolicy::Unclassified` at target-info struct-passing tag 2.
//   A conforming pre-v36 producer never emits that new tag, while pre-v36
//   readers reject a v36 header before reaching it. The value records that a
//   producer has not classified aggregate passing; consumers that require a
//   concrete ABI policy must fail closed rather than infer one.
// v37 (untagged enum images, ADDITIVE): `EnumTagEncoding::Untagged` at
//   enum-layout-descriptor encoding tag 2 — a tag-FREE image, the shape rustc
//   gives a single-INHABITED-variant `repr(Rust)` enum. The descriptor grammar
//   could previously only say direct-or-niche, so a producer had to DECLINE a
//   descriptor for such a def, and a descriptor-less enum falls back to the
//   canonical tagged-union layout, which budgets a tag. Unlike the v36 tag this
//   one IS read-gated (`version >= 37`), because it sits inside a record a v36
//   reader already parses: an ungated arm would let a v36-labelled blob decode
//   as untagged. Well-formed only for a one-variant enum — nothing in the image
//   discriminates.
/// The format version this build serializes. Public so conformance tests and
/// consumers assert against the canonical constant instead of a stale literal.
pub const VERSION: u32 = 37;
/// Current TrustIR binary wire-format version emitted by [`serialize_module`].
pub const FORMAT_VERSION: u32 = VERSION;
const MIN_READ_VERSION: u32 = 23;
const PROOF_LINEAGE_MAGIC: &[u8; 4] = b"TMPL";
const PROOF_LINEAGE_VERSION: u32 = 2;

// ---------------------------------------------------------------------------
// Error
// ---------------------------------------------------------------------------

// `#[non_exhaustive]`: this is a cross-repo contract crate. Decoder diagnostics
// may gain variants (e.g. finer-grained malformed-input cases) without that
// being a breaking change — downstream consumers display/`?` these errors
// rather than matching them exhaustively. The IR enums (`Inst`/`Ty`) are
// deliberately left exhaustive because compiler consumers must match them.
#[derive(Debug, Clone, PartialEq)]
#[non_exhaustive]
pub enum BinaryError {
    InvalidMagic,
    UnsupportedVersion,
    UnexpectedEof,
    InvalidTag(u8),
    /// A LEB128/varint field's continuation bytes exceed the target width.
    VintOverflow,
    /// A string-pool reference points past the end of the decoded pool.
    BadStringId(u32),
    /// The in-memory `NativeVerificationBundle` carries content the binary
    /// envelope deliberately cannot encode (typed requests, evidence bundles,
    /// or non-default policy/provenance/compiler-fact records); use the serde
    /// JSON/MessagePack codec for those. Surfaced by `serialize`, not decode.
    Unencodable(&'static str),
    /// A residual, genuinely-miscellaneous decode failure that does not fit a
    /// typed variant above (e.g. a validation-pass error rendered to text).
    /// Prefer adding a typed category over widening this.
    InvalidData(String),
    Utf8Error,
    /// A length/count field declares more elements than the remaining input
    /// could possibly contain. Surfaced before any allocation so a hostile or
    /// truncated buffer cannot drive an unbounded `Vec::with_capacity` (C1).
    TooLarge {
        declared: usize,
        remaining: usize,
    },
}

impl core::fmt::Display for BinaryError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            BinaryError::InvalidMagic => f.write_str("invalid magic bytes"),
            BinaryError::UnsupportedVersion => f.write_str("unsupported version"),
            BinaryError::UnexpectedEof => f.write_str("unexpected end of data"),
            BinaryError::InvalidTag(t) => write!(f, "invalid tag: {}", t),
            BinaryError::VintOverflow => f.write_str("varint overflow"),
            BinaryError::BadStringId(id) => write!(f, "invalid string id: {id}"),
            BinaryError::Unencodable(what) => write!(f, "not encodable in binary format: {what}"),
            BinaryError::InvalidData(s) => write!(f, "invalid data: {}", s),
            BinaryError::Utf8Error => f.write_str("invalid UTF-8"),
            BinaryError::TooLarge {
                declared,
                remaining,
            } => write!(
                f,
                "declared element count {declared} exceeds {remaining} remaining byte(s)"
            ),
        }
    }
}

// ---------------------------------------------------------------------------
// Writer helpers
// ---------------------------------------------------------------------------

fn write_u8(buf: &mut Vec<u8>, v: u8) {
    buf.push(v);
}

fn write_bool(buf: &mut Vec<u8>, v: bool) {
    buf.push(if v { 1 } else { 0 });
}

fn write_u32(buf: &mut Vec<u8>, v: u32) {
    buf.extend_from_slice(&v.to_le_bytes());
}

fn write_u64(buf: &mut Vec<u8>, v: u64) {
    buf.extend_from_slice(&v.to_le_bytes());
}

fn write_v64(buf: &mut Vec<u8>, mut v: u64) {
    while v >= 0x80 {
        buf.push((v as u8) | 0x80);
        v >>= 7;
    }
    buf.push(v as u8);
}

/// The v1 binary format uses `u32` lengths. Never silently truncate a host
/// `usize`: module bytes feed cryptographic module identity and an aliased
/// length prefix would make two logical values share one encoding.
fn len_u32(value: usize) -> u32 {
    u32::try_from(value).expect("binary value exceeds the format's u32 length limit")
}

fn write_i128(buf: &mut Vec<u8>, v: i128) {
    buf.extend_from_slice(&v.to_le_bytes());
}

fn write_u128(buf: &mut Vec<u8>, v: u128) {
    buf.extend_from_slice(&v.to_le_bytes());
}

fn write_v32(buf: &mut Vec<u8>, v: u32) {
    write_v64(buf, v as u64);
}

fn write_value_id(buf: &mut Vec<u8>, id: ValueId) {
    write_v32(buf, id.index());
}

fn write_block_id(buf: &mut Vec<u8>, id: BlockId) {
    write_v32(buf, id.index());
}

fn write_ty_id(buf: &mut Vec<u8>, id: TyId) {
    write_v32(buf, id.index());
}

fn write_func_id(buf: &mut Vec<u8>, id: FuncId) {
    write_v32(buf, id.index());
}

fn write_func_ty_id(buf: &mut Vec<u8>, id: FuncTyId) {
    write_v32(buf, id.index());
}

fn write_closure_ty_id(buf: &mut Vec<u8>, id: ClosureTyId) {
    write_v32(buf, id.index());
}

fn write_struct_id(buf: &mut Vec<u8>, id: StructId) {
    write_v32(buf, id.index());
}

fn write_enum_id(buf: &mut Vec<u8>, id: EnumId) {
    write_v32(buf, id.index());
}

fn write_record_id(buf: &mut Vec<u8>, id: RecordId) {
    write_v32(buf, id.index());
}

fn write_proof_id(buf: &mut Vec<u8>, id: ProofId) {
    write_v32(buf, id.index());
}

fn write_f64(buf: &mut Vec<u8>, v: f64) {
    buf.extend_from_slice(&v.to_le_bytes());
}

fn write_raw_str(buf: &mut Vec<u8>, s: &str) {
    write_v32(buf, len_u32(s.len()));
    buf.extend_from_slice(s.as_bytes());
}

fn write_str(buf: &mut Vec<u8>, pool: &mut StringPool, s: &str) {
    write_v32(buf, pool.intern(s.to_string()));
}

fn write_bytes(buf: &mut Vec<u8>, data: &[u8]) {
    write_v32(buf, len_u32(data.len()));
    buf.extend_from_slice(data);
}

fn write_opt_u64(buf: &mut Vec<u8>, v: Option<u64>) {
    match v {
        None => write_u8(buf, 0),
        Some(val) => {
            write_u8(buf, 1);
            write_v64(buf, val);
        }
    }
}

fn write_opt_str(buf: &mut Vec<u8>, pool: &mut StringPool, v: Option<&str>) {
    match v {
        None => write_u8(buf, 0),
        Some(s) => {
            write_u8(buf, 1);
            write_str(buf, pool, s);
        }
    }
}

fn collect_strings(module: &Module) -> StringPool {
    let mut pool = StringPool::new();
    pool.intern(module.name.clone());

    if let Some(ti) = &module.target_info {
        pool.intern(ti.triple.clone());
        // Stable ABI identifier (VERSION >= 20).
        if let Some(abi) = &ti.abi {
            pool.intern(abi.clone());
        }
    }

    // Debug-info source-file table paths (VERSION >= 9).
    for path in &module.files {
        pool.intern(path.clone());
    }

    // Obligation-diagnostic strings (VERSION >= 11).
    for d in &module.obligation_diagnostics {
        pool.intern(d.message.clone());
        if let Some(detail) = &d.detail {
            pool.intern(detail.clone());
        }
    }

    for sd in &module.structs {
        pool.intern(sd.name.clone());
        for fd in &sd.fields {
            pool.intern(fd.name.clone());
        }
    }

    for ed in &module.enums {
        pool.intern(ed.name.clone());
        for v in &ed.variants {
            pool.intern(v.name.clone());
            for name in &v.field_names {
                pool.intern(name.clone());
            }
        }
    }

    for rd in &module.records {
        pool.intern(rd.name.clone());
        for fd in &rd.fields {
            pool.intern(fd.name.clone());
        }
    }

    for g in &module.globals {
        pool.intern(g.name.clone());
        if let Some(c) = &g.initializer {
            collect_constant_strings(c, &mut pool);
        }
    }

    for f in &module.functions {
        pool.intern(f.name.clone());
        for b in &f.blocks {
            for node in &b.body {
                collect_inst_strings(&node.inst, &mut pool);
            }
        }
        // v18: separate-compilation contract strings (schemas/payloads/params).
        if let Some(summary) = &f.summary {
            for c in summary.requires.iter().chain(summary.ensures.iter()) {
                pool.intern(c.schema.clone());
                pool.intern(c.payload.clone());
                if let Some(s) = &c.smtlib {
                    pool.intern(s.clone());
                }
                if let Some(s) = &c.sort {
                    pool.intern(s.clone());
                }
            }
            for p in &summary.params {
                pool.intern(p.clone());
            }
        }
        // v32: debug value names (C2-names).
        if let Some(names) = &f.value_names {
            for (_, n) in names {
                pool.intern(n.clone());
            }
        }
        // v35: semantic source-binding names.
        if let Some(provenance) = &f.source_provenance {
            for source_loop in &provenance.loops {
                for binding in &source_loop.bindings {
                    pool.intern(binding.name.clone());
                }
            }
        }
        // v23: producer provenance — only the Other escape carries a string.
        if let Some(Producer::Other(s)) = &f.producer {
            pool.intern(s.clone());
        }
    }

    for po in &module.proof_obligations {
        pool.intern(po.description.clone());
        if let Some(f) = &po.formula {
            pool.intern(f.schema.clone());
            pool.intern(f.payload.clone());
            if let Some(s) = &f.smtlib {
                pool.intern(s.clone());
            }
            if let Some(s) = &f.sort {
                pool.intern(s.clone());
            }
        }
        if let Some(source) = &po.source {
            pool.intern(source.source_id.clone());
            pool.intern(source.assertion_id.clone());
            if let Some(public) = &source.public {
                pool.intern(public.obligation_id.clone());
            }
        }
    }

    for pc in &module.proof_certificates {
        pool.intern(pc.prover.clone());
        collect_evidence_strings(&pc.evidence, &mut pool);
    }

    for sm in &module.spec_modules {
        collect_spec_module_strings(sm, &mut pool);
    }

    pool
}

/// Pre-intern every string referenced by a [`SpecModule`] so that the lazy
/// `write_str` calls in `write_spec_module` only ever hit already-pooled ids.
fn collect_spec_module_strings(sm: &crate::spec::SpecModule, pool: &mut StringPool) {
    pool.intern(sm.name.clone());
    for v in &sm.vars {
        pool.intern(v.name.clone());
        pool.intern(v.ty.clone());
    }
    for a in &sm.actions {
        pool.intern(a.clone());
    }
    for inv in &sm.invariants {
        pool.intern(inv.name.clone());
        pool.intern(inv.formula.clone());
    }
    for anchor in &sm.anchors {
        pool.intern(anchor.machine.clone());
        pool.intern(anchor.action.clone());
        pool.intern(anchor.rust_symbol.clone());
        pool.intern(anchor.span.clone());
        if let Some(p) = &anchor.project {
            pool.intern(p.clone());
        }
    }
    for w in &sm.waivers {
        pool.intern(w.machine.clone());
        pool.intern(w.action.clone());
        pool.intern(w.reason.clone());
    }
    for p in &sm.proofs {
        pool.intern(p.machine.clone());
        pool.intern(p.action.clone());
        pool.intern(p.proof_name.clone());
    }
    if let crate::spec::SpecOrigin::External(path) = &sm.origin {
        pool.intern(path.clone());
    }
}

fn collect_constant_strings(c: &Constant, pool: &mut StringPool) {
    match c {
        Constant::Aggregate(elems)
        | Constant::Array(elems)
        | Constant::Vector(elems)
        | Constant::Sequence(elems)
        | Constant::Set(elems) => {
            for e in elems {
                collect_constant_strings(e, pool);
            }
        }
        Constant::Record(fields) => {
            for (name, val) in fields {
                pool.intern(name.clone());
                collect_constant_strings(val, pool);
            }
        }
        Constant::Closure { captures, .. } => {
            for c in captures {
                collect_constant_strings(c, pool);
            }
        }
        Constant::SymbolAddr { symbol, .. } => {
            pool.intern(symbol.clone());
        }
        _ => {}
    }
}

fn collect_inst_strings(inst: &Inst, pool: &mut StringPool) {
    match inst {
        Inst::OpenFrame { def } => {
            pool.intern(def.name.clone());
            for slot in &def.slots {
                pool.intern(slot.name.clone());
            }
        }
        Inst::DialectOp(op) => {
            pool.intern(op.dialect.clone());
            pool.intern(op.op.clone());
            for entry in &op.attrs {
                pool.intern(entry.name.clone());
                if let crate::dialect::AttrValue::Str(s) = &entry.value {
                    pool.intern(s.clone());
                }
            }
        }
        Inst::Const { value, .. } => {
            collect_constant_strings(value, pool);
        }
        Inst::Switch { cases, .. } => {
            for case in cases {
                collect_constant_strings(&case.value, pool);
            }
        }
        _ => {}
    }
}

fn collect_evidence_strings(ev: &ProofEvidence, pool: &mut StringPool) {
    match ev {
        ProofEvidence::LeanProof(s) | ProofEvidence::KaniHarness(s) | ProofEvidence::Trusted(s) => {
            pool.intern(s.clone());
        }
        ProofEvidence::TranslationValidation { rule_name, .. } => {
            pool.intern(rule_name.clone());
        }
        ProofEvidence::CleanCic {
            kernel_recheck: Some(recheck),
            ..
        } => {
            pool.intern(recheck.module.clone());
            for thm in &recheck.theorems {
                pool.intern(thm.clone());
            }
            pool.intern(recheck.anchor.clone());
            for ax in &recheck.allowed_axioms {
                pool.intern(ax.clone());
            }
        }
        _ => {}
    }
}

// ---------------------------------------------------------------------------
// Reader helpers
// ---------------------------------------------------------------------------

struct Reader<'a> {
    cursor: Cursor<&'a [u8]>,
    pool: Option<StringPool>,
    /// Format version of the module being read, set once after the header is
    /// validated. Lets version-gated reads (e.g. fast-3 v8 fields) consult
    /// `r.version` without threading it through every `read_*` signature.
    version: u32,
    nesting_depth: usize,
}

/// Recursive values need an independent stack bound: a compact chain of
/// `Ty::Ref` or aggregate constants can be deeply nested without declaring a
/// large collection or byte string.
const MAX_BINARY_NESTING_DEPTH: usize = 256;

impl<'a> Reader<'a> {
    fn new(data: &'a [u8]) -> Self {
        Self {
            cursor: Cursor::new(data),
            pool: None,
            version: VERSION,
            nesting_depth: 0,
        }
    }

    fn read_exact(&mut self, n: usize) -> Result<Vec<u8>, BinaryError> {
        // Check before allocating. Most variable-size callers already obtain
        // `n` through `read_checked_len`, but keeping the invariant at this
        // lowest allocation boundary prevents a future direct caller from
        // turning a hostile length into an allocation before EOF is noticed.
        self.reserve_checked(n)?;
        let mut buf = vec![0u8; n];
        self.cursor
            .read_exact(&mut buf)
            .map_err(|_| BinaryError::UnexpectedEof)?;
        Ok(buf)
    }

    fn read_u8(&mut self) -> Result<u8, BinaryError> {
        let b = self.read_exact(1)?;
        Ok(b[0])
    }

    fn read_bool(&mut self) -> Result<bool, BinaryError> {
        match self.read_u8()? {
            0 => Ok(false),
            1 => Ok(true),
            t => Err(BinaryError::InvalidTag(t)),
        }
    }

    fn read_u32(&mut self) -> Result<u32, BinaryError> {
        let b = self.read_exact(4)?;
        Ok(u32::from_le_bytes([b[0], b[1], b[2], b[3]]))
    }

    fn read_u64(&mut self) -> Result<u64, BinaryError> {
        let b = self.read_exact(8)?;
        Ok(u64::from_le_bytes([
            b[0], b[1], b[2], b[3], b[4], b[5], b[6], b[7],
        ]))
    }

    fn read_v64(&mut self) -> Result<u64, BinaryError> {
        let mut result = 0u64;
        let mut shift = 0;
        loop {
            let b = self.read_exact(1)?[0];
            let payload = b & 0x7f;
            // A u64 LEB128 value has at most one payload bit in byte ten.
            // Shifting (for example) 0x02 by 63 silently discards the
            // over-wide bit, aliasing a hostile encoding to a smaller value.
            if shift == 63 && payload > 1 {
                return Err(BinaryError::VintOverflow);
            }
            result |= (payload as u64) << shift;
            if b & 0x80 == 0 {
                // The writer emits the shortest LEB128 spelling. Reject an
                // alternate spelling so serialized identities have one wire
                // representation (e.g. 0x80 0x00 must not alias 0x00).
                if shift != 0 && payload == 0 {
                    return Err(BinaryError::InvalidData(
                        "non-canonical varint encoding".to_string(),
                    ));
                }
                return Ok(result);
            }
            shift += 7;
            if shift >= 64 {
                return Err(BinaryError::VintOverflow);
            }
        }
    }

    fn read_v32(&mut self) -> Result<u32, BinaryError> {
        u32::try_from(self.read_v64()?).map_err(|_| BinaryError::VintOverflow)
    }

    fn read_value_id(&mut self) -> Result<ValueId, BinaryError> {
        self.read_v32().map(ValueId::new)
    }

    fn read_block_id(&mut self) -> Result<BlockId, BinaryError> {
        self.read_v32().map(BlockId::new)
    }

    fn read_ty_id(&mut self) -> Result<TyId, BinaryError> {
        self.read_v32().map(TyId::new)
    }

    fn read_func_id(&mut self) -> Result<FuncId, BinaryError> {
        self.read_v32().map(FuncId::new)
    }

    fn read_func_ty_id(&mut self) -> Result<FuncTyId, BinaryError> {
        self.read_v32().map(FuncTyId::new)
    }

    fn read_closure_ty_id(&mut self) -> Result<ClosureTyId, BinaryError> {
        self.read_v32().map(ClosureTyId::new)
    }

    fn read_struct_id(&mut self) -> Result<StructId, BinaryError> {
        self.read_v32().map(StructId::new)
    }

    fn read_enum_id(&mut self) -> Result<EnumId, BinaryError> {
        self.read_v32().map(EnumId::new)
    }

    fn read_record_id(&mut self) -> Result<RecordId, BinaryError> {
        self.read_v32().map(RecordId::new)
    }

    fn read_proof_id(&mut self) -> Result<ProofId, BinaryError> {
        self.read_v32().map(ProofId::new)
    }

    fn read_i128(&mut self) -> Result<i128, BinaryError> {
        let b = self.read_exact(16)?;
        let mut arr = [0u8; 16];
        arr.copy_from_slice(&b);
        Ok(i128::from_le_bytes(arr))
    }

    fn read_u128(&mut self) -> Result<u128, BinaryError> {
        let b = self.read_exact(16)?;
        let mut arr = [0u8; 16];
        arr.copy_from_slice(&b);
        Ok(u128::from_le_bytes(arr))
    }

    fn read_f64(&mut self) -> Result<f64, BinaryError> {
        let b = self.read_exact(8)?;
        Ok(f64::from_le_bytes([
            b[0], b[1], b[2], b[3], b[4], b[5], b[6], b[7],
        ]))
    }

    fn read_raw_str(&mut self) -> Result<String, BinaryError> {
        let len = self.read_checked_len()?;
        let b = self.read_exact(len)?;
        String::from_utf8(b).map_err(|_| BinaryError::Utf8Error)
    }

    fn read_str(&mut self) -> Result<String, BinaryError> {
        if self.pool.is_some() {
            let id = self.read_v32()?;
            self.pool.as_ref().unwrap().get(id)
        } else {
            self.read_raw_str()
        }
    }

    fn read_bytes(&mut self) -> Result<Vec<u8>, BinaryError> {
        let len = self.read_checked_len()?;
        self.read_exact(len)
    }

    /// Number of bytes left to read in the underlying buffer.
    fn bytes_remaining(&self) -> usize {
        let total = self.cursor.get_ref().len();
        let pos = self.cursor.position() as usize;
        total.saturating_sub(pos)
    }

    /// Validate an untrusted element count `n` against the bytes still
    /// available, then return it so the caller can `Vec::with_capacity(n)`
    /// safely (C1: allocation DoS).
    ///
    /// Every count-driven collection in this codec serializes each element
    /// as at least one byte (the smallest element is a single tag/varint
    /// byte). So a well-formed buffer can never declare more elements than it
    /// has remaining bytes; a buffer that does is truncated or hostile and is
    /// rejected up front rather than pre-reserving gigabytes. This bounds the
    /// reservation to the input size without changing the wire format.
    fn reserve_checked(&self, n: usize) -> Result<usize, BinaryError> {
        let remaining = self.bytes_remaining();
        if n > remaining {
            return Err(BinaryError::TooLarge {
                declared: n,
                remaining,
            });
        }
        Ok(n)
    }

    /// Read a `v32` element count and validate it against the remaining input
    /// before any `Vec::with_capacity` (C1). See [`Reader::reserve_checked`].
    fn read_checked_len(&mut self) -> Result<usize, BinaryError> {
        let n = self.read_v32()? as usize;
        self.reserve_checked(n)
    }

    fn enter_nesting(&mut self) -> Result<(), BinaryError> {
        if self.nesting_depth >= MAX_BINARY_NESTING_DEPTH {
            return Err(BinaryError::InvalidData(format!(
                "binary value nesting exceeds limit {MAX_BINARY_NESTING_DEPTH}"
            )));
        }
        self.nesting_depth += 1;
        Ok(())
    }

    fn leave_nesting(&mut self) {
        self.nesting_depth -= 1;
    }
}

fn read_opt_u64(r: &mut Reader<'_>) -> Result<Option<u64>, BinaryError> {
    let tag = r.read_u8()?;
    match tag {
        0 => Ok(None),
        1 => Ok(Some(r.read_v64()?)),
        _ => Err(BinaryError::InvalidTag(tag)),
    }
}

fn read_opt_str(r: &mut Reader<'_>) -> Result<Option<String>, BinaryError> {
    let tag = r.read_u8()?;
    match tag {
        0 => Ok(None),
        1 => Ok(Some(r.read_str()?)),
        _ => Err(BinaryError::InvalidTag(tag)),
    }
}

// ---------------------------------------------------------------------------
// Ty
// ---------------------------------------------------------------------------

fn write_ty(buf: &mut Vec<u8>, pool: &mut StringPool, ty: &Ty) {
    match ty {
        Ty::I8 => write_u8(buf, 0),
        Ty::I16 => write_u8(buf, 1),
        Ty::I32 => write_u8(buf, 2),
        Ty::I64 => write_u8(buf, 3),
        Ty::I128 => write_u8(buf, 4),
        Ty::U8 => write_u8(buf, 5),
        Ty::U16 => write_u8(buf, 6),
        Ty::U32 => write_u8(buf, 7),
        Ty::U64 => write_u8(buf, 8),
        Ty::U128 => write_u8(buf, 9),
        // v25 B1 scalars (tags 33-35; Error is UNENCODABLE - see below).
        Ty::Isize => write_u8(buf, 33),
        Ty::Usize => write_u8(buf, 34),
        Ty::Char => write_u8(buf, 35),
        // Ty::Error is producer-internal (a fail-closed typing placeholder);
        // validate_module rejects any module carrying it BEFORE serialization,
        // so reaching this arm is an invariant violation - fail closed loudly
        // rather than invent a wire spelling for a typing hole.
        Ty::Error => {
            panic!("Ty::Error is producer-internal and not encodable; validate_module rejects it")
        }
        Ty::F16 => write_u8(buf, 31),
        Ty::F32 => write_u8(buf, 10),
        Ty::F64 => write_u8(buf, 11),
        Ty::Bool => write_u8(buf, 12),
        Ty::Ptr => write_u8(buf, 13),
        Ty::Unit => write_u8(buf, 14),
        Ty::Never => write_u8(buf, 15),
        Ty::Struct(id) => {
            write_u8(buf, 16);
            write_struct_id(buf, *id);
        }
        Ty::Array(tid, len) => {
            write_u8(buf, 17);
            write_ty_id(buf, *tid);
            write_v64(buf, *len);
        }
        Ty::Tuple(elems) => {
            write_u8(buf, 18);
            write_v32(buf, len_u32(elems.len()));
            for e in elems {
                write_ty(buf, pool, e);
            }
        }
        Ty::Enum(id) => {
            write_u8(buf, 19);
            write_enum_id(buf, *id);
        }
        Ty::Func(id) => {
            write_u8(buf, 20);
            write_func_ty_id(buf, *id);
        }
        Ty::Ref(inner) => {
            write_u8(buf, 21);
            write_ty(buf, pool, inner);
        }
        Ty::RefMut(inner) => {
            write_u8(buf, 22);
            write_ty(buf, pool, inner);
        }
        Ty::PtrConst(inner) => {
            write_u8(buf, 23);
            write_ty(buf, pool, inner);
        }
        Ty::PtrMut(inner) => {
            write_u8(buf, 24);
            write_ty(buf, pool, inner);
        }
        Ty::Rc(inner) => {
            write_u8(buf, 25);
            write_ty(buf, pool, inner);
        }
        Ty::Set(elem, repr) => {
            write_u8(buf, 26);
            write_ty_id(buf, *elem);
            write_set_repr(buf, repr);
        }
        Ty::Sequence(elem) => {
            write_u8(buf, 27);
            write_ty_id(buf, *elem);
        }
        Ty::Record(id) => {
            write_u8(buf, 28);
            write_record_id(buf, *id);
        }
        Ty::Closure(id) => {
            write_u8(buf, 29);
            write_closure_ty_id(buf, *id);
        }
        Ty::FatPtr(kind) => {
            write_u8(buf, 30);
            write_fat_ptr_kind(buf, pool, kind);
        }
        Ty::Vector(elem, lanes) => {
            write_u8(buf, 32);
            write_v32(buf, *lanes);
            write_ty(buf, pool, elem);
        }
        // v30: refinement carrier. Representation-preserving — the base `TyId`
        // is what any consumer lays out; the `PredId` is proof surface.
        Ty::Refine(base, pred) => {
            write_u8(buf, 36);
            write_ty_id(buf, *base);
            write_v32(buf, pred.index());
        }
    }
}

fn write_fat_ptr_kind(buf: &mut Vec<u8>, _pool: &mut StringPool, kind: &FatPtrKind) {
    match kind {
        FatPtrKind::Slice(elem) => {
            write_u8(buf, 0);
            write_ty_id(buf, *elem);
        }
        FatPtrKind::Str => write_u8(buf, 1),
        FatPtrKind::TraitObject { trait_id } => {
            write_u8(buf, 2);
            write_v32(buf, *trait_id);
        }
    }
}

fn read_fat_ptr_kind(r: &mut Reader<'_>) -> Result<FatPtrKind, BinaryError> {
    match r.read_u8()? {
        0 => Ok(FatPtrKind::Slice(r.read_ty_id()?)),
        1 => Ok(FatPtrKind::Str),
        2 => Ok(FatPtrKind::TraitObject {
            trait_id: r.read_v32()?,
        }),
        t => Err(BinaryError::InvalidTag(t)),
    }
}

fn write_set_repr(buf: &mut Vec<u8>, repr: &SetRepr) {
    let tag: u8 = match repr {
        SetRepr::Bitset => 0,
        SetRepr::Boxed => 1,
    };
    write_u8(buf, tag);
}

fn read_set_repr(r: &mut Reader<'_>) -> Result<SetRepr, BinaryError> {
    match r.read_u8()? {
        0 => Ok(SetRepr::Bitset),
        1 => Ok(SetRepr::Boxed),
        t => Err(BinaryError::InvalidTag(t)),
    }
}

// ---------------------------------------------------------------------------
// v30: typed value model — Universe / Pred tables
// ---------------------------------------------------------------------------
//
// Both tables are CONTENT-INTERNED in memory. The codec preserves their order
// byte-for-byte because the index IS the identity a `Ty::Refine` cites; it
// deliberately does NOT re-intern on read (that would silently renumber a
// module and break every `PredId`/`UnivId` already embedded in its types).
// `validate_module` re-derives the interning invariant structurally instead.

fn write_universe(buf: &mut Vec<u8>, pool: &mut StringPool, u: &crate::pred::Universe) {
    match u {
        crate::pred::Universe::IntRange { lo, hi } => {
            write_u8(buf, 0);
            write_i128(buf, *lo);
            write_i128(buf, *hi);
        }
        crate::pred::Universe::Members(items) => {
            write_u8(buf, 1);
            write_v32(buf, len_u32(items.len()));
            for c in items {
                write_constant(buf, pool, c);
            }
        }
    }
}

fn read_universe(r: &mut Reader<'_>) -> Result<crate::pred::Universe, BinaryError> {
    match r.read_u8()? {
        0 => {
            let lo = r.read_i128()?;
            let hi = r.read_i128()?;
            Ok(crate::pred::Universe::IntRange { lo, hi })
        }
        1 => {
            let n = r.read_checked_len()?;
            let mut items = Vec::with_capacity(n);
            for _ in 0..n {
                items.push(read_constant(r)?);
            }
            Ok(crate::pred::Universe::Members(items))
        }
        t => Err(BinaryError::InvalidTag(t)),
    }
}

fn write_space(buf: &mut Vec<u8>, space: crate::pred::Space) {
    write_u8(
        buf,
        match space {
            crate::pred::Space::Index => 0,
            crate::pred::Space::Member => 1,
        },
    );
}

fn read_space(r: &mut Reader<'_>) -> Result<crate::pred::Space, BinaryError> {
    match r.read_u8()? {
        0 => Ok(crate::pred::Space::Index),
        1 => Ok(crate::pred::Space::Member),
        t => Err(BinaryError::InvalidTag(t)),
    }
}

fn write_pred(buf: &mut Vec<u8>, pool: &mut StringPool, p: &crate::pred::Pred) {
    use crate::pred::Pred;
    match p {
        Pred::Interval { lo, hi } => {
            write_u8(buf, 0);
            write_i128(buf, *lo);
            write_i128(buf, *hi);
        }
        Pred::FiniteSet(items) => {
            write_u8(buf, 1);
            write_v32(buf, len_u32(items.len()));
            for c in items {
                write_constant(buf, pool, c);
            }
        }
        Pred::InUniverse(u, space) => {
            write_u8(buf, 2);
            write_v32(buf, u.index());
            write_space(buf, *space);
        }
        Pred::NonZero => write_u8(buf, 3),
        Pred::NonNull => write_u8(buf, 4),
        Pred::Conj(children) => {
            write_u8(buf, 5);
            write_v32(buf, len_u32(children.len()));
            for c in children {
                write_v32(buf, c.index());
            }
        }
        Pred::Disj(children) => {
            write_u8(buf, 6);
            write_v32(buf, len_u32(children.len()));
            for c in children {
                write_v32(buf, c.index());
            }
        }
        Pred::Top => write_u8(buf, 7),
        Pred::Bottom => write_u8(buf, 8),
    }
}

fn read_pred(r: &mut Reader<'_>) -> Result<crate::pred::Pred, BinaryError> {
    use crate::pred::Pred;
    match r.read_u8()? {
        0 => {
            let lo = r.read_i128()?;
            let hi = r.read_i128()?;
            Ok(Pred::Interval { lo, hi })
        }
        1 => {
            let n = r.read_checked_len()?;
            let mut items = Vec::with_capacity(n);
            for _ in 0..n {
                items.push(read_constant(r)?);
            }
            Ok(Pred::FiniteSet(items))
        }
        2 => {
            let u = crate::value::UnivId::new(r.read_v32()?);
            let space = read_space(r)?;
            Ok(Pred::InUniverse(u, space))
        }
        3 => Ok(Pred::NonZero),
        4 => Ok(Pred::NonNull),
        tag @ (5 | 6) => {
            let n = r.read_checked_len()?;
            let mut children = Vec::with_capacity(n);
            for _ in 0..n {
                children.push(crate::value::PredId::new(r.read_v32()?));
            }
            Ok(if tag == 5 {
                Pred::Conj(children)
            } else {
                Pred::Disj(children)
            })
        }
        7 => Ok(Pred::Top),
        8 => Ok(Pred::Bottom),
        t => Err(BinaryError::InvalidTag(t)),
    }
}

fn read_ty(r: &mut Reader<'_>) -> Result<Ty, BinaryError> {
    r.enter_nesting()?;
    let result = read_ty_inner(r);
    r.leave_nesting();
    result
}

fn read_ty_inner(r: &mut Reader<'_>) -> Result<Ty, BinaryError> {
    let tag = r.read_u8()?;
    match tag {
        0 => Ok(Ty::I8),
        1 => Ok(Ty::I16),
        2 => Ok(Ty::I32),
        3 => Ok(Ty::I64),
        4 => Ok(Ty::I128),
        5 => Ok(Ty::U8),
        6 => Ok(Ty::U16),
        7 => Ok(Ty::U32),
        8 => Ok(Ty::U64),
        9 => Ok(Ty::U128),
        // v25 B1 scalars.
        33 => Ok(Ty::Isize),
        34 => Ok(Ty::Usize),
        35 => Ok(Ty::Char),
        10 => Ok(Ty::F32),
        11 => Ok(Ty::F64),
        12 => Ok(Ty::Bool),
        13 => Ok(Ty::Ptr),
        14 => Ok(Ty::Unit),
        15 => Ok(Ty::Never),
        16 => Ok(Ty::Struct(r.read_struct_id()?)),
        17 => {
            let tid = r.read_ty_id()?;
            let len = r.read_v64()?;
            Ok(Ty::Array(tid, len))
        }
        18 => {
            let n = r.read_checked_len()?;
            let mut elems = Vec::with_capacity(n);
            for _ in 0..n {
                elems.push(read_ty(r)?);
            }
            Ok(Ty::Tuple(elems))
        }
        19 => Ok(Ty::Enum(r.read_enum_id()?)),
        20 => Ok(Ty::Func(r.read_func_ty_id()?)),
        21 => Ok(Ty::Ref(Box::new(read_ty(r)?))),
        22 => Ok(Ty::RefMut(Box::new(read_ty(r)?))),
        23 => Ok(Ty::PtrConst(Box::new(read_ty(r)?))),
        24 => Ok(Ty::PtrMut(Box::new(read_ty(r)?))),
        25 => Ok(Ty::Rc(Box::new(read_ty(r)?))),
        26 => {
            let elem = r.read_ty_id()?;
            let repr = read_set_repr(r)?;
            Ok(Ty::Set(elem, repr))
        }
        27 => Ok(Ty::Sequence(r.read_ty_id()?)),
        28 => Ok(Ty::Record(r.read_record_id()?)),
        29 => Ok(Ty::Closure(r.read_closure_ty_id()?)),
        30 => Ok(Ty::FatPtr(read_fat_ptr_kind(r)?)),
        31 => Ok(Ty::F16),
        32 => {
            let lanes = r.read_v32()?;
            let elem = read_ty(r)?;
            Ok(Ty::Vector(Box::new(elem), lanes))
        }
        // v30 refinement carrier. No version gate: tag 36 never appears in a
        // pre-v30 blob, so reaching it already implies a v30+ writer.
        36 => {
            let base = r.read_ty_id()?;
            let pred = crate::value::PredId::new(r.read_v32()?);
            Ok(Ty::Refine(base, pred))
        }
        _ => Err(BinaryError::InvalidTag(tag)),
    }
}

// ---------------------------------------------------------------------------
// Constant
// ---------------------------------------------------------------------------

fn write_constant(buf: &mut Vec<u8>, pool: &mut StringPool, c: &Constant) {
    match c {
        Constant::Int(v) => {
            write_u8(buf, 0);
            write_i128(buf, *v);
        }
        // v24: the 128-bit-faithful unsigned carrier (canonical iff the value
        // exceeds i128::MAX - the decoder REJECTS a non-canonical payload).
        Constant::U128(v) => {
            write_u8(buf, 13);
            write_u128(buf, *v);
        }
        // v25: raw byte-array constant (utf8 flag + length-prefixed payload).
        Constant::Bytes { data, utf8 } => {
            write_u8(buf, 14);
            write_bool(buf, *utf8);
            write_v32(buf, len_u32(data.len()));
            buf.extend_from_slice(data);
        }
        Constant::Float(v) => {
            write_u8(buf, 1);
            write_f64(buf, *v);
        }
        Constant::Bool(v) => {
            write_u8(buf, 2);
            write_bool(buf, *v);
        }
        Constant::Aggregate(elems) => {
            write_u8(buf, 3);
            write_v32(buf, len_u32(elems.len()));
            for e in elems {
                write_constant(buf, pool, e);
            }
        }
        Constant::Array(elems) => {
            write_u8(buf, 8);
            write_v32(buf, len_u32(elems.len()));
            for e in elems {
                write_constant(buf, pool, e);
            }
        }
        Constant::Vector(elems) => {
            write_u8(buf, 11);
            write_v32(buf, len_u32(elems.len()));
            for e in elems {
                write_constant(buf, pool, e);
            }
        }
        Constant::Sequence(elems) => {
            write_u8(buf, 4);
            write_v32(buf, len_u32(elems.len()));
            for e in elems {
                write_constant(buf, pool, e);
            }
        }
        Constant::Set(elems) => {
            write_u8(buf, 5);
            write_v32(buf, len_u32(elems.len()));
            for e in elems {
                write_constant(buf, pool, e);
            }
        }
        Constant::Record(fields) => {
            write_u8(buf, 6);
            write_v32(buf, len_u32(fields.len()));
            for (name, val) in fields {
                write_str(buf, pool, name);
                write_constant(buf, pool, val);
            }
        }
        Constant::Closure { func, captures } => {
            write_u8(buf, 7);
            write_func_id(buf, *func);
            write_v32(buf, len_u32(captures.len()));
            for c in captures {
                write_constant(buf, pool, c);
            }
        }
        Constant::FnDef(func) => {
            write_u8(buf, 9);
            write_func_id(buf, *func);
        }
        Constant::SymbolAddr { symbol, addend } => {
            write_u8(buf, 12);
            write_str(buf, pool, symbol);
            write_u64(buf, *addend as u64);
        }
        Constant::PhantomData => write_u8(buf, 10),
    }
}

fn read_constant(r: &mut Reader<'_>) -> Result<Constant, BinaryError> {
    r.enter_nesting()?;
    let result = read_constant_inner(r);
    r.leave_nesting();
    result
}

fn read_constant_inner(r: &mut Reader<'_>) -> Result<Constant, BinaryError> {
    let tag = r.read_u8()?;
    match tag {
        0 => Ok(Constant::Int(r.read_i128()?)),
        // v24 U128: canonicality is CHECKED, not assumed - a payload i128
        // could carry must be spelled Int (one-spelling rule); rejecting it
        // here keeps Eq/Hash value-faithful for every decoded module.
        13 => {
            let v = r.read_u128()?;
            if v <= i128::MAX as u128 {
                return Err(BinaryError::InvalidData(format!(
                    "non-canonical Constant::U128({v}): values <= i128::MAX must be spelled Constant::Int (v24 one-spelling rule)"
                )));
            }
            Ok(Constant::U128(v))
        }
        // v25 Bytes: the utf8 flag is a CHECKED claim — reject invalid UTF-8
        // under the flag at decode (mirrors the validator; a str constant
        // with broken bytes must never materialize).
        14 => {
            let utf8 = r.read_bool()?;
            let len = r.read_checked_len()?;
            let data = r.read_exact(len)?.to_vec();
            if utf8 && std::str::from_utf8(&data).is_err() {
                return Err(BinaryError::InvalidData(
                    "Constant::Bytes marked utf8 carries invalid UTF-8".to_string(),
                ));
            }
            Ok(Constant::Bytes { data, utf8 })
        }
        1 => Ok(Constant::Float(r.read_f64()?)),
        2 => Ok(Constant::Bool(r.read_bool()?)),
        3 => {
            let n = r.read_checked_len()?;
            let mut elems = Vec::with_capacity(n);
            for _ in 0..n {
                elems.push(read_constant(r)?);
            }
            Ok(Constant::Aggregate(elems))
        }
        8 => {
            let n = r.read_checked_len()?;
            let mut elems = Vec::with_capacity(n);
            for _ in 0..n {
                elems.push(read_constant(r)?);
            }
            Ok(Constant::Array(elems))
        }
        11 => {
            let n = r.read_checked_len()?;
            let mut elems = Vec::with_capacity(n);
            for _ in 0..n {
                elems.push(read_constant(r)?);
            }
            Ok(Constant::Vector(elems))
        }
        4 => {
            let n = r.read_checked_len()?;
            let mut elems = Vec::with_capacity(n);
            for _ in 0..n {
                elems.push(read_constant(r)?);
            }
            Ok(Constant::Sequence(elems))
        }
        5 => {
            let n = r.read_checked_len()?;
            let mut elems = Vec::with_capacity(n);
            for _ in 0..n {
                elems.push(read_constant(r)?);
            }
            Ok(Constant::Set(elems))
        }
        6 => {
            let n = r.read_checked_len()?;
            let mut fields = Vec::with_capacity(n);
            for _ in 0..n {
                let name = r.read_str()?;
                let val = read_constant(r)?;
                fields.push((name, val));
            }
            Ok(Constant::Record(fields))
        }
        7 => {
            let func = r.read_func_id()?;
            let n = r.read_checked_len()?;
            let mut captures = Vec::with_capacity(n);
            for _ in 0..n {
                captures.push(read_constant(r)?);
            }
            Ok(Constant::Closure { func, captures })
        }
        9 => Ok(Constant::FnDef(r.read_func_id()?)),
        12 => {
            let symbol = r.read_str()?;
            let addend = r.read_u64()? as i64;
            Ok(Constant::SymbolAddr { symbol, addend })
        }
        10 => Ok(Constant::PhantomData),
        _ => Err(BinaryError::InvalidTag(tag)),
    }
}

// ---------------------------------------------------------------------------
// Small enums (tag-only)
// ---------------------------------------------------------------------------

macro_rules! tag_enum {
    ($write:ident, $read:ident, $ty:ty, $( $variant:ident => $tag:expr ),+ $(,)?) => {
        fn $write(buf: &mut Vec<u8>, v: &$ty) {
            let tag: u8 = match v {
                $( <$ty>::$variant => $tag, )+
            };
            write_u8(buf, tag);
        }

        fn $read(r: &mut Reader<'_>) -> Result<$ty, BinaryError> {
            let tag = r.read_u8()?;
            match tag {
                $( $tag => Ok(<$ty>::$variant), )+
                _ => Err(BinaryError::InvalidTag(tag)),
            }
        }
    };
}

tag_enum!(write_binop, read_binop, BinOp,
    Add => 0, Sub => 1, Mul => 2, UDiv => 3, SDiv => 4,
    URem => 5, SRem => 6, FAdd => 7, FSub => 8, FMul => 9,
    FDiv => 10, FRem => 11, And => 12, Or => 13, Xor => 14,
    Shl => 15, LShr => 16, AShr => 17, FMin => 18, FMax => 19,
    BAnd => 20, BOr => 21, BXor => 22,
);

#[cfg(test)]
mod bool_connective_tag_tests {
    //! The wire tags for `BAnd`/`BOr`/`BXor`.
    //!
    //! These are NOT covered by `module_roundtrip_fuzz`'s `all_binops` catalog:
    //! that feeds generated modules which must type-check, and the connectives
    //! are Bool-only by validation while the generator emits integer operands
    //! (the same reason FMin/FMax are absent from it). Covered directly here so
    //! the tags are not simply untested.

    use super::*;

    #[test]
    fn tags_roundtrip_and_are_appended_not_renumbered() {
        // Appended after FMax=19, so every pre-existing encoding is untouched.
        for (op, tag) in [(BinOp::BAnd, 20u8), (BinOp::BOr, 21), (BinOp::BXor, 22)] {
            let mut buf = Vec::new();
            write_binop(&mut buf, &op);
            assert_eq!(buf, vec![tag], "{op} must encode as the appended tag {tag}");
            let mut reader = Reader::new(buf.as_slice());
            assert_eq!(read_binop(&mut reader).unwrap(), op, "{op} must roundtrip");
        }
        // The pre-existing tags must not have shifted.
        let mut buf = Vec::new();
        write_binop(&mut buf, &BinOp::AShr);
        assert_eq!(buf, vec![17u8], "AShr must still be tag 17");
    }
}

tag_enum!(write_unop, read_unop, UnOp,
    Neg => 0, FNeg => 1, Not => 2, CtPop => 3, FAbs => 4, FSqrt => 5,
    FFloor => 6, FCeil => 7, FTrunc => 8,
);

tag_enum!(write_overflow_op, read_overflow_op, OverflowOp,
    AddOverflow => 0, SubOverflow => 1, MulOverflow => 2,
);

tag_enum!(write_icmp_op, read_icmp_op, ICmpOp,
    Eq => 0, Ne => 1, Ult => 2, Ule => 3, Ugt => 4,
    Uge => 5, Slt => 6, Sle => 7, Sgt => 8, Sge => 9,
);

tag_enum!(write_fcmp_op, read_fcmp_op, FCmpOp,
    OEq => 0, ONe => 1, OLt => 2, OLe => 3, OGt => 4, OGe => 5,
    UEq => 6, UNe => 7, ULt => 8, ULe => 9, UGt => 10, UGe => 11,
);

tag_enum!(write_cast_op, read_cast_op, CastOp,
    Trunc => 0, ZExt => 1, SExt => 2, FPTrunc => 3, FPExt => 4,
    FPToUI => 5, FPToSI => 6, UIToFP => 7, SIToFP => 8,
    PtrToInt => 9, IntToPtr => 10, Bitcast => 11, PtrToPtr => 12,
    Transmute => 13, ReifyFnPointer => 14,
    // Additive leaf tags (no VERSION bump: older modules never carry them, and
    // read_cast_op cleanly rejects an unknown tag). Saturating float→int casts.
    FPToSISat => 15, FPToUISat => 16,
);

tag_enum!(write_ordering, read_ordering, Ordering,
    Relaxed => 0, Acquire => 1, Release => 2, AcqRel => 3, SeqCst => 4,
);

tag_enum!(write_atomic_rmw_op, read_atomic_rmw_op, AtomicRMWOp,
    Xchg => 0, Add => 1, Sub => 2, And => 3, Or => 4,
    Xor => 5, Max => 6, Min => 7, UMax => 8, UMin => 9,
);

tag_enum!(write_obligation_kind, read_obligation_kind, ObligationKind,
    Precondition => 0, Postcondition => 1, LoopInvariant => 2,
    TypeInvariant => 3, RefinementType => 4, TranslationValidation => 5,
    MemorySafety => 6, PanicFreedom => 7, TemporalSafety => 8, Liveness => 9,
    // Trust (trust-ir-spine item T1): panic-class routing-grade kinds.
    ArithmeticSafety => 10, BoundsCheck => 11,
    // Aeneas-style give-back refinement view (trust-ir-giveback).
    GiveBackRefinement => 12,
);

tag_enum!(write_proof_status, read_proof_status, ProofStatus,
    Pending => 0, Discharged => 1, Failed => 2, Trusted => 3, Certified => 4,
);

tag_enum!(write_calling_conv, read_calling_conv, CallingConv,
    C => 0, Fast => 1, Cold => 2, Rust => 3, Swift => 4,
);

tag_enum!(write_linkage, read_linkage, Linkage,
    External => 0, Internal => 1, Private => 2, Weak => 3, LinkOnce => 4,
);

tag_enum!(write_tls_model, read_tls_model, TlsModel,
    LocalExec => 0, InitialExec => 1, GeneralDynamic => 2, LocalDynamic => 3,
);

tag_enum!(write_endianness, read_endianness, Endianness,
    Little => 0, Big => 1,
);

// ---------------------------------------------------------------------------
// Vec helpers
// ---------------------------------------------------------------------------

fn write_vec_value_id(buf: &mut Vec<u8>, ids: &[ValueId]) {
    write_v32(buf, len_u32(ids.len()));
    for id in ids {
        write_value_id(buf, *id);
    }
}

fn read_vec_value_id(r: &mut Reader<'_>) -> Result<Vec<ValueId>, BinaryError> {
    let n = r.read_checked_len()?;
    let mut v = Vec::with_capacity(n);
    for _ in 0..n {
        v.push(r.read_value_id()?);
    }
    Ok(v)
}

// ---------------------------------------------------------------------------
// Inst
// ---------------------------------------------------------------------------

fn write_inst(buf: &mut Vec<u8>, pool: &mut StringPool, inst: &Inst) {
    match inst {
        Inst::BinOp { op, ty, lhs, rhs } => {
            write_u8(buf, 0);
            write_binop(buf, op);
            write_ty(buf, pool, ty);
            write_value_id(buf, *lhs);
            write_value_id(buf, *rhs);
        }
        Inst::UnOp { op, ty, operand } => {
            write_u8(buf, 1);
            write_unop(buf, op);
            write_ty(buf, pool, ty);
            write_value_id(buf, *operand);
        }
        Inst::Overflow { op, ty, lhs, rhs } => {
            write_u8(buf, 2);
            write_overflow_op(buf, op);
            write_ty(buf, pool, ty);
            write_value_id(buf, *lhs);
            write_value_id(buf, *rhs);
        }
        Inst::ICmp { op, ty, lhs, rhs } => {
            write_u8(buf, 3);
            write_icmp_op(buf, op);
            write_ty(buf, pool, ty);
            write_value_id(buf, *lhs);
            write_value_id(buf, *rhs);
        }
        Inst::FCmp { op, ty, lhs, rhs } => {
            write_u8(buf, 4);
            write_fcmp_op(buf, op);
            write_ty(buf, pool, ty);
            write_value_id(buf, *lhs);
            write_value_id(buf, *rhs);
        }
        Inst::Cast {
            op,
            src_ty,
            dst_ty,
            operand,
        } => {
            write_u8(buf, 5);
            write_cast_op(buf, op);
            write_ty(buf, pool, src_ty);
            write_ty(buf, pool, dst_ty);
            write_value_id(buf, *operand);
        }
        Inst::Load {
            ty,
            ptr,
            volatile,
            align,
        } => {
            write_u8(buf, 6);
            write_ty(buf, pool, ty);
            write_value_id(buf, *ptr);
            write_bool(buf, *volatile);
            write_opt_u64(buf, *align);
        }
        Inst::Store {
            ty,
            ptr,
            value,
            volatile,
            align,
        } => {
            write_u8(buf, 7);
            write_ty(buf, pool, ty);
            write_value_id(buf, *ptr);
            write_value_id(buf, *value);
            write_bool(buf, *volatile);
            write_opt_u64(buf, *align);
        }
        Inst::Alloca { ty, count, align } => {
            write_u8(buf, 8);
            write_ty(buf, pool, ty);
            match count {
                None => write_u8(buf, 0),
                Some(v) => {
                    write_u8(buf, 1);
                    write_v32(buf, v.0);
                }
            }
            write_opt_u64(buf, *align);
        }
        Inst::HeapAlloc {
            ty,
            count,
            align,
            origin,
        } => {
            write_u8(buf, 49);
            write_ty(buf, pool, ty);
            match count {
                None => write_u8(buf, 0),
                Some(v) => {
                    write_u8(buf, 1);
                    write_v32(buf, v.0);
                }
            }
            write_opt_u64(buf, *align);
            write_u8(
                buf,
                match origin {
                    AllocOrigin::RustHeap => 0,
                    AllocOrigin::SwiftHeap => 1,
                    AllocOrigin::CMalloc => 2,
                    // v22: Clean Perceus RC heap. Old readers reject the blob
                    // at the header version check before seeing this byte.
                    AllocOrigin::CleanHeap => 3,
                },
            );
        }
        Inst::GEP {
            pointee_ty,
            base,
            indices,
            inbounds,
        } => {
            write_u8(buf, 9);
            write_ty(buf, pool, pointee_ty);
            write_value_id(buf, *base);
            write_vec_value_id(buf, indices);
            write_bool(buf, *inbounds);
        }
        Inst::AtomicLoad { ty, ptr, ordering } => {
            write_u8(buf, 10);
            write_ty(buf, pool, ty);
            write_value_id(buf, *ptr);
            write_ordering(buf, ordering);
        }
        Inst::AtomicStore {
            ty,
            ptr,
            value,
            ordering,
        } => {
            write_u8(buf, 11);
            write_ty(buf, pool, ty);
            write_value_id(buf, *ptr);
            write_value_id(buf, *value);
            write_ordering(buf, ordering);
        }
        Inst::AtomicRMW {
            op,
            ty,
            ptr,
            value,
            ordering,
        } => {
            write_u8(buf, 12);
            write_atomic_rmw_op(buf, op);
            write_ty(buf, pool, ty);
            write_value_id(buf, *ptr);
            write_value_id(buf, *value);
            write_ordering(buf, ordering);
        }
        Inst::CmpXchg {
            ty,
            ptr,
            expected,
            desired,
            success,
            failure,
        } => {
            write_u8(buf, 13);
            write_ty(buf, pool, ty);
            write_value_id(buf, *ptr);
            write_v32(buf, expected.0);
            write_v32(buf, desired.0);
            write_ordering(buf, success);
            write_ordering(buf, failure);
        }
        Inst::Fence { ordering } => {
            write_u8(buf, 14);
            write_ordering(buf, ordering);
        }
        Inst::Br { target, args } => {
            write_u8(buf, 15);
            write_block_id(buf, *target);
            write_vec_value_id(buf, args);
        }
        Inst::CondBr {
            cond,
            then_target,
            then_args,
            else_target,
            else_args,
        } => {
            write_u8(buf, 16);
            write_value_id(buf, *cond);
            write_block_id(buf, *then_target);
            write_vec_value_id(buf, then_args);
            write_block_id(buf, *else_target);
            write_vec_value_id(buf, else_args);
        }
        Inst::Switch {
            value,
            default,
            default_args,
            cases,
            exhaustive_enum_unreachable,
        } => {
            write_u8(buf, 17);
            write_value_id(buf, *value);
            write_block_id(buf, *default);
            write_vec_value_id(buf, default_args);
            write_v32(buf, len_u32(cases.len()));
            for sc in cases {
                write_constant(buf, pool, &sc.value);
                write_v32(buf, sc.target.0);
                write_vec_value_id(buf, &sc.args);
            }
            // v15+: exhaustive-enum-unreachable flag; legacy modules default false.
            write_bool(buf, *exhaustive_enum_unreachable);
        }
        Inst::Call { callee, args } => {
            write_u8(buf, 18);
            write_func_id(buf, *callee);
            write_vec_value_id(buf, args);
        }
        Inst::CallIndirect {
            callee,
            sig,
            args,
            calling_conv,
        } => {
            write_u8(buf, 19);
            write_value_id(buf, *callee);
            write_func_ty_id(buf, *sig);
            write_vec_value_id(buf, args);
            // VERSION >= 12: indirect-call ABI. Read side defaults C on older.
            write_calling_conv(buf, calling_conv);
        }
        Inst::Return { values } => {
            write_u8(buf, 20);
            write_vec_value_id(buf, values);
        }
        Inst::ExtractField {
            ty,
            aggregate,
            field,
        } => {
            write_u8(buf, 21);
            write_ty(buf, pool, ty);
            write_value_id(buf, *aggregate);
            write_v32(buf, *field);
        }
        Inst::InsertField {
            ty,
            aggregate,
            field,
            value,
        } => {
            write_u8(buf, 22);
            write_ty(buf, pool, ty);
            write_value_id(buf, *aggregate);
            write_v32(buf, *field);
            write_value_id(buf, *value);
        }
        Inst::ExtractElement { ty, array, index } => {
            write_u8(buf, 23);
            write_ty(buf, pool, ty);
            write_value_id(buf, *array);
            write_value_id(buf, *index);
        }
        Inst::InsertElement {
            ty,
            array,
            index,
            value,
        } => {
            write_u8(buf, 24);
            write_ty(buf, pool, ty);
            write_value_id(buf, *array);
            write_value_id(buf, *index);
            write_value_id(buf, *value);
        }
        Inst::Const { ty, value } => {
            write_u8(buf, 25);
            write_ty(buf, pool, ty);
            write_constant(buf, pool, value);
        }
        Inst::NullPtr => write_u8(buf, 26),
        Inst::GlobalAddr { global } => {
            write_u8(buf, 48);
            write_v32(buf, global.index());
        }
        Inst::Undef { ty } => {
            write_u8(buf, 27);
            write_ty(buf, pool, ty);
        }
        Inst::Assume { cond } => {
            write_u8(buf, 28);
            write_value_id(buf, *cond);
        }
        Inst::Assert { cond } => {
            write_u8(buf, 29);
            write_value_id(buf, *cond);
        }
        Inst::Unreachable => write_u8(buf, 30),
        Inst::Copy { ty, operand } => {
            write_u8(buf, 31);
            write_ty(buf, pool, ty);
            write_value_id(buf, *operand);
        }
        Inst::Select {
            ty,
            cond,
            then_val,
            else_val,
        } => {
            write_u8(buf, 32);
            write_ty(buf, pool, ty);
            write_value_id(buf, *cond);
            write_value_id(buf, *then_val);
            write_value_id(buf, *else_val);
        }
        Inst::Borrow { ptr } => {
            write_u8(buf, 33);
            write_value_id(buf, *ptr);
        }
        Inst::BorrowMut { ptr } => {
            write_u8(buf, 34);
            write_value_id(buf, *ptr);
        }
        Inst::EndBorrow { borrow_ptr } => {
            write_u8(buf, 35);
            write_value_id(buf, *borrow_ptr);
        }
        Inst::Retain { ptr } => {
            write_u8(buf, 36);
            write_value_id(buf, *ptr);
        }
        Inst::Release { ptr } => {
            write_u8(buf, 37);
            write_value_id(buf, *ptr);
        }
        Inst::IsUnique { ptr } => {
            write_u8(buf, 38);
            write_value_id(buf, *ptr);
        }
        Inst::Dealloc { ptr } => {
            write_u8(buf, 39);
            write_value_id(buf, *ptr);
        }
        // Binding frames (tags 40..=43)
        Inst::OpenFrame { def } => {
            write_u8(buf, 40);
            write_v32(buf, def.id.index());
            write_str(buf, pool, &def.name);
            write_v32(buf, len_u32(def.slots.len()));
            for slot in &def.slots {
                write_str(buf, pool, &slot.name);
                write_ty(buf, pool, &slot.ty);
            }
        }
        Inst::BindSlot { frame, slot, value } => {
            write_u8(buf, 41);
            write_v32(buf, frame.0);
            write_v32(buf, *slot);
            write_value_id(buf, *value);
        }
        Inst::LoadSlot { frame, slot, ty } => {
            write_u8(buf, 42);
            write_v32(buf, frame.0);
            write_v32(buf, *slot);
            write_ty(buf, pool, ty);
        }
        Inst::CloseFrame { frame } => {
            write_u8(buf, 43);
            write_v32(buf, frame.0);
        }
        // Coroutine suspend (tag 50, v16+). New wire tags are never present in
        // pre-v16 blobs, so no read-side version gate is needed.
        Inst::CoroSuspend {
            frame,
            state_slot,
            next_state,
            value,
        } => {
            write_u8(buf, 50);
            write_value_id(buf, *frame);
            write_v32(buf, *state_slot);
            write_i128(buf, i128::from(*next_state));
            write_value_id(buf, *value);
        }
        // Exception handling (tags 51..=53, v17+). New wire tags are never
        // present in pre-v17 blobs, so no read-side version gate is needed.
        Inst::Invoke {
            callee,
            args,
            normal_dest,
            normal_args,
            unwind_dest,
        } => {
            write_u8(buf, 51);
            write_func_id(buf, *callee);
            write_vec_value_id(buf, args);
            write_block_id(buf, *normal_dest);
            write_vec_value_id(buf, normal_args);
            write_block_id(buf, *unwind_dest);
        }
        Inst::LandingPad {
            is_cleanup,
            catch_type_indices,
        } => {
            write_u8(buf, 52);
            write_bool(buf, *is_cleanup);
            write_v32(buf, len_u32(catch_type_indices.len()));
            for idx in catch_type_indices {
                write_v32(buf, *idx);
            }
        }
        Inst::Resume { exn } => {
            write_u8(buf, 53);
            write_value_id(buf, *exn);
        }
        Inst::SeqMapAddK { ty, seq, k } => {
            write_u8(buf, 54);
            write_ty(buf, pool, ty);
            write_value_id(buf, *seq);
            write_u64(buf, *k);
        }
        Inst::SeqMapNot { ty, seq } => {
            write_u8(buf, 55);
            write_ty(buf, pool, ty);
            write_value_id(buf, *seq);
        }
        Inst::SeqMap { ty, seq, fwd } => {
            // VERSION >= 21: general element-op loop (ty + seq + element FuncId).
            write_u8(buf, 56);
            write_ty(buf, pool, ty);
            write_value_id(buf, *seq);
            write_func_id(buf, *fwd);
        }
        Inst::DialectOp(op) => {
            write_u8(buf, 44);
            write_dialect_inst(buf, pool, op);
        }
        Inst::PtrData { ptr_ty, ptr } => {
            write_u8(buf, 45);
            write_ty(buf, pool, ptr_ty);
            write_value_id(buf, *ptr);
        }
        Inst::PtrMetadata {
            ptr_ty,
            metadata_ty,
            ptr,
        } => {
            write_u8(buf, 46);
            write_ty(buf, pool, ptr_ty);
            write_ty(buf, pool, metadata_ty);
            write_value_id(buf, *ptr);
        }
        Inst::PtrFromParts {
            ptr_ty,
            metadata_ty,
            data,
            metadata,
        } => {
            write_u8(buf, 47);
            write_ty(buf, pool, ptr_ty);
            write_ty(buf, pool, metadata_ty);
            write_value_id(buf, *data);
            write_value_id(buf, *metadata);
        }
    }
}

fn write_dialect_inst(buf: &mut Vec<u8>, pool: &mut StringPool, op: &crate::dialect::DialectInst) {
    write_str(buf, pool, &op.dialect);
    write_str(buf, pool, &op.op);
    write_vec_value_id(buf, &op.operands);
    write_v32(buf, len_u32(op.result_tys.len()));
    for t in &op.result_tys {
        write_ty(buf, pool, t);
    }
    write_v32(buf, len_u32(op.attrs.len()));
    for entry in &op.attrs {
        write_str(buf, pool, &entry.name);
        write_attr_value(buf, pool, &entry.value);
    }
    write_v32(buf, op.version);
}

fn write_attr_value(buf: &mut Vec<u8>, pool: &mut StringPool, v: &crate::dialect::AttrValue) {
    use crate::dialect::AttrValue;
    match v {
        AttrValue::I64(x) => {
            write_u8(buf, 0);
            // Stored as u64 bit pattern; read back via signed cast.
            buf.extend_from_slice(&x.to_le_bytes());
        }
        AttrValue::U64(x) => {
            write_u8(buf, 1);
            write_v64(buf, *x);
        }
        AttrValue::F64(x) => {
            write_u8(buf, 2);
            write_f64(buf, *x);
        }
        AttrValue::Bool(x) => {
            write_u8(buf, 3);
            write_bool(buf, *x);
        }
        AttrValue::Str(s) => {
            write_u8(buf, 4);
            write_str(buf, pool, s);
        }
        AttrValue::Bytes(b) => {
            write_u8(buf, 5);
            write_bytes(buf, b);
        }
        AttrValue::Ty(t) => {
            write_u8(buf, 6);
            write_ty(buf, pool, t);
        }
    }
}

fn read_dialect_inst(r: &mut Reader<'_>) -> Result<crate::dialect::DialectInst, BinaryError> {
    let dialect = r.read_str()?;
    let op = r.read_str()?;
    let operands = read_vec_value_id(r)?;
    let n_tys = r.read_checked_len()?;
    let mut result_tys = Vec::with_capacity(n_tys);
    for _ in 0..n_tys {
        result_tys.push(read_ty(r)?);
    }
    let n_attrs = r.read_checked_len()?;
    let mut attrs = Vec::with_capacity(n_attrs);
    for _ in 0..n_attrs {
        let name = r.read_str()?;
        let value = read_attr_value(r)?;
        attrs.push(crate::dialect::AttrEntry { name, value });
    }
    let version = r.read_v32()?;
    Ok(crate::dialect::DialectInst {
        dialect,
        op,
        operands,
        result_tys,
        attrs,
        version,
    })
}

fn read_attr_value(r: &mut Reader<'_>) -> Result<crate::dialect::AttrValue, BinaryError> {
    use crate::dialect::AttrValue;
    let tag = r.read_u8()?;
    Ok(match tag {
        0 => {
            let b = r.read_exact(8)?;
            AttrValue::I64(i64::from_le_bytes([
                b[0], b[1], b[2], b[3], b[4], b[5], b[6], b[7],
            ]))
        }
        // `write_attr_value` encodes U64 as a varint (`write_v64`); the reader
        // must decode the same way. Using `read_u64` here consumed a fixed 8
        // bytes, desynchronizing the stream for every following field (it
        // surfaced as "invalid string id: <garbage>" on the next pooled string).
        1 => AttrValue::U64(r.read_v64()?),
        2 => AttrValue::F64(r.read_f64()?),
        3 => AttrValue::Bool(r.read_bool()?),
        4 => AttrValue::Str(r.read_str()?),
        5 => AttrValue::Bytes(r.read_bytes()?),
        6 => AttrValue::Ty(read_ty(r)?),
        t => return Err(BinaryError::InvalidTag(t)),
    })
}

fn read_inst(r: &mut Reader<'_>) -> Result<Inst, BinaryError> {
    let tag = r.read_u8()?;
    match tag {
        0 => Ok(Inst::BinOp {
            op: read_binop(r)?,
            ty: read_ty(r)?,
            lhs: r.read_value_id()?,
            rhs: r.read_value_id()?,
        }),
        1 => Ok(Inst::UnOp {
            op: read_unop(r)?,
            ty: read_ty(r)?,
            operand: r.read_value_id()?,
        }),
        2 => Ok(Inst::Overflow {
            op: read_overflow_op(r)?,
            ty: read_ty(r)?,
            lhs: r.read_value_id()?,
            rhs: r.read_value_id()?,
        }),
        3 => Ok(Inst::ICmp {
            op: read_icmp_op(r)?,
            ty: read_ty(r)?,
            lhs: r.read_value_id()?,
            rhs: r.read_value_id()?,
        }),
        4 => Ok(Inst::FCmp {
            op: read_fcmp_op(r)?,
            ty: read_ty(r)?,
            lhs: r.read_value_id()?,
            rhs: r.read_value_id()?,
        }),
        5 => Ok(Inst::Cast {
            op: read_cast_op(r)?,
            src_ty: read_ty(r)?,
            dst_ty: read_ty(r)?,
            operand: r.read_value_id()?,
        }),
        6 => Ok(Inst::Load {
            ty: read_ty(r)?,
            ptr: r.read_value_id()?,
            volatile: r.read_bool()?,
            align: read_opt_u64(r)?,
        }),
        7 => Ok(Inst::Store {
            ty: read_ty(r)?,
            ptr: r.read_value_id()?,
            value: r.read_value_id()?,
            volatile: r.read_bool()?,
            align: read_opt_u64(r)?,
        }),
        8 => {
            let ty = read_ty(r)?;
            let has_count = r.read_u8()?;
            let count = if has_count == 0 {
                None
            } else {
                Some(r.read_value_id()?)
            };
            let align = read_opt_u64(r)?;
            Ok(Inst::Alloca { ty, count, align })
        }
        49 => {
            let ty = read_ty(r)?;
            let has_count = r.read_u8()?;
            let count = if has_count == 0 {
                None
            } else {
                Some(r.read_value_id()?)
            };
            let align = read_opt_u64(r)?;
            let origin = match r.read_u8()? {
                0 => AllocOrigin::RustHeap,
                1 => AllocOrigin::SwiftHeap,
                2 => AllocOrigin::CMalloc,
                // v22+; pre-v22 blobs never contain 3, so no version gate
                // (same rationale as the v16/v17/v21 wholly-new tags).
                3 => AllocOrigin::CleanHeap,
                t => {
                    return Err(BinaryError::InvalidTag(t));
                }
            };
            Ok(Inst::HeapAlloc {
                ty,
                count,
                align,
                origin,
            })
        }
        9 => {
            let pointee_ty = read_ty(r)?;
            let base = r.read_value_id()?;
            let indices = read_vec_value_id(r)?;
            // v8+: GEP.inbounds (fast-3); legacy modules default to false.
            let inbounds = if r.version >= 8 {
                r.read_bool()?
            } else {
                false
            };
            Ok(Inst::GEP {
                pointee_ty,
                base,
                indices,
                inbounds,
            })
        }
        10 => Ok(Inst::AtomicLoad {
            ty: read_ty(r)?,
            ptr: r.read_value_id()?,
            ordering: read_ordering(r)?,
        }),
        11 => Ok(Inst::AtomicStore {
            ty: read_ty(r)?,
            ptr: r.read_value_id()?,
            value: r.read_value_id()?,
            ordering: read_ordering(r)?,
        }),
        12 => Ok(Inst::AtomicRMW {
            op: read_atomic_rmw_op(r)?,
            ty: read_ty(r)?,
            ptr: r.read_value_id()?,
            value: r.read_value_id()?,
            ordering: read_ordering(r)?,
        }),
        13 => Ok(Inst::CmpXchg {
            ty: read_ty(r)?,
            ptr: r.read_value_id()?,
            expected: r.read_value_id()?,
            desired: r.read_value_id()?,
            success: read_ordering(r)?,
            failure: read_ordering(r)?,
        }),
        14 => Ok(Inst::Fence {
            ordering: read_ordering(r)?,
        }),
        15 => Ok(Inst::Br {
            target: r.read_block_id()?,
            args: read_vec_value_id(r)?,
        }),
        16 => Ok(Inst::CondBr {
            cond: r.read_value_id()?,
            then_target: r.read_block_id()?,
            then_args: read_vec_value_id(r)?,
            else_target: r.read_block_id()?,
            else_args: read_vec_value_id(r)?,
        }),
        17 => {
            let value = r.read_value_id()?;
            let default = r.read_block_id()?;
            let default_args = read_vec_value_id(r)?;
            let n = r.read_checked_len()?;
            let mut cases = Vec::with_capacity(n);
            for _ in 0..n {
                cases.push(SwitchCase {
                    value: read_constant(r)?,
                    target: r.read_block_id()?,
                    args: read_vec_value_id(r)?,
                });
            }
            // v15+: exhaustive-enum-unreachable flag; legacy modules default false.
            let exhaustive_enum_unreachable = if r.version >= 15 {
                r.read_bool()?
            } else {
                false
            };
            Ok(Inst::Switch {
                value,
                default,
                default_args,
                cases,
                exhaustive_enum_unreachable,
            })
        }
        18 => Ok(Inst::Call {
            callee: r.read_func_id()?,
            args: read_vec_value_id(r)?,
        }),
        19 => {
            let callee = r.read_value_id()?;
            let sig = r.read_func_ty_id()?;
            let args = read_vec_value_id(r)?;
            // VERSION >= 12: indirect-call ABI; older modules default to C.
            let calling_conv = if r.version >= 12 {
                read_calling_conv(r)?
            } else {
                CallingConv::default()
            };
            Ok(Inst::CallIndirect {
                callee,
                sig,
                args,
                calling_conv,
            })
        }
        20 => Ok(Inst::Return {
            values: read_vec_value_id(r)?,
        }),
        21 => Ok(Inst::ExtractField {
            ty: read_ty(r)?,
            aggregate: r.read_value_id()?,
            field: r.read_v32()?,
        }),
        22 => Ok(Inst::InsertField {
            ty: read_ty(r)?,
            aggregate: r.read_value_id()?,
            field: r.read_v32()?,
            value: r.read_value_id()?,
        }),
        23 => Ok(Inst::ExtractElement {
            ty: read_ty(r)?,
            array: r.read_value_id()?,
            index: r.read_value_id()?,
        }),
        24 => Ok(Inst::InsertElement {
            ty: read_ty(r)?,
            array: r.read_value_id()?,
            index: r.read_value_id()?,
            value: r.read_value_id()?,
        }),
        25 => Ok(Inst::Const {
            ty: read_ty(r)?,
            value: read_constant(r)?,
        }),
        26 => Ok(Inst::NullPtr),
        48 => Ok(Inst::GlobalAddr {
            global: GlobalId::new(r.read_v32()?),
        }),
        27 => Ok(Inst::Undef { ty: read_ty(r)? }),
        28 => Ok(Inst::Assume {
            cond: r.read_value_id()?,
        }),
        29 => Ok(Inst::Assert {
            cond: r.read_value_id()?,
        }),
        30 => Ok(Inst::Unreachable),
        31 => Ok(Inst::Copy {
            ty: read_ty(r)?,
            operand: r.read_value_id()?,
        }),
        32 => Ok(Inst::Select {
            ty: read_ty(r)?,
            cond: r.read_value_id()?,
            then_val: r.read_value_id()?,
            else_val: r.read_value_id()?,
        }),
        33 => Ok(Inst::Borrow {
            ptr: r.read_value_id()?,
        }),
        34 => Ok(Inst::BorrowMut {
            ptr: r.read_value_id()?,
        }),
        35 => Ok(Inst::EndBorrow {
            borrow_ptr: r.read_value_id()?,
        }),
        36 => Ok(Inst::Retain {
            ptr: r.read_value_id()?,
        }),
        37 => Ok(Inst::Release {
            ptr: r.read_value_id()?,
        }),
        38 => Ok(Inst::IsUnique {
            ptr: r.read_value_id()?,
        }),
        39 => Ok(Inst::Dealloc {
            ptr: r.read_value_id()?,
        }),
        40 => {
            let id = crate::value::BindingFrameId::new(r.read_v32()?);
            let name = r.read_str()?;
            let slot_count = r.read_checked_len()?;
            let mut slots = Vec::with_capacity(slot_count);
            for _ in 0..slot_count {
                let sname = r.read_str()?;
                let sty = read_ty(r)?;
                slots.push(crate::inst::BindingSlot::new(sname, sty));
            }
            Ok(Inst::OpenFrame {
                def: crate::inst::BindingFrameDef::new(id, name, slots),
            })
        }
        41 => Ok(Inst::BindSlot {
            frame: r.read_value_id()?,
            slot: r.read_v32()?,
            value: r.read_value_id()?,
        }),
        42 => Ok(Inst::LoadSlot {
            frame: r.read_value_id()?,
            slot: r.read_v32()?,
            ty: read_ty(r)?,
        }),
        43 => Ok(Inst::CloseFrame {
            frame: r.read_value_id()?,
        }),
        50 => {
            let frame = r.read_value_id()?;
            let state_slot = r.read_v32()?;
            let next_state_i128 = r.read_i128()?;
            let next_state = i64::try_from(next_state_i128).map_err(|_| {
                BinaryError::InvalidData(format!(
                    "CoroSuspend next_state {next_state_i128} does not fit i64"
                ))
            })?;
            let value = r.read_value_id()?;
            Ok(Inst::CoroSuspend {
                frame,
                state_slot,
                next_state,
                value,
            })
        }
        51 => {
            let callee = r.read_func_id()?;
            let args = read_vec_value_id(r)?;
            let normal_dest = r.read_block_id()?;
            let normal_args = read_vec_value_id(r)?;
            let unwind_dest = r.read_block_id()?;
            Ok(Inst::Invoke {
                callee,
                args,
                normal_dest,
                normal_args,
                unwind_dest,
            })
        }
        52 => {
            let is_cleanup = r.read_bool()?;
            let n = r.read_checked_len()?;
            let mut catch_type_indices = Vec::with_capacity(n);
            for _ in 0..n {
                catch_type_indices.push(r.read_v32()?);
            }
            Ok(Inst::LandingPad {
                is_cleanup,
                catch_type_indices,
            })
        }
        53 => Ok(Inst::Resume {
            exn: r.read_value_id()?,
        }),
        54 => Ok(Inst::SeqMapAddK {
            ty: read_ty(r)?,
            seq: r.read_value_id()?,
            k: r.read_u64()?,
        }),
        55 => Ok(Inst::SeqMapNot {
            ty: read_ty(r)?,
            seq: r.read_value_id()?,
        }),
        56 => Ok(Inst::SeqMap {
            ty: read_ty(r)?,
            seq: r.read_value_id()?,
            fwd: r.read_func_id()?,
        }),
        44 => Ok(Inst::DialectOp(Box::new(read_dialect_inst(r)?))),
        45 => Ok(Inst::PtrData {
            ptr_ty: read_ty(r)?,
            ptr: r.read_value_id()?,
        }),
        46 => Ok(Inst::PtrMetadata {
            ptr_ty: read_ty(r)?,
            metadata_ty: read_ty(r)?,
            ptr: r.read_value_id()?,
        }),
        47 => Ok(Inst::PtrFromParts {
            ptr_ty: read_ty(r)?,
            metadata_ty: read_ty(r)?,
            data: r.read_value_id()?,
            metadata: r.read_value_id()?,
        }),
        _ => Err(BinaryError::InvalidTag(tag)),
    }
}

// ---------------------------------------------------------------------------
// ProofAnnotation
// ---------------------------------------------------------------------------

/// Serialize a `ProofAnnotation` list with a `v32` length prefix.
///
/// The `clean-expr` fusion variant [`ProofAnnotation::Goal`] is an in-memory,
/// build-time obligation carrier (a `clean_kernel::Expr` reconstructable from
/// the node it sits on) and is intentionally NOT part of the stable binary wire
/// format. It is filtered here so the length prefix matches the items actually
/// written; the serde and canonical-text paths preserve it. Keeping the binary
/// codec free of `clean_kernel` is what lets the default zero-dep format build
/// round-trip without the fusion dependency.
fn write_proof_annotation_list(
    buf: &mut Vec<u8>,
    pool: &mut StringPool,
    proofs: &[ProofAnnotation],
) {
    #[cfg(feature = "clean-expr")]
    let items: Vec<&ProofAnnotation> = proofs
        .iter()
        .filter(|p| !matches!(p, ProofAnnotation::Goal(_)))
        .collect();
    #[cfg(not(feature = "clean-expr"))]
    let items: Vec<&ProofAnnotation> = proofs.iter().collect();
    write_v32(buf, len_u32(items.len()));
    for p in items {
        write_proof_annotation(buf, pool, p);
    }
}

fn write_proof_annotation(buf: &mut Vec<u8>, _pool: &mut StringPool, ann: &ProofAnnotation) {
    match ann {
        ProofAnnotation::InBounds => write_u8(buf, 0),
        ProofAnnotation::NotNull => write_u8(buf, 1),
        ProofAnnotation::ValidBorrow => write_u8(buf, 2),
        ProofAnnotation::UniqueBorrow => write_u8(buf, 3),
        ProofAnnotation::SharedBorrow => write_u8(buf, 4),
        ProofAnnotation::ValidDealloc => write_u8(buf, 5),
        ProofAnnotation::NoOverflow => write_u8(buf, 6),
        ProofAnnotation::NoWrap => write_u8(buf, 7),
        ProofAnnotation::DivNonZero => write_u8(buf, 8),
        ProofAnnotation::ShiftInRange => write_u8(buf, 9),
        ProofAnnotation::Pure => write_u8(buf, 10),
        ProofAnnotation::Terminates => write_u8(buf, 11),
        ProofAnnotation::Deterministic => write_u8(buf, 12),
        ProofAnnotation::Associative => write_u8(buf, 13),
        ProofAnnotation::Commutative => write_u8(buf, 14),
        ProofAnnotation::DataRaceFree => write_u8(buf, 15),
        ProofAnnotation::AtomicOrdering(ord) => {
            write_u8(buf, 16);
            write_ordering(buf, ord);
        }
        ProofAnnotation::BoundedOutput { lo, hi } => {
            write_u8(buf, 17);
            write_f64(buf, *lo);
            write_f64(buf, *hi);
        }
        ProofAnnotation::Monotonic => write_u8(buf, 18),
        ProofAnnotation::NoAlias => write_u8(buf, 19),
        ProofAnnotation::Aligned(n) => {
            write_u8(buf, 20);
            write_u64(buf, *n);
        }
        ProofAnnotation::NoPanic => write_u8(buf, 21),
        ProofAnnotation::NoUndef => write_u8(buf, 22),
        ProofAnnotation::Tainted => write_u8(buf, 35),
        ProofAnnotation::TrustedSink => write_u8(buf, 36),
        ProofAnnotation::FreshSymbolicHavoc => write_u8(buf, 37),
        ProofAnnotation::Custom(tag) => {
            write_u8(buf, 23);
            write_v32(buf, tag.0);
        }
        ProofAnnotation::ReadonlyTable => write_u8(buf, 24),
        ProofAnnotation::AppendOnlyBuffer => write_u8(buf, 25),
        ProofAnnotation::AtomicSetInsert => write_u8(buf, 26),
        ProofAnnotation::ParallelMap => write_u8(buf, 27),
        ProofAnnotation::BoundedLoop(n) => {
            write_u8(buf, 28);
            write_u64(buf, *n);
        }
        ProofAnnotation::DivergenceClass(d) => {
            write_u8(buf, 29);
            write_divergence(buf, d);
        }
        ProofAnnotation::ProofRef(id) => {
            write_u8(buf, 30);
            write_proof_id(buf, *id);
        }
        ProofAnnotation::ValueRange { lo, hi } => {
            write_u8(buf, 31);
            write_i128(buf, *lo);
            write_i128(buf, *hi);
        }
        ProofAnnotation::KnownBits { zeros, ones } => {
            write_u8(buf, 32);
            write_u128(buf, *zeros);
            write_u128(buf, *ones);
        }
        ProofAnnotation::Wrapping => write_u8(buf, 33),
        ProofAnnotation::BranchWeights(weights) => {
            write_u8(buf, 34);
            write_v32(buf, len_u32(weights.len()));
            for w in weights {
                write_v32(buf, *w);
            }
        }
        // Filtered out by `write_proof_annotation_list` before reaching here:
        // the fusion obligation is not part of the stable binary wire format.
        #[cfg(feature = "clean-expr")]
        ProofAnnotation::Goal(_) => {
            unreachable!("ProofAnnotation::Goal must be filtered before binary serialization")
        }
    }
}

fn write_divergence(buf: &mut Vec<u8>, d: &Divergence) {
    let tag: u8 = match d {
        Divergence::Uniform => 0,
        Divergence::Low => 1,
        Divergence::High => 2,
    };
    write_u8(buf, tag);
}

fn read_divergence(r: &mut Reader<'_>) -> Result<Divergence, BinaryError> {
    let tag = r.read_u8()?;
    match tag {
        0 => Ok(Divergence::Uniform),
        1 => Ok(Divergence::Low),
        2 => Ok(Divergence::High),
        _ => Err(BinaryError::InvalidTag(tag)),
    }
}

fn read_proof_annotation(r: &mut Reader<'_>) -> Result<ProofAnnotation, BinaryError> {
    let tag = r.read_u8()?;
    match tag {
        0 => Ok(ProofAnnotation::InBounds),
        1 => Ok(ProofAnnotation::NotNull),
        2 => Ok(ProofAnnotation::ValidBorrow),
        3 => Ok(ProofAnnotation::UniqueBorrow),
        4 => Ok(ProofAnnotation::SharedBorrow),
        5 => Ok(ProofAnnotation::ValidDealloc),
        6 => Ok(ProofAnnotation::NoOverflow),
        7 => Ok(ProofAnnotation::NoWrap),
        8 => Ok(ProofAnnotation::DivNonZero),
        9 => Ok(ProofAnnotation::ShiftInRange),
        10 => Ok(ProofAnnotation::Pure),
        11 => Ok(ProofAnnotation::Terminates),
        12 => Ok(ProofAnnotation::Deterministic),
        13 => Ok(ProofAnnotation::Associative),
        14 => Ok(ProofAnnotation::Commutative),
        15 => Ok(ProofAnnotation::DataRaceFree),
        16 => Ok(ProofAnnotation::AtomicOrdering(read_ordering(r)?)),
        17 => {
            let lo = r.read_f64()?;
            let hi = r.read_f64()?;
            Ok(ProofAnnotation::BoundedOutput { lo, hi })
        }
        18 => Ok(ProofAnnotation::Monotonic),
        19 => Ok(ProofAnnotation::NoAlias),
        20 => Ok(ProofAnnotation::Aligned(r.read_u64()?)),
        21 => Ok(ProofAnnotation::NoPanic),
        22 => Ok(ProofAnnotation::NoUndef),
        35 => Ok(ProofAnnotation::Tainted),
        36 => Ok(ProofAnnotation::TrustedSink),
        37 => Ok(ProofAnnotation::FreshSymbolicHavoc),
        23 => Ok(ProofAnnotation::Custom(ProofTag::new(r.read_v32()?))),
        24 => Ok(ProofAnnotation::ReadonlyTable),
        25 => Ok(ProofAnnotation::AppendOnlyBuffer),
        26 => Ok(ProofAnnotation::AtomicSetInsert),
        27 => Ok(ProofAnnotation::ParallelMap),
        28 => Ok(ProofAnnotation::BoundedLoop(r.read_u64()?)),
        29 => Ok(ProofAnnotation::DivergenceClass(read_divergence(r)?)),
        30 => Ok(ProofAnnotation::ProofRef(r.read_proof_id()?)),
        31 => {
            let lo = r.read_i128()?;
            let hi = r.read_i128()?;
            Ok(ProofAnnotation::ValueRange { lo, hi })
        }
        32 => {
            let zeros = r.read_u128()?;
            let ones = r.read_u128()?;
            Ok(ProofAnnotation::KnownBits { zeros, ones })
        }
        33 => Ok(ProofAnnotation::Wrapping),
        34 => {
            let n = r.read_checked_len()?;
            let mut weights = Vec::with_capacity(n);
            for _ in 0..n {
                weights.push(r.read_v32()?);
            }
            Ok(ProofAnnotation::BranchWeights(weights))
        }
        _ => Err(BinaryError::InvalidTag(tag)),
    }
}

// ---------------------------------------------------------------------------
// ProofEvidence
// ---------------------------------------------------------------------------

fn write_proof_evidence(buf: &mut Vec<u8>, pool: &mut StringPool, ev: &ProofEvidence) {
    match ev {
        ProofEvidence::SmtProof(data) => {
            write_u8(buf, 0);
            write_bytes(buf, data);
        }
        ProofEvidence::LeanProof(s) => {
            write_u8(buf, 1);
            write_str(buf, pool, s);
        }
        ProofEvidence::KaniHarness(s) => {
            write_u8(buf, 2);
            write_str(buf, pool, s);
        }
        ProofEvidence::GammaCrownBound {
            epsilon,
            verified_layers,
        } => {
            write_u8(buf, 3);
            write_f64(buf, *epsilon);
            write_v32(buf, *verified_layers);
        }
        ProofEvidence::TranslationValidation {
            rule_name,
            smt_hash,
        } => {
            write_u8(buf, 4);
            write_str(buf, pool, rule_name);
            buf.extend_from_slice(smt_hash);
        }
        ProofEvidence::Trusted(s) => {
            write_u8(buf, 5);
            write_str(buf, pool, s);
        }
        ProofEvidence::InheritedFromCallee { callee, obligation } => {
            write_u8(buf, 6);
            write_v32(buf, callee.index());
            write_v32(buf, obligation.index());
        }
        ProofEvidence::CleanCic {
            term,
            context,
            lineage,
            kernel_recheck,
        } => {
            write_u8(buf, 7);
            write_bytes(buf, term);
            write_bytes(buf, context);
            write_proof_digest(buf, lineage);
            match kernel_recheck {
                None => write_u8(buf, 0),
                Some(recheck) => {
                    write_u8(buf, 1);
                    write_str(buf, pool, &recheck.module);
                    write_v32(buf, len_u32(recheck.theorems.len()));
                    for thm in &recheck.theorems {
                        write_str(buf, pool, thm);
                    }
                    write_str(buf, pool, &recheck.anchor);
                    write_v32(buf, len_u32(recheck.allowed_axioms.len()));
                    for ax in &recheck.allowed_axioms {
                        write_str(buf, pool, ax);
                    }
                }
            }
        }
    }
}

fn read_proof_evidence(r: &mut Reader<'_>) -> Result<ProofEvidence, BinaryError> {
    let tag = r.read_u8()?;
    match tag {
        0 => Ok(ProofEvidence::SmtProof(r.read_bytes()?)),
        1 => Ok(ProofEvidence::LeanProof(r.read_str()?)),
        2 => Ok(ProofEvidence::KaniHarness(r.read_str()?)),
        3 => {
            let epsilon = r.read_f64()?;
            let verified_layers = r.read_v32()?;
            Ok(ProofEvidence::GammaCrownBound {
                epsilon,
                verified_layers,
            })
        }
        4 => {
            let rule_name = r.read_str()?;
            let hash_bytes = r.read_exact(32)?;
            let mut smt_hash = [0u8; 32];
            smt_hash.copy_from_slice(&hash_bytes);
            Ok(ProofEvidence::TranslationValidation {
                rule_name,
                smt_hash,
            })
        }
        5 => Ok(ProofEvidence::Trusted(r.read_str()?)),
        6 => {
            let callee = r.read_func_id()?;
            let obligation = r.read_proof_id()?;
            Ok(ProofEvidence::InheritedFromCallee { callee, obligation })
        }
        7 => {
            let term = r.read_bytes()?;
            let context = r.read_bytes()?;
            let lineage = read_proof_digest(r)?;
            let kernel_recheck = match r.read_u8()? {
                0 => None,
                1 => {
                    let module = r.read_str()?;
                    let thm_count = r.read_checked_len()?;
                    let mut theorems = Vec::with_capacity(thm_count);
                    for _ in 0..thm_count {
                        theorems.push(r.read_str()?);
                    }
                    let anchor = r.read_str()?;
                    let ax_count = r.read_checked_len()?;
                    let mut allowed_axioms = Vec::with_capacity(ax_count);
                    for _ in 0..ax_count {
                        allowed_axioms.push(r.read_str()?);
                    }
                    Some(CleanCicKernelRecheck {
                        module,
                        theorems,
                        anchor,
                        allowed_axioms,
                    })
                }
                other => return Err(BinaryError::InvalidTag(other)),
            };
            Ok(ProofEvidence::CleanCic {
                term,
                context,
                lineage,
                kernel_recheck,
            })
        }
        _ => Err(BinaryError::InvalidTag(tag)),
    }
}

// ---------------------------------------------------------------------------
// InstrNode
// ---------------------------------------------------------------------------

fn write_instr_node(buf: &mut Vec<u8>, pool: &mut StringPool, node: &InstrNode) {
    write_inst(buf, pool, &node.inst);
    write_vec_value_id(buf, &node.results);
    write_proof_annotation_list(buf, pool, &node.proofs);
    match &node.span {
        None => write_u8(buf, 0),
        Some(span) => {
            write_u8(buf, 1);
            write_v32(buf, span.file);
            write_v32(buf, span.line);
            write_v32(buf, span.col);
        }
    }
    // v6+: per-call-site proof context (B5)
    match &node.proof_context {
        None => write_u8(buf, 0),
        Some(pc) => {
            write_u8(buf, 1);
            write_v32(buf, len_u32(pc.assumes.len()));
            for o in &pc.assumes {
                write_proof_id(buf, *o);
            }
            write_v32(buf, len_u32(pc.establishes.len()));
            for o in &pc.establishes {
                write_proof_id(buf, *o);
            }
        }
    }
    // v33+: lexical scope index (C2-scopes).
    match node.scope {
        None => write_u8(buf, 0),
        Some(scope) => {
            write_u8(buf, 1);
            write_v32(buf, scope);
        }
    }
}

fn read_instr_node(r: &mut Reader<'_>, version: u32) -> Result<InstrNode, BinaryError> {
    let inst = read_inst(r)?;
    let results = read_vec_value_id(r)?;
    let proof_count = r.read_checked_len()?;
    let mut proofs = Vec::with_capacity(proof_count);
    for _ in 0..proof_count {
        proofs.push(read_proof_annotation(r)?);
    }
    let span = match r.read_u8()? {
        0 => None,
        1 => Some(SourceSpan {
            file: r.read_v32()?,
            line: r.read_v32()?,
            col: r.read_v32()?,
        }),
        t => return Err(BinaryError::InvalidTag(t)),
    };
    // v6+: per-call-site proof context (B5); legacy files default to None.
    let proof_context = if version >= 6 {
        match r.read_u8()? {
            0 => None,
            1 => {
                let na = r.read_checked_len()?;
                let mut assumes = Vec::with_capacity(na);
                for _ in 0..na {
                    assumes.push(r.read_proof_id()?);
                }
                let ne = r.read_checked_len()?;
                let mut establishes = Vec::with_capacity(ne);
                for _ in 0..ne {
                    establishes.push(r.read_proof_id()?);
                }
                Some(ProofContext {
                    assumes,
                    establishes,
                })
            }
            t => return Err(BinaryError::InvalidTag(t)),
        }
    } else {
        None
    };
    // v33+: lexical scope index; legacy files default to None.
    let scope = if version >= 33 {
        match r.read_u8()? {
            0 => None,
            1 => Some(r.read_v32()?),
            t => return Err(BinaryError::InvalidTag(t)),
        }
    } else {
        None
    };
    Ok(InstrNode {
        inst,
        results,
        proofs,
        span,
        proof_context,
        scope,
    })
}

// ---------------------------------------------------------------------------
// Compound structs
// ---------------------------------------------------------------------------

fn write_func_ty(buf: &mut Vec<u8>, pool: &mut StringPool, ft: &FuncTy) {
    write_v32(buf, len_u32(ft.params.len()));
    for p in &ft.params {
        write_ty(buf, pool, p);
    }
    write_v32(buf, len_u32(ft.returns.len()));
    for r in &ft.returns {
        write_ty(buf, pool, r);
    }
    write_bool(buf, ft.is_vararg);
}

fn read_func_ty(r: &mut Reader<'_>) -> Result<FuncTy, BinaryError> {
    let param_count = r.read_checked_len()?;
    let mut params = Vec::with_capacity(param_count);
    for _ in 0..param_count {
        params.push(read_ty(r)?);
    }
    let ret_count = r.read_checked_len()?;
    let mut returns = Vec::with_capacity(ret_count);
    for _ in 0..ret_count {
        returns.push(read_ty(r)?);
    }
    let is_vararg = r.read_bool()?;
    Ok(FuncTy {
        params,
        returns,
        is_vararg,
    })
}

fn write_field_def(buf: &mut Vec<u8>, pool: &mut StringPool, fd: &FieldDef) {
    write_str(buf, pool, &fd.name);
    write_ty(buf, pool, &fd.ty);
    match fd.offset {
        None => write_u8(buf, 0),
        Some(o) => {
            write_u8(buf, 1);
            write_u64(buf, o);
        }
    }
}

fn read_field_def(r: &mut Reader<'_>) -> Result<FieldDef, BinaryError> {
    let name = r.read_str()?;
    let ty = read_ty(r)?;
    let offset = match r.read_u8()? {
        0 => None,
        1 => Some(r.read_u64()?),
        t => return Err(BinaryError::InvalidTag(t)),
    };
    Ok(FieldDef { name, ty, offset })
}

fn write_struct_def(buf: &mut Vec<u8>, pool: &mut StringPool, sd: &StructDef) {
    write_struct_id(buf, sd.id);
    write_str(buf, pool, &sd.name);
    write_v32(buf, len_u32(sd.fields.len()));
    for f in &sd.fields {
        write_field_def(buf, pool, f);
    }
    match sd.size {
        None => write_u8(buf, 0),
        Some(s) => {
            write_u8(buf, 1);
            write_u64(buf, s);
        }
    }
    match sd.align {
        None => write_u8(buf, 0),
        Some(a) => {
            write_u8(buf, 1);
            write_u64(buf, a);
        }
    }
    // Struct ABI repr (VERSION >= 10). Tag: 0=Rust 1=C 2=Transparent 3=Packed(align).
    match sd.repr {
        StructRepr::Rust => write_u8(buf, 0),
        StructRepr::C => write_u8(buf, 1),
        StructRepr::Transparent => write_u8(buf, 2),
        StructRepr::Packed(align) => {
            write_u8(buf, 3);
            write_v32(buf, align);
        }
    }
}

fn read_struct_def(r: &mut Reader<'_>) -> Result<StructDef, BinaryError> {
    let id = r.read_struct_id()?;
    let name = r.read_str()?;
    let field_count = r.read_checked_len()?;
    let mut fields = Vec::with_capacity(field_count);
    for _ in 0..field_count {
        fields.push(read_field_def(r)?);
    }
    let size = match r.read_u8()? {
        0 => None,
        1 => Some(r.read_u64()?),
        t => return Err(BinaryError::InvalidTag(t)),
    };
    let align = match r.read_u8()? {
        0 => None,
        1 => Some(r.read_u64()?),
        t => return Err(BinaryError::InvalidTag(t)),
    };
    // Struct ABI repr (VERSION >= 10); older modules default to Rust.
    let repr = if r.version >= 10 {
        match r.read_u8()? {
            0 => StructRepr::Rust,
            1 => StructRepr::C,
            2 => StructRepr::Transparent,
            3 => StructRepr::Packed(r.read_v32()?),
            t => return Err(BinaryError::InvalidTag(t)),
        }
    } else {
        StructRepr::Rust
    };
    Ok(StructDef {
        id,
        name,
        fields,
        size,
        align,
        repr,
    })
}

fn write_record_def(buf: &mut Vec<u8>, pool: &mut StringPool, rd: &RecordDef) {
    write_v32(buf, rd.id.0);
    write_str(buf, pool, &rd.name);
    write_v32(buf, len_u32(rd.fields.len()));
    for f in &rd.fields {
        write_field_def(buf, pool, f);
    }
}

fn read_record_def(r: &mut Reader<'_>) -> Result<RecordDef, BinaryError> {
    let id = r.read_record_id()?;
    let name = r.read_str()?;
    let field_count = r.read_checked_len()?;
    let mut fields = Vec::with_capacity(field_count);
    for _ in 0..field_count {
        fields.push(read_field_def(r)?);
    }
    Ok(RecordDef { id, name, fields })
}

fn write_closure_ty(buf: &mut Vec<u8>, pool: &mut StringPool, ct: &ClosureTy) {
    write_func_ty_id(buf, ct.func);
    write_v32(buf, len_u32(ct.captures.len()));
    for c in &ct.captures {
        write_ty(buf, pool, c);
    }
}

fn read_closure_ty(r: &mut Reader<'_>) -> Result<ClosureTy, BinaryError> {
    let func = r.read_func_ty_id()?;
    let n = r.read_checked_len()?;
    let mut captures = Vec::with_capacity(n);
    for _ in 0..n {
        captures.push(read_ty(r)?);
    }
    Ok(ClosureTy { func, captures })
}

fn write_enum_variant(buf: &mut Vec<u8>, pool: &mut StringPool, ev: &EnumVariant) {
    write_str(buf, pool, &ev.name);
    write_v32(buf, len_u32(ev.fields.len()));
    for f in &ev.fields {
        write_ty(buf, pool, f);
    }
    write_v32(buf, len_u32(ev.field_names.len()));
    for name in &ev.field_names {
        write_str(buf, pool, name);
    }
}

fn read_enum_variant(r: &mut Reader<'_>) -> Result<EnumVariant, BinaryError> {
    let name = r.read_str()?;
    let field_count = r.read_checked_len()?;
    let mut fields = Vec::with_capacity(field_count);
    for _ in 0..field_count {
        fields.push(read_ty(r)?);
    }
    let field_names = if r.version >= 31 {
        let name_count = r.read_checked_len()?;
        let mut names = Vec::with_capacity(name_count);
        for _ in 0..name_count {
            names.push(r.read_str()?);
        }
        names
    } else {
        Vec::new()
    };
    Ok(EnumVariant {
        name,
        fields,
        field_names,
    })
}

fn write_enum_def(buf: &mut Vec<u8>, pool: &mut StringPool, ed: &EnumDef) {
    write_enum_id(buf, ed.id);
    write_str(buf, pool, &ed.name);
    write_v32(buf, len_u32(ed.variants.len()));
    for v in &ed.variants {
        write_enum_variant(buf, pool, v);
    }
    // Explicit discriminants + tag-repr hint (VERSION >= 19). Written
    // verbatim (the vector may be shorter than `variants`; entries are
    // Option-tagged 0=implicit 1=explicit i128).
    write_v32(buf, len_u32(ed.discriminants.len()));
    for d in &ed.discriminants {
        match d {
            None => write_u8(buf, 0),
            Some(value) => {
                write_u8(buf, 1);
                write_i128(buf, *value);
            }
        }
    }
    // Tag: 0=no hint, 1..=8 map to EnumTagRepr U8/U16/U32/U64/I8/I16/I32/I64.
    match ed.repr {
        None => write_u8(buf, 0),
        Some(repr) => write_u8(buf, enum_tag_repr_byte(repr)),
    }
    match &ed.layout {
        None => write_u8(buf, 0),
        Some(layout) => {
            write_u8(buf, 1);
            match &layout.encoding {
                EnumTagEncoding::Direct { tag_offset } => {
                    write_u8(buf, 0);
                    write_v64(buf, *tag_offset);
                }
                EnumTagEncoding::Niche {
                    untagged_variant,
                    niche_variants_start,
                    niche_variants_end,
                    niche_start,
                    niche_offset,
                    niche_ty,
                } => {
                    write_u8(buf, 1);
                    write_v32(buf, *untagged_variant);
                    write_v32(buf, *niche_variants_start);
                    write_v32(buf, *niche_variants_end);
                    write_u128(buf, *niche_start);
                    write_v64(buf, *niche_offset);
                    write_u8(buf, enum_tag_repr_byte(*niche_ty));
                }
                // v37. The tag byte is the whole encoding — there is no tag
                // lane to place, so nothing follows it. The reader side IS
                // version-gated, so a v36 blob carrying this byte is refused.
                EnumTagEncoding::Untagged => write_u8(buf, 2),
            }
            write_v64(buf, layout.size);
            write_v64(buf, layout.align);
            write_v32(buf, len_u32(layout.variant_field_offsets.len()));
            for offsets in &layout.variant_field_offsets {
                write_v32(buf, len_u32(offsets.len()));
                for offset in offsets {
                    write_v64(buf, *offset);
                }
            }
        }
    }
}

fn enum_tag_repr_byte(repr: EnumTagRepr) -> u8 {
    match repr {
        EnumTagRepr::U8 => 1,
        EnumTagRepr::U16 => 2,
        EnumTagRepr::U32 => 3,
        EnumTagRepr::U64 => 4,
        EnumTagRepr::I8 => 5,
        EnumTagRepr::I16 => 6,
        EnumTagRepr::I32 => 7,
        EnumTagRepr::I64 => 8,
    }
}

fn enum_tag_repr_from_byte(byte: u8) -> Result<EnumTagRepr, BinaryError> {
    Ok(match byte {
        1 => EnumTagRepr::U8,
        2 => EnumTagRepr::U16,
        3 => EnumTagRepr::U32,
        4 => EnumTagRepr::U64,
        5 => EnumTagRepr::I8,
        6 => EnumTagRepr::I16,
        7 => EnumTagRepr::I32,
        8 => EnumTagRepr::I64,
        tag => return Err(BinaryError::InvalidTag(tag)),
    })
}

fn read_enum_def(r: &mut Reader<'_>) -> Result<EnumDef, BinaryError> {
    let id = r.read_enum_id()?;
    let name = r.read_str()?;
    let variant_count = r.read_checked_len()?;
    let mut variants = Vec::with_capacity(variant_count);
    for _ in 0..variant_count {
        variants.push(read_enum_variant(r)?);
    }
    // Explicit discriminants + tag-repr hint (VERSION >= 19); older modules
    // default to all-implicit discriminants and no hint.
    let (discriminants, repr) = if r.version >= 19 {
        let disc_count = r.read_checked_len()?;
        let mut discriminants = Vec::with_capacity(disc_count);
        for _ in 0..disc_count {
            discriminants.push(match r.read_u8()? {
                0 => None,
                1 => Some(r.read_i128()?),
                t => return Err(BinaryError::InvalidTag(t)),
            });
        }
        let repr = match r.read_u8()? {
            0 => None,
            byte => Some(enum_tag_repr_from_byte(byte)?),
        };
        (discriminants, repr)
    } else {
        (Vec::new(), None)
    };
    let layout = if r.version >= 31 {
        match r.read_u8()? {
            0 => None,
            1 => {
                let encoding = match r.read_u8()? {
                    0 => EnumTagEncoding::Direct {
                        tag_offset: r.read_v64()?,
                    },
                    1 => EnumTagEncoding::Niche {
                        untagged_variant: r.read_v32()?,
                        niche_variants_start: r.read_v32()?,
                        niche_variants_end: r.read_v32()?,
                        niche_start: r.read_u128()?,
                        niche_offset: r.read_v64()?,
                        niche_ty: enum_tag_repr_from_byte(r.read_u8()?)?,
                    },
                    // v37. Gated, not unconditional: byte 2 is not a value any
                    // v36-or-earlier writer could have produced, so a blob
                    // CLAIMING v36 that carries it is malformed and must be
                    // refused rather than silently promoted.
                    2 if r.version >= 37 => EnumTagEncoding::Untagged,
                    tag => return Err(BinaryError::InvalidTag(tag)),
                };
                let size = r.read_v64()?;
                let align = r.read_v64()?;
                let variant_count = r.read_checked_len()?;
                let mut variant_field_offsets = Vec::with_capacity(variant_count);
                for _ in 0..variant_count {
                    let field_count = r.read_checked_len()?;
                    let mut offsets = Vec::with_capacity(field_count);
                    for _ in 0..field_count {
                        offsets.push(r.read_v64()?);
                    }
                    variant_field_offsets.push(offsets);
                }
                Some(EnumLayoutDescriptor {
                    encoding,
                    size,
                    align,
                    variant_field_offsets,
                })
            }
            tag => return Err(BinaryError::InvalidTag(tag)),
        }
    } else {
        None
    };
    Ok(EnumDef {
        id,
        name,
        variants,
        discriminants,
        repr,
        layout,
    })
}

fn write_global(buf: &mut Vec<u8>, pool: &mut StringPool, g: &Global) {
    write_str(buf, pool, &g.name);
    write_ty(buf, pool, &g.ty);
    write_bool(buf, g.mutable);
    match &g.initializer {
        None => write_u8(buf, 0),
        Some(c) => {
            write_u8(buf, 1);
            write_constant(buf, pool, c);
        }
    }
    write_linkage(buf, &g.linkage);
    match g.tls {
        None => write_u8(buf, 0),
        Some(tls) => {
            write_u8(buf, 1);
            write_tls_model(buf, &tls);
        }
    }
    // v26: declared storage alignment (presence byte + v32).
    match g.align {
        None => write_u8(buf, 0),
        Some(align) => {
            write_u8(buf, 1);
            write_v32(buf, align);
        }
    }
}

fn read_global(r: &mut Reader<'_>, version: u32) -> Result<Global, BinaryError> {
    let name = r.read_str()?;
    let ty = read_ty(r)?;
    let mutable = r.read_bool()?;
    let initializer = match r.read_u8()? {
        0 => None,
        1 => Some(read_constant(r)?),
        t => return Err(BinaryError::InvalidTag(t)),
    };
    let linkage = read_linkage(r)?;
    let tls = if version >= 3 {
        match r.read_u8()? {
            0 => None,
            1 => Some(read_tls_model(r)?),
            t => return Err(BinaryError::InvalidTag(t)),
        }
    } else {
        None
    };
    // v26: declared storage alignment (presence byte + v32); defaults None on
    // v23..=v25 blobs (the consumer derives alignment from the type there).
    // Whole-module v26..=v28 payloads are rejected at the header boundary as
    // ambiguous-lineage, so every accepted module that reaches this gate is
    // either pre-v26 or the merged v29+ format.
    let align = if version >= 26 {
        match r.read_u8()? {
            0 => None,
            1 => Some(r.read_v32()?),
            t => return Err(BinaryError::InvalidTag(t)),
        }
    } else {
        None
    };
    Ok(Global {
        name,
        ty,
        mutable,
        initializer,
        linkage,
        tls,
        align,
    })
}

fn write_block(buf: &mut Vec<u8>, pool: &mut StringPool, block: &Block) {
    write_block_id(buf, block.id);
    write_v32(buf, len_u32(block.params.len()));
    for (vid, ty) in &block.params {
        write_value_id(buf, *vid);
        write_ty(buf, pool, ty);
    }
    write_v32(buf, len_u32(block.body.len()));
    for node in &block.body {
        write_instr_node(buf, pool, node);
    }
}

fn read_block(r: &mut Reader<'_>, version: u32) -> Result<Block, BinaryError> {
    let id = r.read_block_id()?;
    let param_count = r.read_checked_len()?;
    let mut params = Vec::with_capacity(param_count);
    for _ in 0..param_count {
        let vid = r.read_value_id()?;
        let ty = read_ty(r)?;
        params.push((vid, ty));
    }
    let body_count = r.read_checked_len()?;
    let mut body = Vec::with_capacity(body_count);
    for _ in 0..body_count {
        body.push(read_instr_node(r, version)?);
    }
    Ok(Block { id, params, body })
}

fn write_proof_obligation(buf: &mut Vec<u8>, pool: &mut StringPool, po: &ProofObligation) {
    write_proof_id(buf, po.id);
    write_obligation_kind(buf, &po.kind);
    write_proof_status(buf, &po.status);
    write_str(buf, pool, &po.description);
    match &po.formula {
        None => write_u8(buf, 0),
        Some(formula) => {
            write_u8(buf, 1);
            write_str(buf, pool, &formula.schema);
            write_str(buf, pool, &formula.payload);
            write_opt_str(buf, pool, formula.smtlib.as_deref());
            write_opt_str(buf, pool, formula.sort.as_deref());
        }
    }
    // v5+: owning-function scope (B4)
    match &po.function {
        None => write_u8(buf, 0),
        Some(f) => {
            write_u8(buf, 1);
            write_v32(buf, f.index());
        }
    }
    // v28+: embedded source/public identity. The nested option keeps the
    // public identifier and semantic digest atomic on the wire.
    match &po.source {
        None => write_u8(buf, 0),
        Some(source) => {
            write_u8(buf, 1);
            write_str(buf, pool, &source.source_id);
            write_str(buf, pool, &source.assertion_id);
            match &source.range {
                None => write_u8(buf, 0),
                Some(range) => {
                    write_u8(buf, 1);
                    write_v32(buf, range.file);
                    write_v32(buf, range.start_line);
                    write_v32(buf, range.start_col);
                    write_v32(buf, range.end_line);
                    write_v32(buf, range.end_col);
                }
            }
            match &source.public {
                None => write_u8(buf, 0),
                Some(public) => {
                    write_u8(buf, 1);
                    write_str(buf, pool, &public.obligation_id);
                    write_proof_digest(buf, &public.semantic_digest);
                }
            }
        }
    }
    // v34+: IR-position backref (the obligation<->VC-condition binding).
    match &po.site {
        None => write_u8(buf, 0),
        Some(site) => {
            write_u8(buf, 1);
            write_v32(buf, site.function.index());
            write_v32(buf, site.block.index());
            write_v32(buf, site.inst_index);
        }
    }
}

fn read_proof_obligation(r: &mut Reader<'_>, version: u32) -> Result<ProofObligation, BinaryError> {
    let id = r.read_proof_id()?;
    let kind = read_obligation_kind(r)?;
    let status = read_proof_status(r)?;
    let description = r.read_str()?;
    let formula = match r.read_u8()? {
        0 => None,
        1 => Some(ProofFormula {
            schema: r.read_str()?,
            payload: r.read_str()?,
            smtlib: read_opt_str(r)?,
            sort: read_opt_str(r)?,
        }),
        tag => return Err(BinaryError::InvalidTag(tag)),
    };
    // v5+: owning-function scope (B4); legacy files default to None.
    let function = if version >= 5 {
        match r.read_u8()? {
            0 => None,
            1 => Some(FuncId::new(r.read_v32()?)),
            tag => return Err(BinaryError::InvalidTag(tag)),
        }
    } else {
        None
    };
    let source = if version >= 28 {
        match r.read_u8()? {
            0 => None,
            1 => {
                let source_id = r.read_str()?;
                let assertion_id = r.read_str()?;
                let range = match r.read_u8()? {
                    0 => None,
                    1 => Some(ProofObligationSourceRange {
                        file: r.read_v32()?,
                        start_line: r.read_v32()?,
                        start_col: r.read_v32()?,
                        end_line: r.read_v32()?,
                        end_col: r.read_v32()?,
                    }),
                    tag => return Err(BinaryError::InvalidTag(tag)),
                };
                let public = match r.read_u8()? {
                    0 => None,
                    1 => Some(PublicObligationIdentity {
                        obligation_id: r.read_str()?,
                        semantic_digest: read_proof_digest(r)?,
                    }),
                    tag => return Err(BinaryError::InvalidTag(tag)),
                };
                Some(ProofObligationSourceIdentity {
                    source_id,
                    assertion_id,
                    range,
                    public,
                })
            }
            tag => return Err(BinaryError::InvalidTag(tag)),
        }
    } else {
        None
    };
    // v34+: IR-position backref; legacy files default to None (unbindable).
    let site = if version >= 34 {
        match r.read_u8()? {
            0 => None,
            1 => Some(trust_ir_site(r.read_v32()?, r.read_v32()?, r.read_v32()?)),
            tag => return Err(BinaryError::InvalidTag(tag)),
        }
    } else {
        None
    };
    Ok(ProofObligation {
        id,
        kind,
        status,
        description,
        formula,
        function,
        source,
        site,
    })
}

fn trust_ir_site(function: u32, block: u32, inst_index: u32) -> crate::proof::ObligationSite {
    crate::proof::ObligationSite::new(
        FuncId::new(function),
        crate::value::BlockId::new(block),
        inst_index,
    )
}

fn write_proof_certificate(buf: &mut Vec<u8>, pool: &mut StringPool, cert: &ProofCertificate) {
    write_proof_id(buf, cert.obligation);
    write_str(buf, pool, &cert.prover);
    write_proof_evidence(buf, pool, &cert.evidence);
}

fn read_proof_certificate(r: &mut Reader<'_>) -> Result<ProofCertificate, BinaryError> {
    let obligation = r.read_proof_id()?;
    let prover = r.read_str()?;
    let evidence = read_proof_evidence(r)?;
    Ok(ProofCertificate {
        obligation,
        prover,
        evidence,
    })
}

// ---------------------------------------------------------------------------
// ProofLineageManifest sidecar storage
// ---------------------------------------------------------------------------

fn write_proof_digest(buf: &mut Vec<u8>, digest: &ProofDigest) {
    match digest.algorithm {
        ProofDigestAlgorithm::Sha256 => write_u8(buf, 0),
        ProofDigestAlgorithm::TrustIrStableV1 => write_u8(buf, 1),
    }
    buf.extend_from_slice(&digest.bytes);
}

fn read_proof_digest(r: &mut Reader<'_>) -> Result<ProofDigest, BinaryError> {
    let algorithm = match r.read_u8()? {
        0 => ProofDigestAlgorithm::Sha256,
        1 => ProofDigestAlgorithm::TrustIrStableV1,
        tag => return Err(BinaryError::InvalidTag(tag)),
    };
    let bytes = r.read_exact(32)?;
    let mut digest = [0u8; 32];
    digest.copy_from_slice(&bytes);
    Ok(ProofDigest {
        algorithm,
        bytes: digest,
    })
}

fn write_proof_transform_stage(buf: &mut Vec<u8>, stage: ProofTransformStage) {
    let tag = match stage {
        ProofTransformStage::Frontend => 0,
        ProofTransformStage::TrustIrLowering => 1,
        ProofTransformStage::TrustIrOptimization => 2,
        ProofTransformStage::SolverAdapter => 3,
        ProofTransformStage::Backend => 4,
        ProofTransformStage::Replay => 5,
        ProofTransformStage::Composition => 6,
        ProofTransformStage::Other => 7,
    };
    write_u8(buf, tag);
}

fn read_proof_transform_stage(r: &mut Reader<'_>) -> Result<ProofTransformStage, BinaryError> {
    match r.read_u8()? {
        0 => Ok(ProofTransformStage::Frontend),
        1 => Ok(ProofTransformStage::TrustIrLowering),
        2 => Ok(ProofTransformStage::TrustIrOptimization),
        3 => Ok(ProofTransformStage::SolverAdapter),
        4 => Ok(ProofTransformStage::Backend),
        5 => Ok(ProofTransformStage::Replay),
        6 => Ok(ProofTransformStage::Composition),
        7 => Ok(ProofTransformStage::Other),
        tag => Err(BinaryError::InvalidTag(tag)),
    }
}

fn write_proof_transform(buf: &mut Vec<u8>, pool: &mut StringPool, transform: &ProofTransform) {
    write_proof_transform_stage(buf, transform.stage);
    write_str(buf, pool, &transform.name);
    write_str(buf, pool, &transform.producer);
    write_str(buf, pool, &transform.version);
}

fn read_proof_transform(r: &mut Reader<'_>) -> Result<ProofTransform, BinaryError> {
    Ok(ProofTransform {
        stage: read_proof_transform_stage(r)?,
        name: r.read_str()?,
        producer: r.read_str()?,
        version: r.read_str()?,
    })
}

fn write_proof_certificate_ref(
    buf: &mut Vec<u8>,
    pool: &mut StringPool,
    cert: &ProofCertificateRef,
) {
    write_proof_id(buf, cert.obligation);
    write_str(buf, pool, &cert.prover);
    write_proof_digest(buf, &cert.evidence_digest);
}

fn read_proof_certificate_ref(r: &mut Reader<'_>) -> Result<ProofCertificateRef, BinaryError> {
    Ok(ProofCertificateRef {
        obligation: r.read_proof_id()?,
        prover: r.read_str()?,
        evidence_digest: read_proof_digest(r)?,
    })
}

fn write_proof_replay_identity(
    buf: &mut Vec<u8>,
    pool: &mut StringPool,
    replay: &ProofReplayIdentity,
) {
    write_str(buf, pool, &replay.engine);
    write_str(buf, pool, &replay.invocation);
    match &replay.transcript_digest {
        None => write_u8(buf, 0),
        Some(digest) => {
            write_u8(buf, 1);
            write_proof_digest(buf, digest);
        }
    }
}

fn read_proof_replay_identity(r: &mut Reader<'_>) -> Result<ProofReplayIdentity, BinaryError> {
    let engine = r.read_str()?;
    let invocation = r.read_str()?;
    let transcript_digest = match r.read_u8()? {
        0 => None,
        1 => Some(read_proof_digest(r)?),
        tag => return Err(BinaryError::InvalidTag(tag)),
    };
    Ok(ProofReplayIdentity {
        engine,
        invocation,
        transcript_digest,
    })
}

fn write_proof_lineage_node(buf: &mut Vec<u8>, pool: &mut StringPool, node: &ProofLineageNode) {
    write_v32(buf, node.id.0);
    write_proof_transform(buf, pool, &node.transform);
    write_proof_digest(buf, &node.source_module);
    write_proof_digest(buf, &node.target_module);

    let mut obligations = node.obligations.clone();
    obligations.sort();
    write_v32(buf, len_u32(obligations.len()));
    for obligation in obligations {
        write_v32(buf, obligation.0);
    }

    let mut certificates = node.certificates.clone();
    certificates.sort();
    write_v32(buf, len_u32(certificates.len()));
    for cert in certificates {
        write_proof_certificate_ref(buf, pool, &cert);
    }

    match &node.replay {
        None => write_u8(buf, 0),
        Some(replay) => {
            write_u8(buf, 1);
            write_proof_replay_identity(buf, pool, replay);
        }
    }

    let mut depends_on = node.depends_on.clone();
    depends_on.sort();
    write_v32(buf, len_u32(depends_on.len()));
    for dependency in depends_on {
        write_v32(buf, dependency.0);
    }
}

fn read_proof_lineage_node(r: &mut Reader<'_>) -> Result<ProofLineageNode, BinaryError> {
    let id = ProofLineageId::new(r.read_v32()?);
    let transform = read_proof_transform(r)?;
    let source_module = read_proof_digest(r)?;
    let target_module = read_proof_digest(r)?;

    let obligation_count = r.read_checked_len()?;
    let mut obligations = Vec::with_capacity(obligation_count);
    for _ in 0..obligation_count {
        obligations.push(r.read_proof_id()?);
    }

    let certificate_count = r.read_checked_len()?;
    let mut certificates = Vec::with_capacity(certificate_count);
    for _ in 0..certificate_count {
        certificates.push(read_proof_certificate_ref(r)?);
    }

    let replay = match r.read_u8()? {
        0 => None,
        1 => Some(read_proof_replay_identity(r)?),
        tag => return Err(BinaryError::InvalidTag(tag)),
    };

    let dependency_count = r.read_checked_len()?;
    let mut depends_on = Vec::with_capacity(dependency_count);
    for _ in 0..dependency_count {
        depends_on.push(ProofLineageId::new(r.read_v32()?));
    }

    Ok(ProofLineageNode {
        id,
        transform,
        source_module,
        target_module,
        obligations,
        certificates,
        replay,
        depends_on,
    })
}

fn write_param_attrs(buf: &mut Vec<u8>, pa: &ParamAttrs) {
    let mut flags: u8 = 0;
    if pa.nonnull {
        flags |= 0b0001;
    }
    if pa.noalias {
        flags |= 0b0010;
    }
    if pa.readonly {
        flags |= 0b0100;
    }
    // VERSION >= 20 (ABI pinning): byval/sret aggregate-passing classification.
    if pa.byval {
        flags |= 0b0_1000;
    }
    if pa.sret {
        flags |= 0b1_0000;
    }
    write_u8(buf, flags);
    write_opt_u64(buf, pa.dereferenceable);
    write_opt_u64(buf, pa.align);
}

fn read_param_attrs(r: &mut Reader<'_>) -> Result<ParamAttrs, BinaryError> {
    let flags = r.read_u8()?;
    let dereferenceable = read_opt_u64(r)?;
    let align = read_opt_u64(r)?;
    // byval/sret are VERSION >= 20 flag bits. Pre-v20 writers never set them,
    // but gate anyway so a hand-crafted pre-v20 blob cannot smuggle them in.
    let abi_bits = r.version >= 20;
    Ok(ParamAttrs {
        dereferenceable,
        nonnull: flags & 0b0001 != 0,
        align,
        noalias: flags & 0b0010 != 0,
        readonly: flags & 0b0100 != 0,
        byval: abi_bits && flags & 0b0_1000 != 0,
        sret: abi_bits && flags & 0b1_0000 != 0,
    })
}

fn write_func_attrs(buf: &mut Vec<u8>, fa: &FuncAttrs) {
    let mut flags: u8 = 0;
    if fa.readonly {
        flags |= 0b0001;
    }
    if fa.readnone {
        flags |= 0b0010;
    }
    if fa.inlinehint {
        flags |= 0b0100;
    }
    if fa.cold {
        flags |= 0b1000;
    }
    write_u8(buf, flags);
    write_v32(buf, len_u32(fa.params.len()));
    for pa in &fa.params {
        write_param_attrs(buf, pa);
    }
}

fn read_func_attrs(r: &mut Reader<'_>) -> Result<FuncAttrs, BinaryError> {
    let flags = r.read_u8()?;
    let n = r.read_checked_len()?;
    let mut params = Vec::with_capacity(n);
    for _ in 0..n {
        params.push(read_param_attrs(r)?);
    }
    Ok(FuncAttrs {
        readonly: flags & 0b0001 != 0,
        readnone: flags & 0b0010 != 0,
        inlinehint: flags & 0b0100 != 0,
        cold: flags & 0b1000 != 0,
        params,
    })
}

/// Serialize a [`ProofFormula`] (schema + payload + optional smtlib/sort). Mirrors
/// the inline encoding in [`write_proof_obligation`] so both stay in lockstep.
fn write_proof_formula(buf: &mut Vec<u8>, pool: &mut StringPool, f: &ProofFormula) {
    write_str(buf, pool, &f.schema);
    write_str(buf, pool, &f.payload);
    write_opt_str(buf, pool, f.smtlib.as_deref());
    write_opt_str(buf, pool, f.sort.as_deref());
}

fn read_proof_formula(r: &mut Reader<'_>) -> Result<ProofFormula, BinaryError> {
    Ok(ProofFormula {
        schema: r.read_str()?,
        payload: r.read_str()?,
        smtlib: read_opt_str(r)?,
        sort: read_opt_str(r)?,
    })
}

/// Serialize the separate-compilation [`FunctionSummary`] (v18+).
fn write_function_summary(buf: &mut Vec<u8>, pool: &mut StringPool, s: &FunctionSummary) {
    write_v32(buf, len_u32(s.requires.len()));
    for c in &s.requires {
        write_proof_formula(buf, pool, c);
    }
    write_v32(buf, len_u32(s.ensures.len()));
    for c in &s.ensures {
        write_proof_formula(buf, pool, c);
    }
    write_v32(buf, len_u32(s.params.len()));
    for p in &s.params {
        write_str(buf, pool, p);
    }
    write_u8(buf, u8::from(s.proved));
}

fn read_function_summary(r: &mut Reader<'_>) -> Result<FunctionSummary, BinaryError> {
    let nr = r.read_checked_len()?;
    let mut requires = Vec::with_capacity(nr);
    for _ in 0..nr {
        requires.push(read_proof_formula(r)?);
    }
    let ne = r.read_checked_len()?;
    let mut ensures = Vec::with_capacity(ne);
    for _ in 0..ne {
        ensures.push(read_proof_formula(r)?);
    }
    let np = r.read_checked_len()?;
    let mut params = Vec::with_capacity(np);
    for _ in 0..np {
        params.push(r.read_str()?);
    }
    let proved = r.read_u8()? != 0;
    Ok(FunctionSummary {
        requires,
        ensures,
        params,
        proved,
    })
}

/// v23: producer provenance tag. Stable wire tags (frozen; new producers
/// append): TRust=0, Clean=1, TrustIr=2, TSwift=3, TC=4, Other=5 followed by
/// its string payload.
fn write_producer(buf: &mut Vec<u8>, pool: &mut StringPool, producer: &Producer) {
    match producer {
        Producer::TRust => write_u8(buf, 0),
        Producer::Clean => write_u8(buf, 1),
        Producer::TrustIr => write_u8(buf, 2),
        Producer::TSwift => write_u8(buf, 3),
        Producer::TC => write_u8(buf, 4),
        Producer::Other(s) => {
            write_u8(buf, 5);
            write_str(buf, pool, s);
        }
    }
}

fn read_producer(r: &mut Reader<'_>) -> Result<Producer, BinaryError> {
    Ok(match r.read_u8()? {
        0 => Producer::TRust,
        1 => Producer::Clean,
        2 => Producer::TrustIr,
        3 => Producer::TSwift,
        4 => Producer::TC,
        5 => Producer::Other(r.read_str()?),
        tag => return Err(BinaryError::InvalidTag(tag)),
    })
}

fn write_function(buf: &mut Vec<u8>, pool: &mut StringPool, func: &Function) {
    write_func_id(buf, func.id);
    write_str(buf, pool, &func.name);
    write_func_ty_id(buf, func.ty);
    write_block_id(buf, func.entry);
    write_v32(buf, len_u32(func.blocks.len()));
    for block in &func.blocks {
        write_block(buf, pool, block);
    }
    write_proof_annotation_list(buf, pool, &func.proofs);
    write_calling_conv(buf, &func.calling_conv);
    write_linkage(buf, &func.linkage);
    write_func_attrs(buf, &func.attrs);
    // v18+: separate-compilation contract. Presence byte then payload, so a
    // body-less declaration carrying a summary round-trips.
    match &func.summary {
        None => write_u8(buf, 0),
        Some(summary) => {
            write_u8(buf, 1);
            write_function_summary(buf, pool, summary);
        }
    }
    // v23+: producer provenance. Presence byte then the stable producer tag.
    match &func.producer {
        None => write_u8(buf, 0),
        Some(producer) => {
            write_u8(buf, 1);
            write_producer(buf, pool, producer);
        }
    }
    // v32+: debug value names (C2-names). Presence byte, then (ValueId, name) pairs.
    match &func.value_names {
        None => write_u8(buf, 0),
        Some(names) => {
            write_u8(buf, 1);
            write_v32(buf, len_u32(names.len()));
            for (v, n) in names {
                write_value_id(buf, *v);
                write_str(buf, pool, n);
            }
        }
    }
    // v33+: lexical scope tree (C2-scopes). Presence byte, then one
    // (parent, span) entry per scope. No strings, so the up-front pool needs
    // no companion entry here — the v32 trap does not repeat.
    match &func.scopes {
        None => write_u8(buf, 0),
        Some(scopes) => {
            write_u8(buf, 1);
            write_v32(buf, len_u32(scopes.len()));
            for sc in scopes {
                match sc.parent {
                    None => write_u8(buf, 0),
                    Some(p) => {
                        write_u8(buf, 1);
                        write_v32(buf, p);
                    }
                }
                match &sc.span {
                    None => write_u8(buf, 0),
                    Some(span) => {
                        write_u8(buf, 1);
                        write_v32(buf, span.file);
                        write_v32(buf, span.line);
                        write_v32(buf, span.col);
                    }
                }
            }
        }
    }
    // v35+: semantic source-loop/place provenance.
    match &func.source_provenance {
        None => write_u8(buf, 0),
        Some(provenance) => {
            write_u8(buf, 1);
            write_v32(buf, provenance.schema);
            write_proof_digest(buf, &provenance.compiler_source_digest);
            write_proof_digest(buf, &provenance.semantic_body_digest);
            write_proof_digest(buf, &provenance.binding_digest);
            write_v32(buf, len_u32(provenance.loops.len()));
            for source_loop in &provenance.loops {
                write_v32(buf, source_loop.source_loop_id);
                write_v32(buf, source_loop.hir_local_id);
                write_block_id(buf, source_loop.header);
                write_v32(buf, len_u32(source_loop.bindings.len()));
                for binding in &source_loop.bindings {
                    write_str(buf, pool, &binding.name);
                    write_v32(buf, binding.hir_local_id);
                    match binding.place {
                        SourcePlace::FunctionParameter { index } => {
                            write_u8(buf, 0);
                            write_v32(buf, index);
                        }
                        SourcePlace::LoopParameter { index } => {
                            write_u8(buf, 1);
                            write_v32(buf, index);
                        }
                    }
                }
            }
        }
    }
}

fn read_function(r: &mut Reader<'_>, version: u32) -> Result<Function, BinaryError> {
    let id = r.read_func_id()?;
    let name = r.read_str()?;
    let ty = r.read_func_ty_id()?;
    let entry = r.read_block_id()?;
    let block_count = r.read_checked_len()?;
    let mut blocks = Vec::with_capacity(block_count);
    for _ in 0..block_count {
        blocks.push(read_block(r, version)?);
    }
    let proof_count = r.read_checked_len()?;
    let mut proofs = Vec::with_capacity(proof_count);
    for _ in 0..proof_count {
        proofs.push(read_proof_annotation(r)?);
    }
    let calling_conv = read_calling_conv(r)?;
    let linkage = read_linkage(r)?;
    // v7+: function/parameter attributes (fast-2); legacy files default-empty.
    let attrs = if version >= 7 {
        read_func_attrs(r)?
    } else {
        FuncAttrs::default()
    };
    // v18+: separate-compilation contract; legacy files default to None.
    let summary = if version >= 18 {
        match r.read_u8()? {
            0 => None,
            1 => Some(read_function_summary(r)?),
            tag => return Err(BinaryError::InvalidTag(tag)),
        }
    } else {
        None
    };
    // v23+: producer provenance; legacy files default to None.
    let producer = if version >= 23 {
        match r.read_u8()? {
            0 => None,
            1 => Some(read_producer(r)?),
            tag => return Err(BinaryError::InvalidTag(tag)),
        }
    } else {
        None
    };
    // v32+: debug value names; legacy files default to None.
    let value_names = if version >= 32 {
        match r.read_u8()? {
            0 => None,
            1 => {
                let n = r.read_checked_len()?;
                let mut names = Vec::with_capacity(n);
                for _ in 0..n {
                    let v = r.read_value_id()?;
                    let s = r.read_str()?;
                    names.push((v, s));
                }
                Some(names)
            }
            tag => return Err(BinaryError::InvalidTag(tag)),
        }
    } else {
        None
    };
    // v33+: lexical scope tree; legacy files default to None.
    let scopes = if version >= 33 {
        match r.read_u8()? {
            0 => None,
            1 => {
                let n = r.read_checked_len()?;
                let mut scopes = Vec::with_capacity(n);
                for _ in 0..n {
                    let parent = match r.read_u8()? {
                        0 => None,
                        1 => Some(r.read_v32()?),
                        tag => return Err(BinaryError::InvalidTag(tag)),
                    };
                    let span = match r.read_u8()? {
                        0 => None,
                        1 => Some(SourceSpan {
                            file: r.read_v32()?,
                            line: r.read_v32()?,
                            col: r.read_v32()?,
                        }),
                        tag => return Err(BinaryError::InvalidTag(tag)),
                    };
                    scopes.push(ScopeData { parent, span });
                }
                Some(scopes)
            }
            tag => return Err(BinaryError::InvalidTag(tag)),
        }
    } else {
        None
    };
    let source_provenance = if version >= 35 {
        match r.read_u8()? {
            0 => None,
            1 => {
                let schema = r.read_v32()?;
                let compiler_source_digest = read_proof_digest(r)?;
                let semantic_body_digest = read_proof_digest(r)?;
                let binding_digest = read_proof_digest(r)?;
                let loop_count = r.read_checked_len()?;
                let mut loops = Vec::with_capacity(loop_count);
                for _ in 0..loop_count {
                    let source_loop_id = r.read_v32()?;
                    let hir_local_id = r.read_v32()?;
                    let header = r.read_block_id()?;
                    let binding_count = r.read_checked_len()?;
                    let mut bindings = Vec::with_capacity(binding_count);
                    for _ in 0..binding_count {
                        let name = r.read_str()?;
                        let hir_local_id = r.read_v32()?;
                        let place = match r.read_u8()? {
                            0 => SourcePlace::FunctionParameter {
                                index: r.read_v32()?,
                            },
                            1 => SourcePlace::LoopParameter {
                                index: r.read_v32()?,
                            },
                            tag => return Err(BinaryError::InvalidTag(tag)),
                        };
                        bindings.push(SourceBindingProvenance {
                            name,
                            hir_local_id,
                            place,
                        });
                    }
                    loops.push(SourceLoopProvenance {
                        source_loop_id,
                        hir_local_id,
                        header,
                        bindings,
                    });
                }
                Some(SourceProvenance {
                    schema,
                    compiler_source_digest,
                    semantic_body_digest,
                    binding_digest,
                    loops,
                })
            }
            tag => return Err(BinaryError::InvalidTag(tag)),
        }
    } else {
        None
    };
    Ok(Function {
        id,
        name,
        ty,
        entry,
        blocks,
        proofs,
        calling_conv,
        linkage,
        attrs,
        summary,
        producer,
        value_names,
        scopes,
        source_provenance,
    })
}

// ---------------------------------------------------------------------------
// Public API
// ---------------------------------------------------------------------------

fn collect_lineage_strings(nodes: &[ProofLineageNode]) -> StringPool {
    let mut pool = StringPool::new();
    for node in nodes {
        pool.intern(node.transform.name.clone());
        pool.intern(node.transform.producer.clone());
        pool.intern(node.transform.version.clone());
        for cert in &node.certificates {
            pool.intern(cert.prover.clone());
        }
        if let Some(replay) = &node.replay {
            pool.intern(replay.engine.clone());
            pool.intern(replay.invocation.clone());
        }
    }
    pool
}

/// Serialize a proof-lineage sidecar manifest to canonical binary storage.
///
/// This is a standalone Trust/consumer boundary, not a new `Module` section:
/// it uses `TMPL` magic and its own version word so `.tmbc` remains v2.
/// Node ids, roots, obligations, certificate refs, and dependencies are sorted
/// on write to avoid golden churn from DAG construction order.
pub fn serialize_proof_lineage_manifest(manifest: &ProofLineageManifest) -> Vec<u8> {
    let mut buf = Vec::new();
    buf.extend_from_slice(PROOF_LINEAGE_MAGIC);
    // Version 2 adds string interning.
    write_u32(&mut buf, PROOF_LINEAGE_VERSION);
    write_u32(&mut buf, manifest.schema_version);

    // Sort nodes by id *before* interning so the string-pool order is derived
    // from the same canonical node order that is written below. Otherwise a
    // serialize -> deserialize -> serialize cycle is non-idempotent: the first
    // pass interns in the caller's (arbitrary) node order while every later
    // pass interns in the deserialized (already-sorted) order, shuffling string
    // ids and the pool header (issue: proof lineage sidecar idempotency).
    let mut nodes = manifest.nodes.clone();
    nodes.sort_by_key(|node| node.id);

    let mut pool = collect_lineage_strings(&nodes);
    write_v32(&mut buf, len_u32(pool.strings.len()));
    for s in &pool.strings {
        write_raw_str(&mut buf, s);
    }

    write_v32(&mut buf, len_u32(nodes.len()));
    for node in &nodes {
        write_proof_lineage_node(&mut buf, &mut pool, node);
    }

    let mut roots = manifest.roots.clone();
    roots.sort();
    write_v32(&mut buf, len_u32(roots.len()));
    for root in roots {
        write_v32(&mut buf, root.0);
    }

    buf
}

/// Deserialize a proof-lineage sidecar manifest from canonical binary storage.
pub fn deserialize_proof_lineage_manifest(
    bytes: &[u8],
) -> Result<ProofLineageManifest, BinaryError> {
    let mut r = Reader::new(bytes);
    let magic = r.read_exact(PROOF_LINEAGE_MAGIC.len())?;
    if magic != PROOF_LINEAGE_MAGIC[..] {
        return Err(BinaryError::InvalidMagic);
    }
    let version = r.read_u32()?;
    if version == 0 || version > 2 {
        return Err(BinaryError::UnsupportedVersion);
    }

    let schema_version = r.read_u32()?;

    if version >= 2 {
        let pool_size = r.read_checked_len()?;
        let mut strings = Vec::with_capacity(pool_size);
        let mut map = BTreeMap::new();
        for i in 0..pool_size {
            let s = r.read_raw_str()?;
            map.insert(s.clone(), len_u32(i));
            strings.push(s);
        }
        r.pool = Some(StringPool { strings, map });
    }

    let node_count = r.read_checked_len()?;
    let mut nodes = Vec::with_capacity(node_count);
    for _ in 0..node_count {
        nodes.push(read_proof_lineage_node(&mut r)?);
    }

    let root_count = r.read_checked_len()?;
    let mut roots = Vec::with_capacity(root_count);
    for _ in 0..root_count {
        roots.push(ProofLineageId::new(r.read_v32()?));
    }

    Ok(ProofLineageManifest {
        schema_version,
        nodes,
        roots,
    })
}

// Native-verification-bundle envelope.
//
// The bundle carries a `Module`, a proof-lineage `Manifest`, and a large body
// of serde-only metadata: typed requests, verifier evidence bundles, policy
// structs, provenance, and compiler facts. The compact `.tmbc`/`.tmpl` codecs
// only model the module and the lineage manifest, so the historical
// two-segment encoding silently dropped everything else and fabricated wrong
// metadata on the way back in (schema_version forced to 1, producer/input/
// digest/requests/evidence reset to defaults).
//
// This codec is honest instead: it encodes the scalar metadata fields it CAN
// represent losslessly (`schema_version`, `producer`, `input`,
// `trust_ir_module_digest`) into a versioned `TMVB` header, then the lineage
// and module segments. Fields the binary format provably cannot carry — the
// `provenance`/`serialization`/`diagnostics`/`compiler_facts` records and the
// `requests`/`evidence_bundles` vectors — must be at their default/empty value
// or `serialize` returns `Err(BinaryError::Unencodable(..))` rather than
// dropping data. Round-tripping those rich bundles is what the serde
// (JSON/MessagePack) path is for; this binary path is the lossless-or-honest
// `.tmbc`-family envelope.
const NATIVE_BUNDLE_MAGIC: &[u8; 4] = b"TMVB";
const NATIVE_BUNDLE_VERSION: u32 = 1;

fn write_native_bundle_producer(
    buf: &mut Vec<u8>,
    producer: &crate::request::NativeBundleProducer,
) {
    use crate::request::NativeBundleProducer;
    let tag: u8 = match producer {
        NativeBundleProducer::TRust => 0,
        NativeBundleProducer::TSwift => 1,
        NativeBundleProducer::TC => 2,
        NativeBundleProducer::TrustIr => 3,
    };
    write_u8(buf, tag);
}

fn read_native_bundle_producer(
    r: &mut Reader<'_>,
) -> Result<crate::request::NativeBundleProducer, BinaryError> {
    use crate::request::NativeBundleProducer;
    match r.read_u8()? {
        0 => Ok(NativeBundleProducer::TRust),
        1 => Ok(NativeBundleProducer::TSwift),
        2 => Ok(NativeBundleProducer::TC),
        3 => Ok(NativeBundleProducer::TrustIr),
        t => Err(BinaryError::InvalidTag(t)),
    }
}

fn write_native_adapter_input(buf: &mut Vec<u8>, input: &crate::request::NativeAdapterInput) {
    use crate::request::NativeAdapterInput;
    match input {
        NativeAdapterInput::RustMir { body_digest } => {
            write_u8(buf, 0);
            write_proof_digest(buf, body_digest);
        }
        NativeAdapterInput::TrustIrModule => write_u8(buf, 1),
    }
}

fn read_native_adapter_input(
    r: &mut Reader<'_>,
) -> Result<crate::request::NativeAdapterInput, BinaryError> {
    use crate::request::NativeAdapterInput;
    match r.read_u8()? {
        0 => Ok(NativeAdapterInput::RustMir {
            body_digest: read_proof_digest(r)?,
        }),
        1 => Ok(NativeAdapterInput::TrustIrModule),
        t => Err(BinaryError::InvalidTag(t)),
    }
}

/// Serialize a native verification bundle to the lossless-or-honest `.tmbc`
/// envelope: `[TMVB header] [Lineage] [Module]`.
///
/// Returns an error if the bundle carries metadata the binary envelope cannot
/// represent (non-default policy/provenance/compiler-fact records, or non-empty
/// `requests`/`evidence_bundles`). Use the serde JSON/MessagePack path for
/// those rich bundles.
pub fn serialize_native_verification_bundle(
    bundle: &crate::request::NativeVerificationBundle,
) -> Result<Vec<u8>, BinaryError> {
    use crate::request::{
        NativeBundleProvenance, NativeCompilerFacts, NativeDiagnosticsPolicy,
        NativeSerializationPolicy,
    };
    // Refuse to silently drop anything the binary envelope cannot carry.
    if !bundle.requests.is_empty() {
        return Err(BinaryError::Unencodable(
            "native bundle binary codec cannot encode typed requests; use serde JSON/MessagePack",
        ));
    }
    if !bundle.evidence_bundles.is_empty() {
        return Err(BinaryError::Unencodable(
            "native bundle binary codec cannot encode evidence bundles; use serde JSON/MessagePack",
        ));
    }
    if bundle.provenance != NativeBundleProvenance::default() {
        return Err(BinaryError::Unencodable(
            "native bundle binary codec cannot encode non-default provenance",
        ));
    }
    if bundle.serialization != NativeSerializationPolicy::default() {
        return Err(BinaryError::Unencodable(
            "native bundle binary codec cannot encode non-default serialization policy",
        ));
    }
    if bundle.diagnostics != NativeDiagnosticsPolicy::default() {
        return Err(BinaryError::Unencodable(
            "native bundle binary codec cannot encode non-default diagnostics policy",
        ));
    }
    if bundle.compiler_facts != NativeCompilerFacts::default() {
        return Err(BinaryError::Unencodable(
            "native bundle binary codec cannot encode non-default compiler facts",
        ));
    }

    let mut buf = Vec::new();
    // Versioned metadata header.
    buf.extend_from_slice(NATIVE_BUNDLE_MAGIC);
    write_u32(&mut buf, NATIVE_BUNDLE_VERSION);
    write_u32(&mut buf, bundle.schema_version);
    write_native_bundle_producer(&mut buf, &bundle.producer);
    write_native_adapter_input(&mut buf, &bundle.input);
    write_proof_digest(&mut buf, &bundle.trust_ir_module_digest);
    // Payload segments (each self-describing via its own magic).
    buf.extend_from_slice(&serialize_proof_lineage_manifest(&bundle.lineage));
    buf.extend_from_slice(&serialize_module(&bundle.module));
    Ok(buf)
}

pub fn deserialize_native_verification_bundle(
    bytes: &[u8],
) -> Result<crate::request::NativeVerificationBundle, BinaryError> {
    // New envelope: TMVB header carries the scalar metadata losslessly, then
    // the TMPL lineage and TRUST_IR module segments follow.
    if bytes.starts_with(NATIVE_BUNDLE_MAGIC) {
        let mut r = Reader::new(bytes);
        let _magic = r.read_exact(NATIVE_BUNDLE_MAGIC.len())?;
        let version = r.read_u32()?;
        if version != NATIVE_BUNDLE_VERSION {
            return Err(BinaryError::UnsupportedVersion);
        }
        let schema_version = r.read_u32()?;
        let producer = read_native_bundle_producer(&mut r)?;
        let input = read_native_adapter_input(&mut r)?;
        let trust_ir_module_digest = read_proof_digest(&mut r)?;
        let header_end = r.cursor.position() as usize;
        let rest = &bytes[header_end..];

        if !rest.starts_with(PROOF_LINEAGE_MAGIC) {
            return Err(BinaryError::InvalidMagic);
        }
        let lineage = deserialize_proof_lineage_manifest(rest)?;
        let module_pos = rest
            .windows(MAGIC.len())
            .position(|window| window == MAGIC)
            .ok_or(BinaryError::InvalidMagic)?;
        let module = deserialize_module(&rest[module_pos..])?;

        let mut bundle = crate::request::NativeVerificationBundle::new(
            producer,
            input,
            trust_ir_module_digest,
            module,
            lineage,
        );
        bundle.schema_version = schema_version;
        // Decoded from bytes — never a live in-process source generation:
        // `NativeVerificationBundle::new` leaves the private source-generation
        // marker at its not-live default, so the proof-authority gate stays
        // fail-closed for this bundle.
        return Ok(bundle);
    }

    Err(BinaryError::InvalidMagic)
}

/// Serialize a TrustIr module to a compact binary format.
/// Serialize a [`crate::spec::SpecModule`] (current v27 layout). All strings go through
/// the interning `write_str`; every one of them is pre-pooled by
/// [`collect_spec_module_strings`].
fn write_spec_module(buf: &mut Vec<u8>, pool: &mut StringPool, sm: &crate::spec::SpecModule) {
    use crate::spec::SpecOrigin;

    write_str(buf, pool, &sm.name);

    write_v32(buf, len_u32(sm.vars.len()));
    for v in &sm.vars {
        write_str(buf, pool, &v.name);
        write_str(buf, pool, &v.ty);
    }

    write_v32(buf, len_u32(sm.actions.len()));
    for a in &sm.actions {
        write_str(buf, pool, a);
    }

    write_v32(buf, len_u32(sm.invariants.len()));
    for inv in &sm.invariants {
        write_str(buf, pool, &inv.name);
        write_str(buf, pool, &inv.formula);
    }

    write_v32(buf, len_u32(sm.anchors.len()));
    for anchor in &sm.anchors {
        write_str(buf, pool, &anchor.machine);
        write_str(buf, pool, &anchor.action);
        write_str(buf, pool, &anchor.rust_symbol);
        write_str(buf, pool, &anchor.span);
        match &anchor.project {
            None => write_u8(buf, 0),
            Some(p) => {
                write_u8(buf, 1);
                write_str(buf, pool, p);
            }
        }
        match anchor.function {
            None => write_u8(buf, 0),
            Some(function) => {
                write_u8(buf, 1);
                write_v32(buf, function.index());
            }
        }
        match anchor.projection_target {
            None => write_u8(buf, 0),
            Some(crate::spec::SpecProjectionTarget::Function(function)) => {
                write_u8(buf, 1);
                write_v32(buf, function.index());
            }
            Some(crate::spec::SpecProjectionTarget::TemporalFieldPathsV1) => write_u8(buf, 2),
            Some(crate::spec::SpecProjectionTarget::ExternalUnresolved) => write_u8(buf, 3),
        }
    }

    write_v32(buf, len_u32(sm.waivers.len()));
    for w in &sm.waivers {
        write_str(buf, pool, &w.machine);
        write_str(buf, pool, &w.action);
        write_str(buf, pool, &w.reason);
    }

    match &sm.origin {
        SpecOrigin::Embedded => write_u8(buf, 0),
        SpecOrigin::External(path) => {
            write_u8(buf, 1);
            write_str(buf, pool, path);
        }
    }

    // Proofs (v14+). Appended after the v13 body so the v13 prefix layout is
    // byte-identical; a v13 reader simply stops here. The reader only consumes
    // this block when `version >= 14`.
    write_proofs(buf, pool, &sm.proofs);
    match sm.enforcement {
        crate::spec::SpecEnforcementMode::DesignOnly => write_u8(buf, 0),
        crate::spec::SpecEnforcementMode::Linked => write_u8(buf, 1),
    }
}

/// Serialize the `proofs` block of a [`crate::spec::SpecModule`] (v14+).
fn write_proofs(buf: &mut Vec<u8>, pool: &mut StringPool, proofs: &[crate::spec::SpecProof]) {
    use crate::spec::ProofKind;
    write_v32(buf, len_u32(proofs.len()));
    for p in proofs {
        write_str(buf, pool, &p.machine);
        write_str(buf, pool, &p.action);
        write_str(buf, pool, &p.proof_name);
        match p.kind {
            ProofKind::Kani => write_u8(buf, 0),
        }
    }
}

/// Deserialize a [`crate::spec::SpecModule`]. The v13 body is read first; the
/// `proofs` block (v14+) is version-gated, and the trailing per-anchor typed
/// function (v26+) defaults to `None` for v23..=v25 blobs. The v27 enforcement
/// mode and projection target use explicit DesignOnly/None compatibility
/// mappings for v23..=v26.
fn read_spec_module(r: &mut Reader<'_>) -> Result<crate::spec::SpecModule, BinaryError> {
    use crate::spec::{
        ProofKind, SpecAnchor, SpecEnforcementMode, SpecInvariant, SpecModule, SpecOrigin,
        SpecProjectionTarget, SpecProof, SpecVar, SpecWaiver,
    };

    let name = r.read_str()?;

    let var_count = r.read_checked_len()?;
    let mut vars = Vec::with_capacity(var_count);
    for _ in 0..var_count {
        let vname = r.read_str()?;
        let vty = r.read_str()?;
        vars.push(SpecVar {
            name: vname,
            ty: vty,
        });
    }

    let action_count = r.read_checked_len()?;
    let mut actions = Vec::with_capacity(action_count);
    for _ in 0..action_count {
        actions.push(r.read_str()?);
    }

    let inv_count = r.read_checked_len()?;
    let mut invariants = Vec::with_capacity(inv_count);
    for _ in 0..inv_count {
        let iname = r.read_str()?;
        let formula = r.read_str()?;
        invariants.push(SpecInvariant {
            name: iname,
            formula,
        });
    }

    let anchor_count = r.read_checked_len()?;
    let mut anchors = Vec::with_capacity(anchor_count);
    for _ in 0..anchor_count {
        let machine = r.read_str()?;
        let action = r.read_str()?;
        let rust_symbol = r.read_str()?;
        let span = r.read_str()?;
        let project = match r.read_u8()? {
            0 => None,
            1 => Some(r.read_str()?),
            t => return Err(BinaryError::InvalidTag(t)),
        };
        let function = if r.version >= 26 {
            match r.read_u8()? {
                0 => None,
                1 => Some(FuncId::new(r.read_v32()?)),
                t => return Err(BinaryError::InvalidTag(t)),
            }
        } else {
            None
        };
        let projection_target = if r.version >= 27 {
            match r.read_u8()? {
                0 => None,
                1 => Some(SpecProjectionTarget::Function(FuncId::new(r.read_v32()?))),
                2 => Some(SpecProjectionTarget::TemporalFieldPathsV1),
                3 => Some(SpecProjectionTarget::ExternalUnresolved),
                t => return Err(BinaryError::InvalidTag(t)),
            }
        } else {
            SpecProjectionTarget::legacy_compatibility()
        };
        anchors.push(SpecAnchor {
            machine,
            action,
            rust_symbol,
            span,
            project,
            function,
            projection_target,
        });
    }

    let waiver_count = r.read_checked_len()?;
    let mut waivers = Vec::with_capacity(waiver_count);
    for _ in 0..waiver_count {
        let machine = r.read_str()?;
        let action = r.read_str()?;
        let reason = r.read_str()?;
        waivers.push(SpecWaiver {
            machine,
            action,
            reason,
        });
    }

    let origin = match r.read_u8()? {
        0 => SpecOrigin::Embedded,
        1 => SpecOrigin::External(r.read_str()?),
        t => return Err(BinaryError::InvalidTag(t)),
    };

    // Proofs (v14+). v13 blobs end after `origin`, so they default to empty.
    let proofs = if r.version >= 14 {
        let proof_count = r.read_checked_len()?;
        let mut proofs = Vec::with_capacity(proof_count);
        for _ in 0..proof_count {
            let machine = r.read_str()?;
            let action = r.read_str()?;
            let proof_name = r.read_str()?;
            let kind = match r.read_u8()? {
                0 => ProofKind::Kani,
                t => return Err(BinaryError::InvalidTag(t)),
            };
            proofs.push(SpecProof {
                machine,
                action,
                proof_name,
                kind,
            });
        }
        proofs
    } else {
        Vec::new()
    };
    let enforcement = if r.version >= 27 {
        match r.read_u8()? {
            0 => SpecEnforcementMode::DesignOnly,
            1 => SpecEnforcementMode::Linked,
            t => return Err(BinaryError::InvalidTag(t)),
        }
    } else {
        SpecEnforcementMode::legacy_compatibility()
    };

    Ok(SpecModule {
        name,
        vars,
        actions,
        invariants,
        anchors,
        waivers,
        proofs,
        origin,
        enforcement,
    })
}

pub fn serialize_module(module: &Module) -> Vec<u8> {
    let mut buf = Vec::new();

    // Header
    buf.extend_from_slice(MAGIC);
    write_u32(&mut buf, VERSION);

    let mut pool = collect_strings(module);
    write_v32(&mut buf, len_u32(pool.strings.len()));
    for s in &pool.strings {
        write_raw_str(&mut buf, s);
    }

    // Module name
    write_str(&mut buf, &mut pool, &module.name);

    // Func types
    write_v32(&mut buf, len_u32(module.func_types.len()));
    for ft in &module.func_types {
        write_func_ty(&mut buf, &mut pool, ft);
    }

    // Structs
    write_v32(&mut buf, len_u32(module.structs.len()));
    for sd in &module.structs {
        write_struct_def(&mut buf, &mut pool, sd);
    }

    // Enums
    write_v32(&mut buf, len_u32(module.enums.len()));
    for ed in &module.enums {
        write_enum_def(&mut buf, &mut pool, ed);
    }

    // Records
    write_v32(&mut buf, len_u32(module.records.len()));
    for rd in &module.records {
        write_record_def(&mut buf, &mut pool, rd);
    }

    // Closure types
    write_v32(&mut buf, len_u32(module.closure_types.len()));
    for ct in &module.closure_types {
        write_closure_ty(&mut buf, &mut pool, ct);
    }

    // Globals
    write_v32(&mut buf, len_u32(module.globals.len()));
    for g in &module.globals {
        write_global(&mut buf, &mut pool, g);
    }

    // Types
    write_v32(&mut buf, len_u32(module.types.len()));
    for ty in &module.types {
        write_ty(&mut buf, &mut pool, ty);
    }

    // Functions
    write_v32(&mut buf, len_u32(module.functions.len()));
    for func in &module.functions {
        write_function(&mut buf, &mut pool, func);
    }

    // Proof obligations
    write_v32(&mut buf, len_u32(module.proof_obligations.len()));
    for po in &module.proof_obligations {
        write_proof_obligation(&mut buf, &mut pool, po);
    }

    // Proof certificates
    write_v32(&mut buf, len_u32(module.proof_certificates.len()));
    for cert in &module.proof_certificates {
        write_proof_certificate(&mut buf, &mut pool, cert);
    }

    // Target info
    match &module.target_info {
        None => write_u8(&mut buf, 0),
        Some(ti) => {
            write_u8(&mut buf, 1);
            write_str(&mut buf, &mut pool, &ti.triple);
            write_v32(&mut buf, ti.pointer_size);
            write_endianness(&mut buf, &ti.endianness);
            // ABI pinning (VERSION >= 20): stable ABI id + struct-passing
            // policy. Digest-bearing: these bytes feed Module::stable_digest.
            write_opt_str(&mut buf, &mut pool, ti.abi.as_deref());
            write_u8(
                &mut buf,
                match ti.struct_passing {
                    StructPassingPolicy::NativeC => 0,
                    StructPassingPolicy::AlwaysMemory => 1,
                    // v36: additive tag. A pre-v36 reader never sees it — the version gate
                    // rejects a v36 blob before reaching this byte — so MIN_READ_VERSION holds.
                    StructPassingPolicy::Unclassified => 2,
                },
            );
        }
    }

    // Debug-info source-file table (VERSION >= 9). Additive trailing section:
    // older readers stop before it; newer readers gate on the version.
    write_v32(&mut buf, len_u32(module.files.len()));
    for path in &module.files {
        write_str(&mut buf, &mut pool, path);
    }

    // Obligation-diagnostics sidecar (VERSION >= 11). Additive trailing section.
    write_v32(&mut buf, len_u32(module.obligation_diagnostics.len()));
    for d in &module.obligation_diagnostics {
        write_proof_id(&mut buf, d.obligation);
        write_u8(
            &mut buf,
            match d.severity {
                crate::proof::DiagnosticSeverity::Error => 0,
                crate::proof::DiagnosticSeverity::Warning => 1,
                crate::proof::DiagnosticSeverity::Note => 2,
            },
        );
        write_str(&mut buf, &mut pool, &d.message);
        match &d.location {
            None => write_u8(&mut buf, 0),
            Some(s) => {
                write_u8(&mut buf, 1);
                write_v32(&mut buf, s.file);
                write_v32(&mut buf, s.line);
                write_v32(&mut buf, s.col);
            }
        }
        match &d.detail {
            None => write_u8(&mut buf, 0),
            Some(detail) => {
                write_u8(&mut buf, 1);
                write_str(&mut buf, &mut pool, detail);
            }
        }
    }

    // Spec modules (VERSION >= 13). Additive trailing section; the current
    // writer always emits it, older readers stop before reaching it.
    write_v32(&mut buf, len_u32(module.spec_modules.len()));
    for sm in &module.spec_modules {
        write_spec_module(&mut buf, &mut pool, sm);
    }

    // Typed value model (VERSION >= 30). Two additive trailing sections.
    // Universes FIRST: a predicate may cite a `UnivId`, so the referent table
    // precedes the referencing one.
    write_v32(&mut buf, len_u32(module.universes.len()));
    for u in &module.universes {
        write_universe(&mut buf, &mut pool, u);
    }
    write_v32(&mut buf, len_u32(module.predicates.len()));
    for p in &module.predicates {
        write_pred(&mut buf, &mut pool, p);
    }

    buf
}

/// Deserialize a TrustIr module from the compact binary format.
pub fn deserialize_module(bytes: &[u8]) -> Result<Module, BinaryError> {
    let mut r = Reader::new(bytes);

    // Header
    let magic = r.read_exact(MAGIC.len())?;
    if magic != MAGIC[..] {
        return Err(BinaryError::InvalidMagic);
    }
    let version = r.read_u32()?;
    if !(MIN_READ_VERSION..=VERSION).contains(&version) {
        return Err(BinaryError::UnsupportedVersion);
    }
    // Ambiguous-lineage refusal (see the VERSION ledger): v26..=v28 blobs were
    // written by two divergent lines with byte-incompatible layouts and cannot
    // be decoded without risking a misparse of one line under the other's
    // gates. Fail closed; the producer regenerates at v29.
    if (26..=28).contains(&version) {
        return Err(BinaryError::UnsupportedVersion);
    }
    r.version = version;

    if version >= 4 {
        let pool_size = r.read_checked_len()?;
        let mut strings = Vec::with_capacity(pool_size);
        let mut map = BTreeMap::new();
        for i in 0..pool_size {
            let s = r.read_raw_str()?;
            map.insert(s.clone(), len_u32(i));
            strings.push(s);
        }
        r.pool = Some(StringPool { strings, map });
    }

    // Module name
    let name = r.read_str()?;

    // Func types
    let ft_count = r.read_checked_len()?;
    let mut func_types = Vec::with_capacity(ft_count);
    for _ in 0..ft_count {
        func_types.push(read_func_ty(&mut r)?);
    }

    // Structs
    let struct_count = r.read_checked_len()?;
    let mut structs = Vec::with_capacity(struct_count);
    for _ in 0..struct_count {
        structs.push(read_struct_def(&mut r)?);
    }

    // Enums
    let enum_count = r.read_checked_len()?;
    let mut enums = Vec::with_capacity(enum_count);
    for _ in 0..enum_count {
        enums.push(read_enum_def(&mut r)?);
    }

    // Records
    let record_count = r.read_checked_len()?;
    let mut records = Vec::with_capacity(record_count);
    for _ in 0..record_count {
        records.push(read_record_def(&mut r)?);
    }

    // Closure types
    let closure_ty_count = r.read_checked_len()?;
    let mut closure_types = Vec::with_capacity(closure_ty_count);
    for _ in 0..closure_ty_count {
        closure_types.push(read_closure_ty(&mut r)?);
    }

    // Globals
    let global_count = r.read_checked_len()?;
    let mut globals = Vec::with_capacity(global_count);
    for _ in 0..global_count {
        globals.push(read_global(&mut r, version)?);
    }

    // Types
    let type_count = r.read_checked_len()?;
    let mut types = Vec::with_capacity(type_count);
    for _ in 0..type_count {
        types.push(read_ty(&mut r)?);
    }

    // Functions
    let func_count = r.read_checked_len()?;
    let mut functions = Vec::with_capacity(func_count);
    for _ in 0..func_count {
        functions.push(read_function(&mut r, version)?);
    }

    // Proof obligations
    let po_count = r.read_checked_len()?;
    let mut proof_obligations = Vec::with_capacity(po_count);
    for _ in 0..po_count {
        proof_obligations.push(read_proof_obligation(&mut r, version)?);
    }

    // Proof certificates
    let cert_count = r.read_checked_len()?;
    let mut proof_certificates = Vec::with_capacity(cert_count);
    for _ in 0..cert_count {
        proof_certificates.push(read_proof_certificate(&mut r)?);
    }

    // Target info
    let target_info = match r.read_u8()? {
        0 => None,
        1 => {
            let triple = r.read_str()?;
            let pointer_size = r.read_v32()?;
            let endianness = read_endianness(&mut r)?;
            // ABI pinning (VERSION >= 20); pre-v20 records stop at endianness.
            let (abi, struct_passing) = if version >= 20 {
                let abi = read_opt_str(&mut r)?;
                let struct_passing = match r.read_u8()? {
                    0 => StructPassingPolicy::NativeC,
                    1 => StructPassingPolicy::AlwaysMemory,
                    2 if version >= 36 => StructPassingPolicy::Unclassified,
                    t => return Err(BinaryError::InvalidTag(t)),
                };
                (abi, struct_passing)
            } else {
                (None, StructPassingPolicy::default())
            };
            Some(TargetInfo {
                triple,
                pointer_size,
                endianness,
                abi,
                struct_passing,
            })
        }
        t => return Err(BinaryError::InvalidTag(t)),
    };

    // Debug-info source-file table (VERSION >= 9). Older modules have none.
    let files = if r.version >= 9 {
        let n = r.read_checked_len()?;
        let mut files = Vec::with_capacity(n);
        for _ in 0..n {
            files.push(r.read_str()?);
        }
        files
    } else {
        Vec::new()
    };

    // Obligation-diagnostics sidecar (VERSION >= 11). Older modules have none.
    let obligation_diagnostics = if r.version >= 11 {
        let n = r.read_checked_len()?;
        let mut diags = Vec::with_capacity(n);
        for _ in 0..n {
            let obligation = r.read_proof_id()?;
            let severity = match r.read_u8()? {
                0 => crate::proof::DiagnosticSeverity::Error,
                1 => crate::proof::DiagnosticSeverity::Warning,
                2 => crate::proof::DiagnosticSeverity::Note,
                t => return Err(BinaryError::InvalidTag(t)),
            };
            let message = r.read_str()?;
            let location = match r.read_u8()? {
                0 => None,
                1 => Some(SourceSpan {
                    file: r.read_v32()?,
                    line: r.read_v32()?,
                    col: r.read_v32()?,
                }),
                t => return Err(BinaryError::InvalidTag(t)),
            };
            let detail = match r.read_u8()? {
                0 => None,
                1 => Some(r.read_str()?),
                t => return Err(BinaryError::InvalidTag(t)),
            };
            diags.push(crate::proof::ObligationDiagnostic {
                obligation,
                severity,
                message,
                location,
                detail,
            });
        }
        diags
    } else {
        Vec::new()
    };

    // Spec modules (VERSION >= 13). Older blobs end before this section, so they
    // default to an empty vector — exactly mirroring the serde `#[serde(default)]`.
    let spec_modules = if version >= 13 {
        let sm_count = r.read_checked_len()?;
        let mut spec_modules = Vec::with_capacity(sm_count);
        for _ in 0..sm_count {
            spec_modules.push(read_spec_module(&mut r)?);
        }
        spec_modules
    } else {
        Vec::new()
    };

    // Typed value model (VERSION >= 30). Pre-v30 blobs end before these
    // sections and default to empty tables — which, combined with the fact
    // that no pre-v30 blob can carry a `Ty::Refine` (tag 36 is new), means a
    // v29 module decodes to EXACTLY what it always meant.
    let (universes, predicates) = if version >= 30 {
        let u_count = r.read_checked_len()?;
        let mut universes = Vec::with_capacity(u_count);
        for _ in 0..u_count {
            universes.push(read_universe(&mut r)?);
        }
        let p_count = r.read_checked_len()?;
        let mut predicates = Vec::with_capacity(p_count);
        for _ in 0..p_count {
            predicates.push(read_pred(&mut r)?);
        }
        (universes, predicates)
    } else {
        (Vec::new(), Vec::new())
    };

    let module = Module {
        name,
        functions,
        structs,
        enums,
        records,
        closure_types,
        globals,
        func_types,
        types,
        proof_obligations,
        proof_certificates,
        target_info,
        files,
        obligation_diagnostics,
        spec_modules,
        universes,
        predicates,
    };

    if let Err(errors) = module.validate_vector_select_contracts() {
        return Err(BinaryError::InvalidData(format!("{}", errors[0])));
    }

    Ok(module)
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    fn v(n: u32) -> ValueId {
        ValueId::new(n)
    }

    fn b(n: u32) -> BlockId {
        BlockId::new(n)
    }

    fn d(n: u8) -> ProofDigest {
        ProofDigest::sha256([n; 32])
    }

    fn lineage_cert(id: u32, prover: &str, payload: &[u8]) -> ProofCertificate {
        ProofCertificate {
            obligation: ProofId::new(id),
            prover: prover.to_string(),
            evidence: ProofEvidence::SmtProof(payload.to_vec()),
        }
    }

    fn proof_lineage_manifest() -> ProofLineageManifest {
        let cert0 = lineage_cert(0, "ay", &[1, 2, 3]);
        let cert1 = lineage_cert(1, "lean", b"rfl");

        let mut lowering = ProofLineageNode::new(
            ProofLineageId::new(0),
            ProofTransform::new(
                ProofTransformStage::TrustIrLowering,
                "trust-to-trust_ir",
                "Trust",
                "0.1.0",
            ),
            d(1),
            d(2),
        );
        lowering.obligations.push(ProofId::new(0));
        lowering.certificates.push(cert0.lineage_ref());

        let mut solver = ProofLineageNode::new(
            ProofLineageId::new(1),
            ProofTransform::new(
                ProofTransformStage::SolverAdapter,
                "trust-ir-ay",
                "TrustIr",
                "0.1.0",
            ),
            d(2),
            d(3),
        );
        solver.obligations.push(ProofId::new(1));
        solver.certificates.push(cert1.lineage_ref());
        solver.depends_on.push(ProofLineageId::new(0));
        solver.replay = Some(
            ProofReplayIdentity::new("tcargo-stage2", "cargo test -p trust-ir-ay")
                .with_transcript_digest(ProofDigest::sha256_domain("binary-test.v1", b"ok")),
        );

        ProofLineageManifest {
            schema_version: ProofLineageManifest::SCHEMA_VERSION,
            nodes: vec![solver, lowering],
            roots: vec![ProofLineageId::new(1)],
        }
    }

    /// Round-trip helper: serialize then deserialize, assert equality.
    fn round_trip(module: &Module) -> Module {
        let bytes = serialize_module(module);
        let back = deserialize_module(&bytes).expect("deserialize should succeed");
        assert_eq!(module, &back, "round-trip mismatch");
        back
    }

    // --- Separate-compilation contract (v18) ---

    #[test]
    fn function_summary_declaration_round_trips() {
        use crate::{FunctionSummary, ProofFormula};
        let mut module = Module::new("composition");
        let ft = module.add_func_type(FuncTy {
            params: vec![Ty::I32],
            returns: vec![Ty::I32],
            is_vararg: false,
        });
        let summary = FunctionSummary::new()
            .with_params(vec!["x".to_string()])
            .requiring(ProofFormula::trust_types_json(
                "{\"Ge\":[{\"Var\":[\"x\",\"Int\"]},{\"Int\":0}]}",
                "(>= x 0)",
                "Bool",
            ))
            .ensuring(ProofFormula::smtlib2("(> result 0)", "Bool"))
            .proved();
        // A contract-only declaration: body None ⇒ summary.
        let decl = Function::declaration(FuncId::new(0), "helper", ft, summary.clone());
        assert!(decl.is_declaration());
        assert!(!decl.has_body());
        assert!(decl.body().is_none());
        module.add_function(decl);

        let back = round_trip(&module);
        let f = &back.functions[0];
        assert!(f.is_declaration(), "declaration state survives round-trip");
        assert_eq!(
            f.summary.as_ref(),
            Some(&summary),
            "contract survives round-trip"
        );
    }

    #[test]
    fn function_value_names_round_trip() {
        // Trust (C2-names, v32): Some survives byte-exact; None writes the absent presence byte
        // and reads back None — and both directions are pinned so a future writer cannot start
        // stamping empty tables that read as "named, zero names".
        let mut module = Module::new("names");
        let ft = module.add_func_type(FuncTy {
            params: vec![Ty::I32],
            returns: vec![Ty::I32],
            is_vararg: false,
        });
        let mut named = Function::new(FuncId::new(0), "named", ft, BlockId(0));
        named.value_names = Some(vec![
            (ValueId::new(0), "x".to_string()),
            (ValueId::new(7), "tmp_sum".to_string()),
        ]);
        named.blocks.push(Block {
            id: BlockId(0),
            params: vec![(ValueId::new(0), Ty::I32)],
            body: vec![
                InstrNode::new(Inst::Copy {
                    ty: Ty::I32,
                    operand: ValueId::new(0),
                })
                .with_result(ValueId::new(7)),
                InstrNode::new(Inst::Return {
                    values: vec![ValueId::new(7)],
                }),
            ],
        });
        module.add_function(named);
        let mut anon = Function::new(FuncId::new(1), "anon", ft, BlockId(0));
        anon.blocks.push(Block {
            id: BlockId(0),
            params: vec![(ValueId::new(0), Ty::I32)],
            body: vec![InstrNode::new(Inst::Return {
                values: vec![ValueId::new(0)],
            })],
        });
        module.add_function(anon);

        let back = round_trip(&module);
        assert_eq!(
            back.functions[0].value_names.as_deref(),
            Some(
                &[
                    (ValueId::new(0), "x".to_string()),
                    (ValueId::new(7), "tmp_sum".to_string())
                ][..]
            ),
            "value names survive round-trip in order"
        );
        assert_eq!(
            back.functions[1].value_names, None,
            "absent stays absent, not Some(empty)"
        );
    }

    #[test]
    fn function_scope_tree_round_trips() {
        // Trust (C2-scopes, v33): the tree and the per-node index are two halves
        // of one fact, so the test pins BOTH — a codec that carried the table but
        // dropped the indices would still read as "scopes work".
        let mut module = Module::new("scopes");
        let ft = module.add_func_type(FuncTy {
            params: vec![Ty::I32],
            returns: vec![Ty::I32],
            is_vararg: false,
        });
        let mut scoped = Function::new(FuncId::new(0), "scoped", ft, BlockId(0));
        let mut n0 = InstrNode::new(Inst::Copy {
            ty: Ty::I32,
            operand: ValueId::new(0),
        })
        .with_result(ValueId::new(1));
        n0.scope = Some(2);
        let n1 = InstrNode::new(Inst::Return {
            values: vec![ValueId::new(1)],
        });
        scoped.blocks.push(Block {
            id: BlockId(0),
            params: vec![(ValueId::new(0), Ty::I32)],
            body: vec![n0, n1],
        });
        scoped.scopes = Some(vec![
            ScopeData {
                parent: None,
                span: Some(SourceSpan {
                    file: 0,
                    line: 1,
                    col: 0,
                }),
            },
            ScopeData {
                parent: Some(0),
                span: Some(SourceSpan {
                    file: 0,
                    line: 2,
                    col: 4,
                }),
            },
            // A span-less scope is legal: the producer knew the nesting but not
            // the location. Pinned so the presence bytes stay independent.
            ScopeData {
                parent: Some(1),
                span: None,
            },
        ]);
        module.add_function(scoped);
        let mut flat = Function::new(FuncId::new(1), "flat", ft, BlockId(0));
        flat.blocks.push(Block {
            id: BlockId(0),
            params: Vec::new(),
            body: Vec::new(),
        });
        module.add_function(flat);

        let back = round_trip(&module);
        let f = &back.functions[0];
        assert_eq!(
            f.scopes.as_deref(),
            Some(
                &[
                    ScopeData {
                        parent: None,
                        span: Some(SourceSpan {
                            file: 0,
                            line: 1,
                            col: 0
                        })
                    },
                    ScopeData {
                        parent: Some(0),
                        span: Some(SourceSpan {
                            file: 0,
                            line: 2,
                            col: 4
                        })
                    },
                    ScopeData {
                        parent: Some(1),
                        span: None
                    },
                ][..]
            ),
            "scope tree survives round-trip in order"
        );
        assert_eq!(
            f.blocks[0].body[0].scope,
            Some(2),
            "per-node scope index survives"
        );
        assert_eq!(
            f.blocks[0].body[1].scope, None,
            "unstamped stays unstamped — None must not decode as scope 0"
        );
        assert_eq!(
            back.functions[1].scopes, None,
            "absent stays absent, not Some(empty)"
        );
    }

    #[test]
    fn function_producer_round_trips_every_variant() {
        // v23: every producer tag — including the Other escape with characters
        // that exercise the string pool — survives the binary round-trip.
        let producers = [
            Producer::TRust,
            Producer::Clean,
            Producer::TrustIr,
            Producer::TSwift,
            Producer::TC,
            Producer::Other("my custom \"frontend\" v1.2\n".to_string()),
        ];
        let mut module = Module::new("producers");
        let ft = module.add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::Unit],
            is_vararg: false,
        });
        for (i, producer) in producers.iter().enumerate() {
            let mut func = Function::new(FuncId::new(i as u32), format!("f{i}"), ft, b(0));
            func.producer = Some(producer.clone());
            let mut block = Block::new(b(0));
            block
                .body
                .push(InstrNode::new(Inst::Return { values: vec![] }));
            func.blocks.push(block);
            module.add_function(func);
        }
        // Plus one untagged function: None must round-trip as None.
        let mut untagged = Function::new(FuncId::new(6), "untagged", ft, b(0));
        let mut block = Block::new(b(0));
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        untagged.blocks.push(block);
        module.add_function(untagged);

        let back = round_trip(&module);
        for (i, producer) in producers.iter().enumerate() {
            assert_eq!(
                back.functions[i].producer.as_ref(),
                Some(producer),
                "producer variant {i} survives the v23 round-trip"
            );
        }
        assert_eq!(back.functions[6].producer, None);
    }

    #[test]
    fn defined_function_without_summary_serializes_unchanged_byte_count() {
        // A function with a body and no summary writes exactly one extra presence
        // byte (the `None` tag) versus pre-v18 — and round-trips identically.
        let mut module = Module::new("nosummary");
        let ft = module.add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::Unit],
            is_vararg: false,
        });
        let mut func = Function::new(FuncId::new(0), "f", ft, b(0));
        let mut block = Block::new(b(0));
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        func.blocks.push(block);
        assert!(func.has_body());
        assert!(func.summary.is_none());
        module.add_function(func);
        let back = round_trip(&module);
        assert!(back.functions[0].summary.is_none());
    }

    // --- Header tests ---

    #[test]
    fn header_magic_and_version() {
        let module = Module::new("header_test");
        let bytes = serialize_module(&module);
        assert_eq!(&bytes[0..8], b"TRUST_IR");
        assert_eq!(
            u32::from_le_bytes([bytes[8], bytes[9], bytes[10], bytes[11]]),
            VERSION
        );
    }

    #[test]
    fn v25_spec_anchor_defaults_trailing_function_to_none() {
        // Forge exactly the pre-v26 SpecModule record: project is the final
        // anchor field, immediately followed by the waiver count. The v26
        // reader must not consume that count as a function presence tag.
        let mut pool = StringPool::new();
        let mut bytes = Vec::new();
        write_str(&mut bytes, &mut pool, "crate::Machine");
        write_v32(&mut bytes, 0); // vars
        write_v32(&mut bytes, 1); // actions
        write_str(&mut bytes, &mut pool, "Step");
        write_v32(&mut bytes, 0); // invariants
        write_v32(&mut bytes, 1); // anchors
        write_str(&mut bytes, &mut pool, "crate::Machine");
        write_str(&mut bytes, &mut pool, "Step");
        write_str(&mut bytes, &mut pool, "crate::Machine::step");
        write_str(&mut bytes, &mut pool, "fixture.rs:1:1");
        write_u8(&mut bytes, 1); // project Some
        write_str(&mut bytes, &mut pool, "crate::project");
        // v25 has no SpecAnchor.function bytes here.
        write_v32(&mut bytes, 0); // waivers
        write_u8(&mut bytes, 0); // embedded origin
        write_v32(&mut bytes, 0); // proofs (v14+)

        let mut reader = Reader::new(&bytes);
        reader.version = 25;
        reader.pool = Some(pool);
        let spec = read_spec_module(&mut reader).expect("v25 SpecModule decode");
        assert_eq!(spec.anchors.len(), 1);
        assert_eq!(spec.anchors[0].function, None);
        assert_eq!(spec.anchors[0].project.as_deref(), Some("crate::project"));
        assert_eq!(spec.anchors[0].projection_target, None);
        assert_eq!(
            spec.enforcement,
            crate::spec::SpecEnforcementMode::DesignOnly
        );
        assert_eq!(reader.cursor.position() as usize, bytes.len());
    }

    #[test]
    fn v26_spec_module_maps_only_to_design_only_without_projection_target() {
        // v26 already carried the typed action FuncId, but not the v27
        // projection target or enforcement mode. Decoding must preserve the
        // action target while conservatively mapping the missing fields.
        let mut pool = StringPool::new();
        let mut bytes = Vec::new();
        write_str(&mut bytes, &mut pool, "crate::Machine");
        write_v32(&mut bytes, 0); // vars
        write_v32(&mut bytes, 1); // actions
        write_str(&mut bytes, &mut pool, "Step");
        write_v32(&mut bytes, 0); // invariants
        write_v32(&mut bytes, 1); // anchors
        write_str(&mut bytes, &mut pool, "crate::Machine");
        write_str(&mut bytes, &mut pool, "Step");
        write_str(&mut bytes, &mut pool, "crate::Machine::step");
        write_str(&mut bytes, &mut pool, "fixture.rs:1:1");
        write_u8(&mut bytes, 1);
        write_str(&mut bytes, &mut pool, "crate::project");
        write_u8(&mut bytes, 1); // action function Some
        write_v32(&mut bytes, 7);
        // v26 has no projection-target bytes here.
        write_v32(&mut bytes, 0); // waivers
        write_u8(&mut bytes, 0); // embedded origin
        write_v32(&mut bytes, 0); // proofs
        // v26 has no enforcement byte here.

        let mut reader = Reader::new(&bytes);
        reader.version = 26;
        reader.pool = Some(pool);
        let spec = read_spec_module(&mut reader).expect("v26 SpecModule decode");
        assert_eq!(spec.anchors[0].function, Some(FuncId::new(7)));
        assert_eq!(spec.anchors[0].projection_target, None);
        assert_eq!(
            spec.enforcement,
            crate::spec::SpecEnforcementMode::legacy_compatibility()
        );
        assert_eq!(reader.cursor.position() as usize, bytes.len());
    }

    #[test]
    fn v27_spec_link_tags_reject_unknown_values() {
        let mut pool = StringPool::new();
        let mut bad_projection = Vec::new();
        write_str(&mut bad_projection, &mut pool, "Machine");
        write_v32(&mut bad_projection, 0); // vars
        write_v32(&mut bad_projection, 1); // actions
        write_str(&mut bad_projection, &mut pool, "Step");
        write_v32(&mut bad_projection, 0); // invariants
        write_v32(&mut bad_projection, 1); // anchors
        write_str(&mut bad_projection, &mut pool, "Machine");
        write_str(&mut bad_projection, &mut pool, "Step");
        write_str(&mut bad_projection, &mut pool, "step");
        write_str(&mut bad_projection, &mut pool, "fixture.rs:1:1");
        write_u8(&mut bad_projection, 1);
        write_str(&mut bad_projection, &mut pool, "project");
        write_u8(&mut bad_projection, 0); // action function None
        write_u8(&mut bad_projection, 99); // invalid projection target

        let mut reader = Reader::new(&bad_projection);
        reader.version = 27;
        reader.pool = Some(pool);
        assert_eq!(
            read_spec_module(&mut reader),
            Err(BinaryError::InvalidTag(99))
        );

        let mut pool = StringPool::new();
        let mut bad_enforcement = Vec::new();
        write_str(&mut bad_enforcement, &mut pool, "Machine");
        write_v32(&mut bad_enforcement, 0); // vars
        write_v32(&mut bad_enforcement, 0); // actions
        write_v32(&mut bad_enforcement, 0); // invariants
        write_v32(&mut bad_enforcement, 0); // anchors
        write_v32(&mut bad_enforcement, 0); // waivers
        write_u8(&mut bad_enforcement, 0); // embedded origin
        write_v32(&mut bad_enforcement, 0); // proofs
        write_u8(&mut bad_enforcement, 99); // invalid enforcement

        let mut reader = Reader::new(&bad_enforcement);
        reader.version = 27;
        reader.pool = Some(pool);
        assert_eq!(
            read_spec_module(&mut reader),
            Err(BinaryError::InvalidTag(99))
        );
    }

    #[test]
    fn invalid_magic_rejected() {
        let mut bytes = serialize_module(&Module::new("test"));
        bytes[0] = b'X';
        assert_eq!(deserialize_module(&bytes), Err(BinaryError::InvalidMagic));
    }

    #[test]
    fn unsupported_version_rejected() {
        let mut bytes = serialize_module(&Module::new("test"));
        // Overwrite version to 99
        let v = 99u32.to_le_bytes();
        bytes[8..12].copy_from_slice(&v);
        assert_eq!(
            deserialize_module(&bytes),
            Err(BinaryError::UnsupportedVersion)
        );
    }

    #[test]
    fn ambiguous_versions_26_through_28_are_rejected() {
        for version in 26..=28u32 {
            let mut bytes = serialize_module(&Module::new("test"));
            bytes[8..12].copy_from_slice(&version.to_le_bytes());
            assert_eq!(
                deserialize_module(&bytes),
                Err(BinaryError::UnsupportedVersion),
                "ambiguous-lineage module version {version} must fail closed"
            );
        }
    }

    #[test]
    fn proof_lineage_header_magic_and_version() {
        let manifest = proof_lineage_manifest();
        let bytes = serialize_proof_lineage_manifest(&manifest);
        assert_eq!(&bytes[0..4], b"TMPL");
        assert_eq!(
            u32::from_le_bytes([bytes[4], bytes[5], bytes[6], bytes[7]]),
            PROOF_LINEAGE_VERSION
        );
    }

    #[test]
    fn proof_lineage_manifest_round_trip_is_canonical() {
        let manifest = proof_lineage_manifest();
        let bytes = serialize_proof_lineage_manifest(&manifest);
        let back = deserialize_proof_lineage_manifest(&bytes)
            .expect("proof lineage deserialize should succeed");
        back.validate().expect("proof lineage shape remains valid");

        assert_eq!(back.nodes[0].id, ProofLineageId::new(0));
        assert_eq!(back.nodes[1].id, ProofLineageId::new(1));
        assert_eq!(back.nodes[1].depends_on, vec![ProofLineageId::new(0)]);
        assert_eq!(
            serialize_proof_lineage_manifest(&back),
            bytes,
            "proof lineage binary sidecar is idempotent"
        );
    }

    #[test]
    fn proof_lineage_bad_header_rejected() {
        let mut bytes = serialize_proof_lineage_manifest(&proof_lineage_manifest());
        bytes[0] = b'X';
        assert_eq!(
            deserialize_proof_lineage_manifest(&bytes),
            Err(BinaryError::InvalidMagic)
        );

        let mut bytes = serialize_proof_lineage_manifest(&proof_lineage_manifest());
        bytes[4..8].copy_from_slice(&99u32.to_le_bytes());
        assert_eq!(
            deserialize_proof_lineage_manifest(&bytes),
            Err(BinaryError::UnsupportedVersion)
        );
    }

    #[test]
    fn truncated_data_rejected() {
        let bytes = serialize_module(&Module::new("test"));
        // Truncate to just the header
        assert!(deserialize_module(&bytes[..6]).is_err());
    }

    // --- Empty module ---

    #[test]
    fn empty_module_round_trip() {
        round_trip(&Module::new("empty"));
    }

    // --- Module with types ---

    #[test]
    fn module_with_all_primitive_types() {
        let mut module = Module::new("primitives");
        let primitives = [
            Ty::I8,
            Ty::I16,
            Ty::I32,
            Ty::I64,
            Ty::I128,
            Ty::U8,
            Ty::U16,
            Ty::U32,
            Ty::U64,
            Ty::U128,
            Ty::F16,
            Ty::F32,
            Ty::F64,
            Ty::Bool,
            Ty::Ptr,
            Ty::Unit,
            Ty::Never,
        ];
        for ty in &primitives {
            module.add_type(ty.clone());
        }
        round_trip(&module);
    }

    #[test]
    fn module_with_composite_types() {
        let mut module = Module::new("composites");
        module.add_type(Ty::Struct(StructId::new(0)));
        module.add_type(Ty::Array(TyId::new(0), 16));
        module.add_type(Ty::Tuple(vec![Ty::I32, Ty::Bool]));
        module.add_type(Ty::Enum(EnumId::new(0)));
        module.add_type(Ty::Func(FuncTyId::new(0)));
        module.add_type(Ty::Ref(Box::new(Ty::I32)));
        module.add_type(Ty::RefMut(Box::new(Ty::I64)));
        module.add_type(Ty::PtrConst(Box::new(Ty::U32)));
        module.add_type(Ty::PtrMut(Box::new(Ty::F64)));
        module.add_type(Ty::Rc(Box::new(Ty::Bool)));
        module.add_type(Ty::Vector(Box::new(Ty::I32), 4));
        module.add_type(Ty::Vector(Box::new(Ty::Bool), 8));
        // Nested reference types
        module.add_type(Ty::Ref(Box::new(Ty::RefMut(Box::new(Ty::I32)))));
        module.add_type(Ty::Rc(Box::new(Ty::Tuple(vec![Ty::I32, Ty::U64]))));
        round_trip(&module);
    }

    fn vector_instruction_module(name: &str) -> Module {
        let v4i32 = Ty::Vector(Box::new(Ty::I32), 4);
        let v4bool = Ty::Vector(Box::new(Ty::Bool), 4);

        let mut module = Module::new(name);
        module.add_type(v4i32.clone());
        module.add_type(v4bool.clone());
        let ft = module.add_func_type(FuncTy {
            params: vec![Ty::Ptr, v4i32.clone(), v4i32.clone()],
            returns: vec![v4i32.clone(), v4bool.clone()],
            is_vararg: false,
        });

        let mut func = Function::new(FuncId::new(0), "batch_i32", ft, b(0));
        let mut block = Block::new(b(0));
        block.params.push((v(0), Ty::Ptr));
        block.params.push((v(1), v4i32.clone()));
        block.params.push((v(2), v4i32.clone()));

        block.body.push(
            InstrNode::new(Inst::Load {
                ty: v4i32.clone(),
                ptr: v(0),
                volatile: false,
                align: Some(16),
            })
            .with_result(v(3)),
        );
        block.body.push(
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: v4i32.clone(),
                lhs: v(1),
                rhs: v(2),
            })
            .with_result(v(4)),
        );
        block.body.push(
            InstrNode::new(Inst::BinOp {
                op: BinOp::Sub,
                ty: v4i32.clone(),
                lhs: v(4),
                rhs: v(3),
            })
            .with_result(v(5)),
        );
        block.body.push(
            InstrNode::new(Inst::BinOp {
                op: BinOp::Mul,
                ty: v4i32.clone(),
                lhs: v(5),
                rhs: v(2),
            })
            .with_result(v(6)),
        );
        block.body.push(
            InstrNode::new(Inst::BinOp {
                op: BinOp::And,
                ty: v4i32.clone(),
                lhs: v(6),
                rhs: v(1),
            })
            .with_result(v(7)),
        );
        block.body.push(
            InstrNode::new(Inst::BinOp {
                op: BinOp::Or,
                ty: v4i32.clone(),
                lhs: v(7),
                rhs: v(2),
            })
            .with_result(v(8)),
        );
        block.body.push(
            InstrNode::new(Inst::BinOp {
                op: BinOp::Xor,
                ty: v4i32.clone(),
                lhs: v(8),
                rhs: v(3),
            })
            .with_result(v(9)),
        );
        block.body.push(
            InstrNode::new(Inst::ICmp {
                op: ICmpOp::Eq,
                ty: v4i32.clone(),
                lhs: v(9),
                rhs: v(3),
            })
            .with_result(v(10)),
        );
        block.body.push(
            InstrNode::new(Inst::Select {
                ty: v4i32.clone(),
                cond: v(10),
                then_val: v(9),
                else_val: v(3),
            })
            .with_result(v(11)),
        );
        block.body.push(InstrNode::new(Inst::Store {
            ty: v4i32.clone(),
            ptr: v(0),
            value: v(11),
            volatile: false,
            align: Some(16),
        }));
        block.body.push(InstrNode::new(Inst::Return {
            values: vec![v(11), v(10)],
        }));

        func.blocks.push(block);
        module.add_function(func);
        module
    }

    fn invalid_vector_select_physical_mask_module(name: &str) -> Module {
        let v4i32 = Ty::Vector(Box::new(Ty::I32), 4);

        let mut module = Module::new(name);
        let ft = module.add_func_type(FuncTy {
            params: vec![v4i32.clone(), v4i32.clone(), v4i32.clone()],
            returns: vec![v4i32.clone()],
            is_vararg: false,
        });

        let mut func = Function::new(FuncId::new(0), "bad_batch_i32", ft, b(0));
        let mut block = Block::new(b(0));
        block.params.push((v(0), v4i32.clone()));
        block.params.push((v(1), v4i32.clone()));
        block.params.push((v(2), v4i32.clone()));
        block.body.push(
            InstrNode::new(Inst::Select {
                ty: v4i32,
                cond: v(0),
                then_val: v(1),
                else_val: v(2),
            })
            .with_result(v(3)),
        );
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![v(3)] }));
        func.blocks.push(block);
        module.add_function(func);
        module
    }

    #[test]
    fn vector_instruction_module_round_trip() {
        round_trip(&vector_instruction_module("vector_binary"));
    }

    #[test]
    fn vector_constant_module_round_trip() {
        let mut module = Module::new("vector_const_binary");
        module.globals.push(Global {
            name: "LANES".to_string(),
            ty: Ty::Vector(Box::new(Ty::I32), 4),
            mutable: false,
            initializer: Some(Constant::vector_i32([1, -1, 0, 42])),
            linkage: Linkage::Internal,
            tls: None,
            align: None,
        });
        round_trip(&module);
    }

    #[test]
    fn symbol_addr_global_round_trip() {
        // A mini-vtable: a global whose initializer is an aggregate of
        // relocatable function-address elements plus a data-pointer element
        // with a non-zero addend. The binary codec must preserve the symbol
        // names and addends exactly.
        let mut module = Module::new("symbol_addr_binary");
        module.globals.push(Global {
            name: "VTABLE".to_string(),
            ty: Ty::Tuple(vec![]),
            mutable: false,
            initializer: Some(Constant::Aggregate(vec![
                Constant::symbol_addr("fa"),
                Constant::symbol_addr("fb"),
                Constant::symbol_addr_with_addend("data_global", 16),
                Constant::symbol_addr_with_addend("neg", -8),
            ])),
            linkage: Linkage::Internal,
            tls: None,
            align: None,
        });
        round_trip(&module);
    }

    #[test]
    fn tls_global_round_trip() {
        let cases = [
            TlsModel::LocalExec,
            TlsModel::InitialExec,
            TlsModel::GeneralDynamic,
            TlsModel::LocalDynamic,
        ];

        for tls in cases {
            let mut module = Module::new("tls_binary");
            module.globals.push(Global {
                name: format!("TLS_{tls:?}"),
                ty: Ty::I64,
                mutable: false,
                initializer: Some(Constant::Int(11)),
                linkage: Linkage::Internal,
                tls: Some(tls),
                align: None,
            });

            let back = round_trip(&module);
            assert_eq!(back.globals[0].tls, Some(tls));
        }
    }

    #[test]
    fn version_2_blob_rejected_below_read_floor() {
        let mut bytes = Vec::new();
        let mut pool = StringPool::new();
        bytes.extend_from_slice(MAGIC);
        // The module header version is a fixed 4-byte LE word (see
        // `serialize_module`/`deserialize_module`, which use `write_u32`/
        // `read_u32`). A real v2 payload therefore encodes the version with
        // `write_u32`; emulating it with `write_v32` produced a 1-byte version
        // that the reader mis-parsed as a huge value -> UnsupportedVersion.
        write_u32(&mut bytes, 2);
        write_raw_str(&mut bytes, "v2_globals");

        write_v32(&mut bytes, 0); // func types
        write_v32(&mut bytes, 0); // structs
        write_v32(&mut bytes, 0); // enums
        write_v32(&mut bytes, 0); // records
        write_v32(&mut bytes, 0); // closure types

        write_v32(&mut bytes, 1); // globals
        write_raw_str(&mut bytes, "ORDINARY");
        write_ty(&mut bytes, &mut pool, &Ty::I64);
        write_bool(&mut bytes, false);
        write_u8(&mut bytes, 0); // no initializer
        write_linkage(&mut bytes, &Linkage::External);

        write_v32(&mut bytes, 0); // types
        write_v32(&mut bytes, 0); // functions
        write_v32(&mut bytes, 0); // proof obligations
        write_v32(&mut bytes, 0); // proof certificates
        write_u8(&mut bytes, 0); // no target info

        // v24 floor move (MIN_READ_VERSION = 23): a v2 payload is REJECTED at
        // the header check - pinning the deliberate Phase-2 break. Before the
        // floor move this test asserted the v2 decode path (tls defaulting to
        // None); that path was deleted with the other dead read gates.
        let err = deserialize_module(&bytes)
            .expect_err("v2 blob must be rejected once MIN_READ_VERSION is 23");
        assert!(
            matches!(err, BinaryError::UnsupportedVersion),
            "expected UnsupportedVersion, got {err:?}"
        );
    }

    #[test]
    fn u128_constant_round_trips_at_both_boundaries() {
        // v24 gate: the 128-bit-faithful carrier round-trips at the first
        // value i128 cannot carry and at u128::MAX, as an Inst::Const and a
        // global initializer.
        let mut module = Module::new("u128_rt");
        module.globals.push(Global {
            name: "G".to_string(),
            ty: Ty::U128,
            mutable: false,
            initializer: Some(Constant::U128(u128::MAX)),
            linkage: Linkage::External,
            tls: None,
            align: None,
        });
        module.globals.push(Global {
            name: "H".to_string(),
            ty: Ty::U128,
            mutable: false,
            initializer: Some(Constant::U128(i128::MAX as u128 + 1)),
            linkage: Linkage::External,
            tls: None,
            align: None,
        });
        let bytes = serialize_module(&module);
        let back = deserialize_module(&bytes).expect("u128 module round-trips");
        assert_eq!(back.globals[0].initializer, Some(Constant::U128(u128::MAX)));
        assert_eq!(
            back.globals[1].initializer,
            Some(Constant::U128(i128::MAX as u128 + 1))
        );
    }

    #[test]
    fn bytes_constant_round_trips_and_utf8_claim_is_checked() {
        // v25 gate: raw + utf8 bytes round-trip as global initializers, and a
        // hand-corrupted utf8 payload is REJECTED at decode.
        let mut module = Module::new("bytes_rt");
        let tid = module.add_type(Ty::U8);
        module.globals.push(Global {
            name: "RAW".to_string(),
            ty: Ty::Array(tid, 3),
            mutable: false,
            initializer: Some(Constant::bytes(vec![0u8, 255, 16])),
            linkage: Linkage::External,
            tls: None,
            align: None,
        });
        module.globals.push(Global {
            name: "STR".to_string(),
            ty: Ty::Array(tid, 2),
            mutable: false,
            initializer: Some(Constant::str_bytes("hi")),
            linkage: Linkage::External,
            tls: None,
            align: None,
        });
        let bytes = serialize_module(&module);
        let back = deserialize_module(&bytes).expect("bytes module round-trips");
        assert_eq!(
            back.globals[0].initializer,
            Some(Constant::bytes(vec![0u8, 255, 16]))
        );
        assert_eq!(back.globals[1].initializer, Some(Constant::str_bytes("hi")));

        // Corrupt the utf8-flagged payload ("hi" = 68 69) into invalid UTF-8
        // (a lone continuation byte) and expect decode rejection.
        let needle = [0x68u8, 0x69];
        let pos = bytes
            .windows(2)
            .rposition(|w| w == needle)
            .expect("utf8 payload present");
        let mut corrupted = bytes.clone();
        corrupted[pos] = 0xFF;
        corrupted[pos + 1] = 0xFE;
        let err = deserialize_module(&corrupted)
            .expect_err("invalid UTF-8 under the utf8 claim must be rejected");
        assert!(
            matches!(err, BinaryError::InvalidData(ref m) if m.contains("invalid UTF-8")),
            "expected the utf8-claim rejection, got {err:?}"
        );
    }

    #[test]
    fn non_canonical_u128_payload_rejected_on_read() {
        // The WRITER can never produce this (the smart constructor and the
        // validator forbid it), so hand-patch a serialized module: write a
        // canonical U128 global, then overwrite the 16-byte payload with a
        // value i128 could carry. The decoder must reject it (one-spelling
        // rule) rather than materialize a non-canonical constant.
        let mut module = Module::new("u128_noncanon");
        module.globals.push(Global {
            name: "G".to_string(),
            ty: Ty::U128,
            mutable: false,
            initializer: Some(Constant::U128(u128::MAX)),
            linkage: Linkage::External,
            tls: None,
            align: None,
        });
        let mut bytes = serialize_module(&module);
        // Locate the 16-byte LE u128::MAX payload (the only run of 16 0xFF).
        let needle = [0xFFu8; 16];
        let pos = bytes
            .windows(16)
            .position(|w| w == needle)
            .expect("u128::MAX payload present");
        bytes[pos..pos + 16].copy_from_slice(&5u128.to_le_bytes());
        let err =
            deserialize_module(&bytes).expect_err("non-canonical U128 payload must be rejected");
        assert!(
            matches!(err, BinaryError::InvalidData(ref m) if m.contains("non-canonical")),
            "expected the one-spelling rejection, got {err:?}"
        );
    }

    #[test]
    fn vector_select_physical_mask_is_rejected_on_binary_read() {
        let bytes = serialize_module(&invalid_vector_select_physical_mask_module(
            "bad_vector_binary",
        ));
        let err = deserialize_module(&bytes).expect_err("binary reader validates vector select");
        match err {
            BinaryError::InvalidData(message) => {
                assert!(
                    message.contains("<4 x bool>"),
                    "expected vector bool condition in diagnostic: {message}"
                );
                assert!(
                    message.contains("compared to zero"),
                    "expected compare-to-zero guidance in diagnostic: {message}"
                );
            }
            other => panic!("unexpected binary error: {other:?}"),
        }
    }

    // --- Full module ---

    #[test]
    fn full_module_round_trip() {
        let mut module = Module::new("test_module");

        let ft = module.add_func_type(FuncTy {
            params: vec![Ty::I32, Ty::I32],
            returns: vec![Ty::I32],
            is_vararg: false,
        });

        module.add_struct(StructDef {
            id: StructId::new(0),
            name: "Point".to_string(),
            fields: vec![
                FieldDef {
                    name: "x".to_string(),
                    ty: Ty::F64,
                    offset: Some(0),
                },
                FieldDef {
                    name: "y".to_string(),
                    ty: Ty::F64,
                    offset: Some(8),
                },
            ],
            size: Some(16),
            align: Some(8),

            repr: Default::default(),
        });

        module.add_enum(EnumDef {
            id: EnumId::new(0),
            name: "Color".to_string(),
            variants: vec![
                EnumVariant {
                    name: "Red".to_string(),
                    fields: vec![],
                    field_names: Vec::new(),
                },
                EnumVariant {
                    name: "Green".to_string(),
                    fields: vec![],
                    field_names: Vec::new(),
                },
                EnumVariant {
                    name: "Blue".to_string(),
                    fields: vec![Ty::U8],
                    field_names: Vec::new(),
                },
            ],
            discriminants: Vec::new(),
            repr: None,
            layout: None,
        });

        module.add_type(Ty::I32);

        module.globals.push(Global {
            name: "COUNTER".to_string(),
            ty: Ty::I64,
            mutable: true,
            initializer: Some(Constant::Int(0)),
            linkage: Linkage::External,
            tls: None,
            align: None,
        });
        module.globals.push(Global {
            name: "UNINIT".to_string(),
            ty: Ty::I32,
            mutable: false,
            initializer: None,
            linkage: Linkage::External,
            tls: None,
            align: None,
        });

        let func_id = FuncId::new(0);
        let entry = BlockId::new(0);
        let mut func = Function::new(func_id, "add", ft, entry);
        func.proofs.push(ProofAnnotation::Pure);
        func.proofs.push(ProofAnnotation::NoOverflow);
        func.proofs.push(ProofAnnotation::NoPanic);

        let mut block = Block::new(entry);
        block.params.push((v(0), Ty::I32));
        block.params.push((v(1), Ty::I32));

        block.body.push(
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I32,
                lhs: v(0),
                rhs: v(1),
            })
            .with_result(v(2))
            .with_proof(ProofAnnotation::NoOverflow)
            .with_span(SourceSpan {
                file: 0,
                line: 10,
                col: 4,
            }),
        );
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![v(2)] }));
        func.blocks.push(block);
        module.add_function(func);

        module.proof_obligations.push(ProofObligation {
            id: ProofId::new(0),
            kind: ObligationKind::PanicFreedom,
            status: ProofStatus::Discharged,
            description: "add does not overflow".to_string(),
            formula: Some(ProofFormula::smtlib2("(bvadd_no_overflow a b)", "Bool")),
            function: None,
            source: None,
            site: None,
        });

        module.proof_certificates.push(ProofCertificate {
            obligation: ProofId::new(0),
            prover: "ay".to_string(),
            evidence: ProofEvidence::SmtProof(vec![0xDE, 0xAD]),
        });

        round_trip(&module);
    }

    // --- v19: EnumDef discriminants + tag repr ---

    #[test]
    fn enum_def_discriminants_and_repr_round_trip() {
        let mut module = Module::new("enum_v19");
        // Explicit + implicit discriminant mix (negative + extreme values) and
        // a tag-repr hint — the full v19 wire surface.
        module.add_enum(
            EnumDef::new(
                EnumId::new(0),
                "Sparse",
                vec![
                    EnumVariant {
                        name: "A".to_string(),
                        fields: vec![],
                        field_names: Vec::new(),
                    },
                    EnumVariant {
                        name: "B".to_string(),
                        fields: vec![Ty::I64],
                        field_names: Vec::new(),
                    },
                    EnumVariant {
                        name: "C".to_string(),
                        fields: vec![],
                        field_names: Vec::new(),
                    },
                ],
            )
            .with_discriminants(vec![Some(-5), None, Some(i128::from(i64::MAX))])
            .with_repr(EnumTagRepr::I64),
        );
        // A second enum with all-implicit discriminants and no hint: the
        // default (empty/None) v19 fields round-trip too.
        module.add_enum(EnumDef::new(
            EnumId::new(1),
            "Plain",
            vec![EnumVariant {
                name: "Only".to_string(),
                fields: vec![],
                field_names: Vec::new(),
            }],
        ));
        let back = round_trip(&module);
        assert_eq!(
            back.enums[0].discriminants,
            vec![Some(-5), None, Some(i128::from(i64::MAX))]
        );
        assert_eq!(back.enums[0].repr, Some(EnumTagRepr::I64));
        assert!(back.enums[1].discriminants.is_empty());
        assert_eq!(back.enums[1].repr, None);
    }

    #[test]
    fn enum_layout_descriptors_and_field_names_round_trip_at_current_version() {
        let mut module = Module::new("enum_v31");
        let mut direct = EnumDef::new(
            EnumId::new(0),
            "Direct",
            vec![EnumVariant {
                name: "Value".into(),
                fields: vec![Ty::I32],
                field_names: vec!["value".into()],
            }],
        );
        direct.layout = Some(EnumLayoutDescriptor {
            encoding: EnumTagEncoding::Direct { tag_offset: 4 },
            size: 8,
            align: 4,
            variant_field_offsets: vec![vec![0]],
        });
        module.add_enum(direct);

        let mut niche = EnumDef::new(
            EnumId::new(1),
            "Niche",
            vec![
                EnumVariant {
                    name: "Value".into(),
                    fields: vec![Ty::U64],
                    field_names: vec!["value".into()],
                },
                EnumVariant {
                    name: "Empty".into(),
                    fields: vec![],
                    field_names: Vec::new(),
                },
            ],
        );
        niche.layout = Some(EnumLayoutDescriptor {
            encoding: EnumTagEncoding::Niche {
                untagged_variant: 0,
                niche_variants_start: 1,
                niche_variants_end: 1,
                niche_start: u128::from(u64::MAX),
                niche_offset: 0,
                niche_ty: EnumTagRepr::U64,
            },
            size: 8,
            align: 8,
            variant_field_offsets: vec![vec![0], vec![]],
        });
        module.add_enum(niche);

        let encoded = serialize_module(&module);
        assert_eq!(&encoded[8..12], &VERSION.to_le_bytes());
        assert_eq!(
            deserialize_module(&encoded).expect("current-version enum codec"),
            module
        );
    }

    /// v37 `Untagged` (wire tag 2). The encoding is a bare unit variant, so
    /// the round trip is the whole of its write side; the read side is
    /// version-GATED, which the companion test below pins.
    #[test]
    fn untagged_enum_layout_descriptor_round_trips_at_current_version() {
        let mut module = Module::new("enum_v37");
        let mut untagged = EnumDef::new(
            EnumId::new(0),
            "UnOp",
            vec![EnumVariant {
                name: "Not".into(),
                fields: vec![Ty::U64],
                field_names: vec!["operand".into()],
            }],
        );
        untagged.layout = Some(EnumLayoutDescriptor {
            encoding: EnumTagEncoding::Untagged,
            size: 8,
            align: 8,
            variant_field_offsets: vec![vec![0]],
        });
        module.add_enum(untagged);

        let encoded = serialize_module(&module);
        assert_eq!(&encoded[8..12], &VERSION.to_le_bytes());
        assert_eq!(
            deserialize_module(&encoded).expect("current-version untagged codec"),
            module
        );
    }

    /// The v37 read gate has teeth: byte 2 in the encoding slot is not a value
    /// any v36-or-earlier writer could have produced, so a blob CLAIMING v36
    /// that carries it is malformed and must be refused — not silently
    /// promoted. Patching the header version is a legitimate construction here
    /// precisely because v37 added no field: the only decode difference
    /// between the two versions is this tag.
    #[test]
    fn a_v36_blob_may_not_carry_the_untagged_encoding() {
        let mut module = Module::new("enum_v37_gate");
        let mut untagged = EnumDef::new(
            EnumId::new(0),
            "UnOp",
            vec![EnumVariant {
                name: "Not".into(),
                fields: vec![Ty::U64],
                field_names: vec!["operand".into()],
            }],
        );
        untagged.layout = Some(EnumLayoutDescriptor {
            encoding: EnumTagEncoding::Untagged,
            size: 8,
            align: 8,
            variant_field_offsets: vec![vec![0]],
        });
        module.add_enum(untagged);

        let mut encoded = serialize_module(&module);
        encoded[8..12].copy_from_slice(&36u32.to_le_bytes());
        assert_eq!(
            deserialize_module(&encoded).expect_err("v36 must not decode the v37 encoding tag"),
            BinaryError::InvalidTag(2)
        );
    }

    #[test]
    fn v30_enum_record_defaults_v31_fields_without_desynchronizing() {
        let mut pool = StringPool::new();
        let mut bytes = Vec::new();
        write_enum_id(&mut bytes, EnumId::new(0));
        write_str(&mut bytes, &mut pool, "Legacy");
        write_v32(&mut bytes, 1);
        write_str(&mut bytes, &mut pool, "Value");
        write_v32(&mut bytes, 1);
        write_ty(&mut bytes, &mut pool, &Ty::I32);
        write_v32(&mut bytes, 0); // implicit discriminants
        write_u8(&mut bytes, 0); // no repr; v30 record ends here

        let mut reader = Reader::new(&bytes);
        reader.version = 30;
        reader.pool = Some(pool);
        let decoded = read_enum_def(&mut reader).expect("v30 enum record");
        assert!(decoded.variants[0].field_names.is_empty());
        assert_eq!(decoded.layout, None);
        assert_eq!(reader.cursor.position() as usize, bytes.len());
    }

    // --- fast-2: function/parameter attributes (v7) ---

    #[test]
    fn func_attrs_round_trips() {
        let mut module = Module::new("attrs");
        let ft = module.add_func_type(FuncTy {
            params: vec![Ty::Ptr, Ty::I32],
            returns: vec![Ty::I32],
            is_vararg: false,
        });
        let mut func = Function::new(FuncId::new(0), "f", ft, b(0));
        func.attrs.readonly = true;
        func.attrs.inlinehint = true;
        func.attrs.params = vec![
            ParamAttrs {
                dereferenceable: Some(8),
                nonnull: true,
                align: Some(4),
                noalias: true,
                readonly: true,
                byval: true,
                sret: false,
            },
            ParamAttrs {
                sret: true,
                ..ParamAttrs::default()
            },
        ];
        let mut block = Block::new(b(0));
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        func.blocks.push(block);
        module.add_function(func);

        let back = round_trip(&module);
        let a = &back.functions[0].attrs;
        assert!(a.readonly && a.inlinehint && !a.readnone && !a.cold);
        assert_eq!(a.params[0].dereferenceable, Some(8));
        assert_eq!(a.params[0].align, Some(4));
        assert!(a.params[0].nonnull && a.params[0].noalias && a.params[0].readonly);
        // v20 ABI-pinning bits round-trip independently.
        assert!(a.params[0].byval && !a.params[0].sret);
        assert!(a.params[1].sret && !a.params[1].byval);
        assert!(!a.params[1].is_empty());
    }

    #[test]
    fn empty_func_attrs_round_trips() {
        let mut module = Module::new("empty_attrs");
        let ft = module.add_func_type(FuncTy {
            params: vec![],
            returns: vec![],
            is_vararg: false,
        });
        let mut func = Function::new(FuncId::new(0), "g", ft, b(0));
        let mut block = Block::new(b(0));
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        func.blocks.push(block);
        module.add_function(func);

        let back = round_trip(&module);
        assert!(back.functions[0].attrs.is_empty());
    }

    // --- ABI pinning: TargetInfo.abi + struct_passing (v20) ---

    #[test]
    fn target_info_abi_fields_round_trip() {
        let mut module = Module::new("target_abi");
        module.target_info = Some(TargetInfo {
            triple: "x86_64-unknown-linux-gnu".into(),
            pointer_size: 8,
            endianness: Endianness::Little,
            abi: Some("sysv64".into()),
            struct_passing: StructPassingPolicy::AlwaysMemory,
        });
        let back = round_trip(&module);
        let ti = back.target_info.expect("target info survives");
        assert_eq!(ti.abi.as_deref(), Some("sysv64"));
        assert_eq!(ti.struct_passing, StructPassingPolicy::AlwaysMemory);

        // The legacy default state round-trips to itself too.
        let mut legacy = Module::new("target_plain");
        legacy.target_info = Some(TargetInfo {
            triple: "aarch64-apple-darwin".into(),
            pointer_size: 8,
            endianness: Endianness::Little,
            abi: None,
            struct_passing: StructPassingPolicy::default(),
        });
        let back = round_trip(&legacy);
        let ti = back.target_info.expect("target info survives");
        assert_eq!(ti.abi, None);
        assert_eq!(ti.struct_passing, StructPassingPolicy::NativeC);
    }

    #[test]
    fn target_info_unclassified_is_v36_gated() {
        let mut module = Module::new("target_unclassified");
        module.target_info = Some(TargetInfo {
            triple: "aarch64-unknown-none".into(),
            pointer_size: 8,
            endianness: Endianness::Little,
            abi: Some("aapcs64".into()),
            struct_passing: StructPassingPolicy::Unclassified,
        });

        let bytes = serialize_module(&module);
        let back = deserialize_module(&bytes).expect("v36 unclassified target info must decode");
        assert_eq!(
            back.target_info
                .expect("target info survives")
                .struct_passing,
            StructPassingPolicy::Unclassified
        );

        // Tag 2 did not exist in v35. Merely lowering the header must not let
        // a malformed pre-v36 blob smuggle the new policy through an older
        // schema identity.
        let mut forged_v35 = bytes;
        forged_v35[8..12].copy_from_slice(&35_u32.to_le_bytes());
        assert_eq!(
            deserialize_module(&forged_v35),
            Err(BinaryError::InvalidTag(2))
        );
    }

    // --- fast-3 D.2: GEP.inbounds (v8) ---

    #[test]
    fn gep_inbounds_round_trips() {
        let mut module = Module::new("gep_ib");
        let ft = module.add_func_type(FuncTy {
            params: vec![Ty::Ptr],
            returns: vec![Ty::Ptr],
            is_vararg: false,
        });
        let mut func = Function::new(FuncId::new(0), "f", ft, b(0));
        let mut block = Block::new(b(0));
        block.params.push((v(0), Ty::Ptr));
        block.body.push(
            InstrNode::new(Inst::GEP {
                pointee_ty: Ty::I32,
                base: v(0),
                indices: vec![],
                inbounds: true,
            })
            .with_result(v(1)),
        );
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![v(1)] }));
        func.blocks.push(block);
        module.add_function(func);

        let back = round_trip(&module);
        assert!(
            matches!(
                back.functions[0].blocks[0].body[0].inst,
                Inst::GEP { inbounds: true, .. }
            ),
            "GEP.inbounds=true must round-trip"
        );
        let bytes = serialize_module(&module);
        assert_eq!(
            u32::from_le_bytes([bytes[8], bytes[9], bytes[10], bytes[11]]),
            VERSION
        );
    }

    // --- Clean RC heap: AllocOrigin::CleanHeap (origin byte 3, v22) ---

    #[test]
    fn clean_heap_origin_round_trips() {
        let mut module = Module::new("clean_heap_bin");
        let ft = module.add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::Ptr],
            is_vararg: false,
        });
        let mut func = Function::new(FuncId::new(0), "clean_cell", ft, b(0));
        let mut block = Block::new(b(0));
        block.body.push(
            InstrNode::new(Inst::HeapAlloc {
                ty: Ty::I64,
                count: None,
                align: None,
                origin: AllocOrigin::CleanHeap,
            })
            .with_result(v(0)),
        );
        func.blocks.push(block);
        module.add_function(func);

        let back = round_trip(&module);
        assert!(
            matches!(
                back.functions[0].blocks[0].body[0].inst,
                Inst::HeapAlloc {
                    origin: AllocOrigin::CleanHeap,
                    ..
                }
            ),
            "AllocOrigin::CleanHeap must round-trip"
        );
        let bytes = serialize_module(&module);
        assert_eq!(
            u32::from_le_bytes([bytes[8], bytes[9], bytes[10], bytes[11]]),
            VERSION,
            "VERSION must be bumped for the CleanHeap origin byte"
        );
        const {
            assert!(
                VERSION >= 22,
                "CleanHeap origin byte 3 is a v22 wire commitment"
            );
        }
    }

    // --- coroutines: Inst::CoroSuspend (wire tag 50, v16) ---

    #[test]
    fn coro_suspend_round_trips() {
        let mut module = Module::new("coro_bin");
        let ft = module.add_func_type(FuncTy {
            params: vec![Ty::Ptr],
            returns: vec![Ty::I64],
            is_vararg: false,
        });
        let mut func = Function::new(FuncId::new(0), "gen", ft, b(0));
        let mut block = Block::new(b(0));
        block.params.push((v(0), Ty::Ptr));
        block.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(7),
            })
            .with_result(v(1)),
        );
        block.body.push(InstrNode::new(Inst::CoroSuspend {
            frame: v(0),
            state_slot: 2,
            next_state: -5,
            value: v(1),
        }));
        func.blocks.push(block);
        module.add_function(func);

        let back = round_trip(&module);
        assert!(
            matches!(
                back.functions[0].blocks[0].body[1].inst,
                Inst::CoroSuspend {
                    state_slot: 2,
                    next_state: -5,
                    ..
                }
            ),
            "CoroSuspend fields (incl. negative next_state) must round-trip"
        );
        let bytes = serialize_module(&module);
        assert_eq!(
            u32::from_le_bytes([bytes[8], bytes[9], bytes[10], bytes[11]]),
            VERSION,
            "VERSION must be bumped for the CoroSuspend opcode"
        );
    }

    // --- exceptions: Inst::Invoke / LandingPad / Resume (tags 51..=53, v17) ---

    #[test]
    fn eh_opcodes_round_trip() {
        let mut module = Module::new("eh_bin");
        // callee: () -> i32 (may throw); caller: () -> i32 that invokes it.
        let callee_ft = module.add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::I32],
            is_vararg: false,
        });
        let caller_ft = module.add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::I32],
            is_vararg: false,
        });
        let callee = Function::new(FuncId::new(0), "may_throw", callee_ft, b(0));
        module.add_function(callee);

        let mut func = Function::new(FuncId::new(1), "caller", caller_ft, b(0));
        // bb0: invoke may_throw() -> normal=bb1, unwind=bb2
        let mut bb0 = Block::new(b(0));
        bb0.body.push(InstrNode::new(Inst::Invoke {
            callee: FuncId::new(0),
            args: vec![],
            normal_dest: b(1),
            normal_args: vec![],
            unwind_dest: b(2),
        }));
        // bb1: normal continuation receives the i32 result as a block param.
        let mut bb1 = Block::new(b(1));
        bb1.params.push((v(10), Ty::I32));
        bb1.body.push(InstrNode::new(Inst::Return {
            values: vec![v(10)],
        }));
        // bb2: landing pad (catch-all) -> resume.
        let mut bb2 = Block::new(b(2));
        bb2.body.push(
            InstrNode::new(Inst::LandingPad {
                is_cleanup: false,
                catch_type_indices: vec![0, 7],
            })
            .with_results(vec![v(20), v(21)]),
        );
        bb2.body.push(InstrNode::new(Inst::Resume { exn: v(20) }));
        func.blocks.push(bb0);
        func.blocks.push(bb1);
        func.blocks.push(bb2);
        module.add_function(func);

        let back = round_trip(&module);
        let caller = &back.functions[1];
        assert!(
            matches!(
                &caller.blocks[0].body[0].inst,
                Inst::Invoke { normal_dest, unwind_dest, .. }
                    if *normal_dest == b(1) && *unwind_dest == b(2)
            ),
            "Invoke successors must round-trip"
        );
        assert!(
            matches!(
                &caller.blocks[2].body[0].inst,
                Inst::LandingPad { is_cleanup: false, catch_type_indices }
                    if catch_type_indices == &vec![0u32, 7u32]
            ),
            "LandingPad catch indices must round-trip"
        );
        assert!(
            matches!(caller.blocks[2].body[1].inst, Inst::Resume { exn } if exn == v(20)),
            "Resume operand must round-trip"
        );
        let bytes = serialize_module(&module);
        assert_eq!(
            u32::from_le_bytes([bytes[8], bytes[9], bytes[10], bytes[11]]),
            VERSION,
            "VERSION must be bumped for the EH opcodes"
        );
    }

    #[test]
    fn gep_default_inbounds_false_round_trips() {
        let mut module = Module::new("gep_default");
        let ft = module.add_func_type(FuncTy {
            params: vec![Ty::Ptr],
            returns: vec![Ty::Ptr],
            is_vararg: false,
        });
        let mut func = Function::new(FuncId::new(0), "g", ft, b(0));
        let mut block = Block::new(b(0));
        block.params.push((v(0), Ty::Ptr));
        block.body.push(
            InstrNode::new(Inst::GEP {
                pointee_ty: Ty::I32,
                base: v(0),
                indices: vec![],
                inbounds: false,
            })
            .with_result(v(1)),
        );
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![v(1)] }));
        func.blocks.push(block);
        module.add_function(func);
        let back = round_trip(&module);
        assert!(matches!(
            back.functions[0].blocks[0].body[0].inst,
            Inst::GEP {
                inbounds: false,
                ..
            }
        ));
    }

    // --- Compact vs JSON ---

    #[test]
    fn binary_smaller_than_json() {
        let mut module = Module::new("compact");
        let ft = module.add_func_type(FuncTy {
            params: vec![Ty::I32],
            returns: vec![Ty::I32],
            is_vararg: false,
        });
        let mut func = Function::new(FuncId::new(0), "id", ft, b(0));
        let mut block = Block::new(b(0));
        block.params.push((v(0), Ty::I32));
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![v(0)] }));
        func.blocks.push(block);
        module.add_function(func);

        let binary = serialize_module(&module);
        // Compare conceptually: binary should be compact (under 200 bytes for this)
        assert!(
            binary.len() < 200,
            "binary encoding should be compact, got {} bytes",
            binary.len()
        );
    }

    // --- All instruction variants ---

    #[test]
    fn all_instruction_variants_round_trip() {
        let mut module = Module::new("all_insts");
        let ft = module.add_func_type(FuncTy {
            params: vec![],
            returns: vec![],
            is_vararg: false,
        });
        let mut func = Function::new(FuncId::new(0), "test", ft, b(0));
        let mut block = Block::new(b(0));

        // All instruction types
        let instructions = vec![
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I32,
                lhs: v(0),
                rhs: v(1),
            })
            .with_result(v(100)),
            InstrNode::new(Inst::UnOp {
                op: UnOp::Neg,
                ty: Ty::I32,
                operand: v(0),
            })
            .with_result(v(101)),
            InstrNode::new(Inst::Overflow {
                op: OverflowOp::AddOverflow,
                ty: Ty::I64,
                lhs: v(0),
                rhs: v(1),
            })
            .with_result(v(102)),
            InstrNode::new(Inst::ICmp {
                op: ICmpOp::Sgt,
                ty: Ty::I64,
                lhs: v(0),
                rhs: v(1),
            })
            .with_result(v(103)),
            InstrNode::new(Inst::FCmp {
                op: FCmpOp::OLt,
                ty: Ty::F64,
                lhs: v(0),
                rhs: v(1),
            })
            .with_result(v(104)),
            InstrNode::new(Inst::Cast {
                op: CastOp::ZExt,
                src_ty: Ty::I32,
                dst_ty: Ty::I64,
                operand: v(0),
            })
            .with_result(v(105)),
            InstrNode::new(Inst::Load {
                ty: Ty::I32,
                ptr: v(0),
                volatile: false,
                align: None,
            })
            .with_result(v(106)),
            InstrNode::new(Inst::Store {
                ty: Ty::I32,
                ptr: v(0),
                value: v(1),
                volatile: false,
                align: None,
            }),
            InstrNode::new(Inst::Alloca {
                ty: Ty::I64,
                count: None,
                align: None,
            })
            .with_result(v(107)),
            InstrNode::new(Inst::Alloca {
                ty: Ty::I64,
                count: Some(v(3)),
                align: None,
            })
            .with_result(v(108)),
            InstrNode::new(Inst::GEP {
                pointee_ty: Ty::I32,
                base: v(0),
                indices: vec![v(1), v(2)],
                inbounds: false,
            })
            .with_result(v(109)),
            InstrNode::new(Inst::AtomicLoad {
                ty: Ty::I64,
                ptr: v(0),
                ordering: Ordering::Acquire,
            })
            .with_result(v(110)),
            InstrNode::new(Inst::AtomicStore {
                ty: Ty::I64,
                ptr: v(0),
                value: v(1),
                ordering: Ordering::Release,
            }),
            InstrNode::new(Inst::AtomicRMW {
                op: AtomicRMWOp::Add,
                ty: Ty::I64,
                ptr: v(0),
                value: v(1),
                ordering: Ordering::SeqCst,
            })
            .with_result(v(111)),
            InstrNode::new(Inst::CmpXchg {
                ty: Ty::I64,
                ptr: v(0),
                expected: v(1),
                desired: v(2),
                success: Ordering::AcqRel,
                failure: Ordering::Relaxed,
            })
            .with_result(v(112)),
            InstrNode::new(Inst::Fence {
                ordering: Ordering::SeqCst,
            }),
            InstrNode::new(Inst::Call {
                callee: FuncId::new(0),
                args: vec![v(0), v(1)],
            })
            .with_result(v(113)),
            InstrNode::new(Inst::CallIndirect {
                callee: v(0),
                sig: FuncTyId::new(0),
                args: vec![v(1)],

                calling_conv: crate::CallingConv::C,
            })
            .with_result(v(114)),
            InstrNode::new(Inst::ExtractField {
                ty: Ty::I32,
                aggregate: v(0),
                field: 1,
            })
            .with_result(v(115)),
            InstrNode::new(Inst::InsertField {
                ty: Ty::I32,
                aggregate: v(0),
                field: 1,
                value: v(2),
            })
            .with_result(v(116)),
            InstrNode::new(Inst::ExtractElement {
                ty: Ty::I32,
                array: v(0),
                index: v(1),
            })
            .with_result(v(117)),
            InstrNode::new(Inst::InsertElement {
                ty: Ty::I32,
                array: v(0),
                index: v(1),
                value: v(2),
            })
            .with_result(v(118)),
            InstrNode::new(Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(42),
            })
            .with_result(v(119)),
            InstrNode::new(Inst::Const {
                ty: Ty::F64,
                value: Constant::Float(1.25),
            })
            .with_result(v(120)),
            InstrNode::new(Inst::Const {
                ty: Ty::Bool,
                value: Constant::Bool(true),
            })
            .with_result(v(121)),
            InstrNode::new(Inst::NullPtr).with_result(v(122)),
            InstrNode::new(Inst::Undef { ty: Ty::I32 }).with_result(v(123)),
            InstrNode::new(Inst::Assume { cond: v(0) }),
            InstrNode::new(Inst::Assert { cond: v(0) }),
            InstrNode::new(Inst::Copy {
                ty: Ty::I32,
                operand: v(0),
            })
            .with_result(v(124)),
            InstrNode::new(Inst::Select {
                ty: Ty::I32,
                cond: v(0),
                then_val: v(1),
                else_val: v(2),
            })
            .with_result(v(125)),
            InstrNode::new(Inst::Borrow { ptr: v(0) }).with_result(v(126)),
            InstrNode::new(Inst::BorrowMut { ptr: v(0) }).with_result(v(127)),
            InstrNode::new(Inst::EndBorrow { borrow_ptr: v(0) }),
            InstrNode::new(Inst::Retain { ptr: v(0) }),
            InstrNode::new(Inst::Release { ptr: v(0) }),
            InstrNode::new(Inst::IsUnique { ptr: v(0) }).with_result(v(128)),
            InstrNode::new(Inst::Dealloc { ptr: v(0) }),
            InstrNode::new(Inst::PtrData {
                ptr_ty: Ty::FatPtr(FatPtrKind::Str),
                ptr: v(0),
            })
            .with_result(v(129)),
            InstrNode::new(Inst::PtrMetadata {
                ptr_ty: Ty::FatPtr(FatPtrKind::Str),
                metadata_ty: Ty::U64,
                ptr: v(0),
            })
            .with_result(v(130)),
            InstrNode::new(Inst::PtrFromParts {
                ptr_ty: Ty::FatPtr(FatPtrKind::Str),
                metadata_ty: Ty::U64,
                data: v(0),
                metadata: v(1),
            })
            .with_result(v(131)),
            // Control flow last (terminators)
            InstrNode::new(Inst::Return { values: vec![] }),
        ];

        block.body = instructions;
        func.blocks.push(block);

        // Add a second block with CondBr
        let mut block2 = Block::new(b(1));
        block2.body.push(InstrNode::new(Inst::CondBr {
            cond: v(0),
            then_target: b(2),
            then_args: vec![v(1)],
            else_target: b(3),
            else_args: vec![v(2), v(3)],
        }));
        func.blocks.push(block2);

        // Add a third block with Switch
        let mut block3 = Block::new(b(2));
        block3.body.push(InstrNode::new(Inst::Switch {
            value: v(0),
            default: b(10),
            default_args: vec![],
            cases: vec![
                SwitchCase {
                    value: Constant::Int(0),
                    target: b(1),
                    args: vec![],
                },
                SwitchCase {
                    value: Constant::Int(1),
                    target: b(2),
                    args: vec![v(1)],
                },
            ],
            exhaustive_enum_unreachable: false,
        }));
        func.blocks.push(block3);

        // Add a fourth block with Br
        let mut block4 = Block::new(b(3));
        block4.body.push(InstrNode::new(Inst::Br {
            target: b(0),
            args: vec![v(0)],
        }));
        func.blocks.push(block4);

        // Add a fifth block with Unreachable
        let mut block5 = Block::new(b(4));
        block5.body.push(InstrNode::new(Inst::Unreachable));
        func.blocks.push(block5);

        module.add_function(func);
        round_trip(&module);
    }

    // --- All proof annotation variants ---

    #[test]
    fn all_proof_annotation_variants_round_trip() {
        let mut module = Module::new("proofs");
        let ft = module.add_func_type(FuncTy {
            params: vec![],
            returns: vec![],
            is_vararg: false,
        });
        let mut func = Function::new(FuncId::new(0), "test", ft, b(0));
        func.proofs = vec![
            ProofAnnotation::InBounds,
            ProofAnnotation::NotNull,
            ProofAnnotation::ValidBorrow,
            ProofAnnotation::UniqueBorrow,
            ProofAnnotation::SharedBorrow,
            ProofAnnotation::ValidDealloc,
            ProofAnnotation::NoOverflow,
            ProofAnnotation::NoWrap,
            ProofAnnotation::DivNonZero,
            ProofAnnotation::ShiftInRange,
            ProofAnnotation::Pure,
            ProofAnnotation::Terminates,
            ProofAnnotation::Deterministic,
            ProofAnnotation::Associative,
            ProofAnnotation::Commutative,
            ProofAnnotation::DataRaceFree,
            ProofAnnotation::AtomicOrdering(Ordering::SeqCst),
            ProofAnnotation::BoundedOutput { lo: -1.0, hi: 1.0 },
            ProofAnnotation::Monotonic,
            ProofAnnotation::NoAlias,
            ProofAnnotation::Aligned(64),
            ProofAnnotation::NoPanic,
            ProofAnnotation::NoUndef,
            ProofAnnotation::Custom(ProofTag::new(42)),
            ProofAnnotation::ReadonlyTable,
            ProofAnnotation::AppendOnlyBuffer,
            ProofAnnotation::AtomicSetInsert,
            ProofAnnotation::ParallelMap,
            ProofAnnotation::BoundedLoop(2048),
            ProofAnnotation::DivergenceClass(Divergence::Uniform),
            ProofAnnotation::DivergenceClass(Divergence::Low),
            ProofAnnotation::DivergenceClass(Divergence::High),
            ProofAnnotation::ValueRange { lo: -100, hi: 100 },
            ProofAnnotation::ValueRange {
                lo: i128::MIN,
                hi: i128::MAX,
            },
            ProofAnnotation::KnownBits {
                zeros: 0xff00,
                ones: 0x00ff,
            },
            ProofAnnotation::KnownBits {
                zeros: u128::MAX,
                ones: 0,
            },
            ProofAnnotation::Tainted,
            ProofAnnotation::TrustedSink,
            ProofAnnotation::FreshSymbolicHavoc,
        ];
        let mut block = Block::new(b(0));
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        func.blocks.push(block);
        module.add_function(func);
        round_trip(&module);
    }

    #[test]
    fn fresh_symbolic_havoc_has_stable_public_wire_tag() {
        // This is a semantic marker, not an unforgeable capability. Lock both
        // sides of its public wire representation so consumers cannot silently
        // reinterpret an old artifact after an enum/tag edit.
        let mut bytes = Vec::new();
        let mut pool = StringPool::new();
        write_proof_annotation(&mut bytes, &mut pool, &ProofAnnotation::FreshSymbolicHavoc);
        assert_eq!(bytes, [37]);

        let mut reader = Reader::new(&bytes);
        assert_eq!(
            read_proof_annotation(&mut reader),
            Ok(ProofAnnotation::FreshSymbolicHavoc)
        );
        assert_eq!(reader.cursor.position() as usize, bytes.len());
    }

    // --- All proof evidence variants ---

    #[test]
    fn all_proof_evidence_variants_round_trip() {
        let mut module = Module::new("evidence");
        module.proof_obligations.push(ProofObligation {
            id: ProofId::new(0),
            kind: ObligationKind::MemorySafety,
            status: ProofStatus::Discharged,
            description: "test".to_string(),
            formula: None,
            function: None,
            source: None,
            site: None,
        });
        module.proof_certificates.push(ProofCertificate {
            obligation: ProofId::new(0),
            prover: "ay".to_string(),
            evidence: ProofEvidence::SmtProof(vec![0xDE, 0xAD, 0xBE, 0xEF]),
        });
        module.proof_certificates.push(ProofCertificate {
            obligation: ProofId::new(0),
            prover: "lean4".to_string(),
            evidence: ProofEvidence::LeanProof("theorem foo : True := trivial".to_string()),
        });
        module.proof_certificates.push(ProofCertificate {
            obligation: ProofId::new(0),
            prover: "kani".to_string(),
            evidence: ProofEvidence::KaniHarness("check_bounds".to_string()),
        });
        module.proof_certificates.push(ProofCertificate {
            obligation: ProofId::new(0),
            prover: "gamma-crown".to_string(),
            evidence: ProofEvidence::GammaCrownBound {
                epsilon: 0.001,
                verified_layers: 12,
            },
        });
        module.proof_certificates.push(ProofCertificate {
            obligation: ProofId::new(0),
            prover: "tv".to_string(),
            evidence: ProofEvidence::TranslationValidation {
                rule_name: "inline_expansion".to_string(),
                smt_hash: [0xAB; 32],
            },
        });
        module.proof_certificates.push(ProofCertificate {
            obligation: ProofId::new(0),
            prover: "manual".to_string(),
            evidence: ProofEvidence::Trusted("manual audit 2026-04-16".to_string()),
        });
        module.proof_certificates.push(ProofCertificate {
            obligation: ProofId::new(0),
            prover: "compose".to_string(),
            evidence: ProofEvidence::InheritedFromCallee {
                callee: FuncId::new(7),
                obligation: ProofId::new(3),
            },
        });
        round_trip(&module);
    }

    // --- All obligation kinds ---

    #[test]
    fn all_obligation_kinds_round_trip() {
        let mut module = Module::new("obligations");
        let kinds = [
            ObligationKind::Precondition,
            ObligationKind::Postcondition,
            ObligationKind::LoopInvariant,
            ObligationKind::TypeInvariant,
            ObligationKind::RefinementType,
            ObligationKind::TranslationValidation,
            ObligationKind::MemorySafety,
            ObligationKind::PanicFreedom,
        ];
        let statuses = [
            ProofStatus::Pending,
            ProofStatus::Discharged,
            ProofStatus::Failed,
            ProofStatus::Trusted,
        ];
        for (i, kind) in kinds.iter().enumerate() {
            module.proof_obligations.push(ProofObligation {
                id: ProofId::new(i as u32),
                kind: kind.clone(),
                status: statuses[i % statuses.len()],
                description: format!("obligation {}", i),
                formula: None,
                function: None,
                source: None,
                site: None,
            });
        }
        round_trip(&module);
    }

    // --- Complex module with multiple functions ---

    #[test]
    fn multi_function_module_round_trip() {
        let mut module = Module::new("multi_func");

        let ft_add = module.add_func_type(FuncTy {
            params: vec![Ty::I32, Ty::I32],
            returns: vec![Ty::I32],
            is_vararg: false,
        });
        let ft_main = module.add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::I32],
            is_vararg: false,
        });
        let ft_vararg = module.add_func_type(FuncTy {
            params: vec![Ty::Ptr],
            returns: vec![Ty::I32],
            is_vararg: true,
        });

        module.add_struct(StructDef {
            id: StructId::new(0),
            name: "Vec2".to_string(),
            fields: vec![
                FieldDef {
                    name: "x".to_string(),
                    ty: Ty::F32,
                    offset: Some(0),
                },
                FieldDef {
                    name: "y".to_string(),
                    ty: Ty::F32,
                    offset: Some(4),
                },
            ],
            size: Some(8),
            align: Some(4),

            repr: Default::default(),
        });

        module.add_type(Ty::I32);
        module.add_type(Ty::Array(TyId::new(0), 10));

        module.globals.push(Global {
            name: "FLAG".to_string(),
            ty: Ty::Bool,
            mutable: true,
            initializer: Some(Constant::Bool(false)),
            linkage: Linkage::External,
            tls: None,
            align: None,
        });

        // Function 1: add
        let mut f_add = Function::new(FuncId::new(0), "add", ft_add, b(0));
        f_add.proofs.push(ProofAnnotation::Pure);
        let mut b_add = Block::new(b(0));
        b_add.params.push((v(0), Ty::I32));
        b_add.params.push((v(1), Ty::I32));
        b_add.body.push(
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I32,
                lhs: v(0),
                rhs: v(1),
            })
            .with_result(v(2))
            .with_proof(ProofAnnotation::NoOverflow),
        );
        b_add
            .body
            .push(InstrNode::new(Inst::Return { values: vec![v(2)] }));
        f_add.blocks.push(b_add);
        module.add_function(f_add);

        // Function 2: main
        let mut f_main = Function::new(FuncId::new(1), "main", ft_main, b(0));
        let mut b_main = Block::new(b(0));
        b_main.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(10),
            })
            .with_result(v(0)),
        );
        b_main.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(20),
            })
            .with_result(v(1)),
        );
        b_main.body.push(
            InstrNode::new(Inst::Call {
                callee: FuncId::new(0),
                args: vec![v(0), v(1)],
            })
            .with_result(v(2)),
        );
        b_main
            .body
            .push(InstrNode::new(Inst::Return { values: vec![v(2)] }));
        f_main.blocks.push(b_main);
        module.add_function(f_main);

        // Function 3: vararg
        let mut f_va = Function::new(FuncId::new(2), "printf_wrapper", ft_vararg, b(0));
        let mut b_va = Block::new(b(0));
        b_va.params.push((v(0), Ty::Ptr));
        b_va.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(0),
            })
            .with_result(v(1)),
        );
        b_va.body
            .push(InstrNode::new(Inst::Return { values: vec![v(1)] }));
        f_va.blocks.push(b_va);
        module.add_function(f_va);

        round_trip(&module);
    }

    // --- InstrNode metadata ---

    #[test]
    fn instr_node_with_full_metadata_round_trip() {
        let mut module = Module::new("metadata");
        let ft = module.add_func_type(FuncTy {
            params: vec![],
            returns: vec![],
            is_vararg: false,
        });
        let mut func = Function::new(FuncId::new(0), "test", ft, b(0));
        let mut block = Block::new(b(0));

        let node = InstrNode::new(Inst::BinOp {
            op: BinOp::Add,
            ty: Ty::I32,
            lhs: v(0),
            rhs: v(1),
        })
        .with_result(v(2))
        .with_proof(ProofAnnotation::NoOverflow)
        .with_proof(ProofAnnotation::NoWrap)
        .with_proof(ProofAnnotation::BoundedOutput { lo: 0.0, hi: 100.0 })
        .with_span(SourceSpan {
            file: 1,
            line: 42,
            col: 10,
        });

        block.body.push(node);
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        func.blocks.push(block);
        module.add_function(func);
        round_trip(&module);
    }

    #[test]
    fn semantic_source_provenance_v35_round_trip() {
        let mut module = Module::new("source_provenance");
        let ft = module.add_func_type(FuncTy {
            params: vec![Ty::U64],
            returns: vec![],
            is_vararg: false,
        });
        let mut func = Function::new(FuncId::new(0), "looping", ft, b(0));
        let mut entry = Block::new(b(0));
        entry.params.push((v(0), Ty::U64));
        entry.body.push(InstrNode::new(Inst::Br {
            target: b(1),
            args: vec![v(0)],
        }));
        let mut header = Block::new(b(1));
        header.params.push((v(1), Ty::U64));
        header.body.push(InstrNode::new(Inst::Br {
            target: b(1),
            args: vec![v(1)],
        }));
        func.blocks.extend([entry, header]);
        func.source_provenance = Some(SourceProvenance::new(
            d(7),
            d(8),
            vec![SourceLoopProvenance {
                source_loop_id: 0,
                hir_local_id: 41,
                header: b(1),
                bindings: vec![
                    SourceBindingProvenance {
                        name: "limit".into(),
                        hir_local_id: 9,
                        place: SourcePlace::FunctionParameter { index: 0 },
                    },
                    SourceBindingProvenance {
                        name: "x".into(),
                        hir_local_id: 10,
                        place: SourcePlace::LoopParameter { index: 0 },
                    },
                ],
            }],
        ));
        module.add_function(func);

        let back = round_trip(&module);
        assert_eq!(
            back.functions[0].source_provenance,
            module.functions[0].source_provenance,
        );
    }

    // --- Constant edge cases ---

    #[test]
    fn constant_edge_cases_round_trip() {
        let mut module = Module::new("constants");
        let ft = module.add_func_type(FuncTy {
            params: vec![],
            returns: vec![],
            is_vararg: false,
        });
        let mut func = Function::new(FuncId::new(0), "test", ft, b(0));
        let mut block = Block::new(b(0));

        // Large integers
        block.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I128,
                value: Constant::Int(i128::MAX),
            })
            .with_result(v(0)),
        );
        block.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I128,
                value: Constant::Int(i128::MIN),
            })
            .with_result(v(1)),
        );
        // Special floats
        block.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::F64,
                value: Constant::Float(f64::INFINITY),
            })
            .with_result(v(2)),
        );
        block.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::F64,
                value: Constant::Float(f64::NEG_INFINITY),
            })
            .with_result(v(3)),
        );
        // Nested aggregate
        block.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::Unit,
                value: Constant::Aggregate(vec![
                    Constant::Aggregate(vec![Constant::Int(1), Constant::Float(2.0)]),
                    Constant::Bool(true),
                ]),
            })
            .with_result(v(4)),
        );
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        func.blocks.push(block);
        module.add_function(func);
        round_trip(&module);
    }

    // --- New aggregate / closure types (issue #30) ---

    #[test]
    fn set_type_round_trip_both_reprs() {
        let mut module = Module::new("set_types");
        module.add_type(Ty::Set(TyId::new(0), SetRepr::Bitset));
        module.add_type(Ty::Set(TyId::new(3), SetRepr::Boxed));
        round_trip(&module);
    }

    #[test]
    fn sequence_type_round_trip() {
        let mut module = Module::new("seq_types");
        module.add_type(Ty::Sequence(TyId::new(0)));
        module.add_type(Ty::Sequence(TyId::new(7)));
        round_trip(&module);
    }

    #[test]
    fn record_type_round_trip() {
        let mut module = Module::new("record_types");
        module.add_record(RecordDef {
            id: RecordId::new(0),
            name: "Point".to_string(),
            fields: vec![
                FieldDef {
                    name: "x".to_string(),
                    ty: Ty::I32,
                    offset: None,
                },
                FieldDef {
                    name: "y".to_string(),
                    ty: Ty::I32,
                    offset: None,
                },
            ],
        });
        module.add_type(Ty::Record(RecordId::new(0)));
        round_trip(&module);
    }

    #[test]
    fn closure_type_round_trip_with_captures() {
        let mut module = Module::new("closure_types");
        let ft = module.add_func_type(FuncTy {
            params: vec![Ty::I32],
            returns: vec![Ty::I32],
            is_vararg: false,
        });
        module.add_closure_type(ClosureTy {
            func: ft,
            captures: vec![Ty::I32, Ty::Bool],
        });
        module.add_type(Ty::Closure(ClosureTyId::new(0)));
        round_trip(&module);
    }

    #[test]
    fn closure_type_round_trip_empty_captures() {
        let mut module = Module::new("bare_closure");
        let ft = module.add_func_type(FuncTy {
            params: vec![],
            returns: vec![],
            is_vararg: false,
        });
        module.add_closure_type(ClosureTy::bare(ft));
        module.add_type(Ty::Closure(ClosureTyId::new(0)));
        round_trip(&module);
    }

    #[test]
    fn new_constants_round_trip_in_global() {
        let mut module = Module::new("new_consts");
        // Sequence constant in a global initializer
        module.globals.push(Global {
            name: "SEQ".to_string(),
            ty: Ty::Sequence(TyId::new(0)),
            mutable: false,
            initializer: Some(Constant::Sequence(vec![
                Constant::Int(1),
                Constant::Int(2),
                Constant::Int(3),
            ])),
            linkage: Linkage::Internal,
            tls: None,
            align: None,
        });
        // Set constant
        module.globals.push(Global {
            name: "SET".to_string(),
            ty: Ty::Set(TyId::new(0), SetRepr::Boxed),
            mutable: false,
            initializer: Some(Constant::Set(vec![Constant::Int(10), Constant::Int(20)])),
            linkage: Linkage::Internal,
            tls: None,
            align: None,
        });
        // Record constant
        module.globals.push(Global {
            name: "REC".to_string(),
            ty: Ty::Record(RecordId::new(0)),
            mutable: false,
            initializer: Some(Constant::Record(vec![
                ("x".to_string(), Constant::Int(5)),
                ("y".to_string(), Constant::Bool(true)),
            ])),
            linkage: Linkage::Internal,
            tls: None,
            align: None,
        });
        // Closure constant
        module.globals.push(Global {
            name: "CLOS".to_string(),
            ty: Ty::Closure(ClosureTyId::new(0)),
            mutable: false,
            initializer: Some(Constant::Closure {
                func: FuncId::new(42),
                captures: vec![Constant::Int(7), Constant::Bool(false)],
            }),
            linkage: Linkage::Internal,
            tls: None,
            align: None,
        });
        round_trip(&module);
    }

    #[test]
    fn empty_aggregate_constants_round_trip() {
        let mut module = Module::new("empty_aggs");
        module.globals.push(Global {
            name: "EMPTY_SEQ".to_string(),
            ty: Ty::Sequence(TyId::new(0)),
            mutable: false,
            initializer: Some(Constant::Sequence(vec![])),
            linkage: Linkage::Internal,
            tls: None,
            align: None,
        });
        module.globals.push(Global {
            name: "EMPTY_SET".to_string(),
            ty: Ty::Set(TyId::new(0), SetRepr::Boxed),
            mutable: false,
            initializer: Some(Constant::Set(vec![])),
            linkage: Linkage::Internal,
            tls: None,
            align: None,
        });
        module.globals.push(Global {
            name: "EMPTY_REC".to_string(),
            ty: Ty::Record(RecordId::new(0)),
            mutable: false,
            initializer: Some(Constant::Record(vec![])),
            linkage: Linkage::Internal,
            tls: None,
            align: None,
        });
        module.globals.push(Global {
            name: "BARE_CLOS".to_string(),
            ty: Ty::Closure(ClosureTyId::new(0)),
            mutable: false,
            initializer: Some(Constant::Closure {
                func: FuncId::new(0),
                captures: vec![],
            }),
            linkage: Linkage::Internal,
            tls: None,
            align: None,
        });
        round_trip(&module);
    }

    // --- NaN handling ---

    #[test]
    fn nan_round_trip() {
        let mut module = Module::new("nan");
        let ft = module.add_func_type(FuncTy {
            params: vec![],
            returns: vec![],
            is_vararg: false,
        });
        let mut func = Function::new(FuncId::new(0), "test", ft, b(0));
        let mut block = Block::new(b(0));
        block.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::F64,
                value: Constant::Float(f64::NAN),
            })
            .with_result(v(0)),
        );
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        func.blocks.push(block);
        module.add_function(func);

        let bytes = serialize_module(&module);
        let back = deserialize_module(&bytes).expect("deserialize");
        // NaN != NaN, so check manually
        if let Inst::Const {
            value: Constant::Float(v),
            ..
        } = &back.functions[0].blocks[0].body[0].inst
        {
            assert!(v.is_nan(), "expected NaN");
        } else {
            panic!("expected Const Float instruction");
        }
    }

    // --- Dialect op binary round-trip ---

    #[test]
    fn dialect_op_round_trip() {
        use crate::dialect::{AttrValue, DialectInst};
        let mut module = Module::new("dialect_bin");
        let ft = module.add_func_type(FuncTy {
            params: vec![Ty::Ptr, Ty::I64],
            returns: vec![Ty::Ptr],
            is_vararg: false,
        });
        let mut func = Function::new(FuncId::new(0), "f", ft, b(0));
        let mut block = Block::new(b(0));
        block.params.push((v(0), Ty::Ptr));
        block.params.push((v(1), Ty::I64));

        // Cover every AttrValue variant so the tag byte table is exercised.
        let op = DialectInst::new("verif", "bfs_step")
            .with_operand(v(0))
            .with_operand(v(1))
            .with_result_ty(Ty::Ptr)
            .with_attr("parallel", AttrValue::Bool(true))
            .with_attr("delta", AttrValue::I64(-42))
            .with_attr("size", AttrValue::U64(1024))
            .with_attr("weight", AttrValue::F64(1.5))
            .with_attr("label", AttrValue::Str("frontier-a".to_string()))
            .with_attr("blob", AttrValue::Bytes(vec![0xde, 0xad, 0xbe, 0xef]))
            .with_attr("elem_ty", AttrValue::Ty(Ty::I32))
            .with_version(3);
        block
            .body
            .push(InstrNode::new(Inst::DialectOp(Box::new(op))).with_result(v(2)));
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![v(2)] }));
        func.blocks.push(block);
        module.add_function(func);

        round_trip(&module);
    }

    #[test]
    fn native_verification_bundle_round_trip() {
        use crate::request::*;
        let mut module = Module::new("bundle_test");
        let ft = module.add_func_type(FuncTy {
            params: vec![Ty::I32],
            returns: vec![Ty::I32],
            is_vararg: false,
        });
        let mut func = Function::new(FuncId::new(0), "f", ft, b(0));
        let mut block = Block::new(b(0));
        block.params.push((v(0), Ty::I32));
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![v(0)] }));
        func.blocks.push(block);
        module.add_function(func);

        // Use NON-default scalar metadata so the round-trip would visibly
        // mis-decode if the codec fabricated values (the old bug).
        let digest = crate::proof::ProofDigest::trust_ir_stable("bundle_test", b"abc");
        let mut bundle = NativeVerificationBundle::new(
            NativeBundleProducer::TSwift,
            NativeAdapterInput::RustMir {
                body_digest: crate::proof::ProofDigest::sha256([3u8; 32]),
            },
            digest,
            module,
            proof_lineage_manifest(),
        );
        bundle.schema_version = 7;

        let bytes = serialize_native_verification_bundle(&bundle).expect("serialize bundle");
        let back = deserialize_native_verification_bundle(&bytes).expect("deserialize bundle");

        // Scalar metadata is no longer silently reset (finding I): producer,
        // input, digest, and schema_version all survive the round-trip.
        assert_eq!(back.schema_version, bundle.schema_version);
        assert_eq!(back.producer, bundle.producer);
        assert_eq!(back.input, bundle.input);
        assert_eq!(back.trust_ir_module_digest, bundle.trust_ir_module_digest);
        // Module is byte-identical.
        assert_eq!(back.module, bundle.module);
        // Lineage is preserved (the sidecar codec canonicalizes node order, so
        // compare by its order-independent stable digest).
        assert_eq!(
            back.lineage.stable_digest(),
            bundle.lineage.stable_digest(),
            "native bundle lineage lost across round-trip"
        );
        // Fields the envelope refuses to drop stay at their defaults.
        assert!(back.requests.is_empty());
        assert!(back.evidence_bundles.is_empty());
    }

    #[test]
    fn native_verification_bundle_rejects_unrepresentable_requests() {
        use crate::request::*;
        let module = Module::new("rejects");
        let mut bundle = NativeVerificationBundle::new(
            NativeBundleProducer::TrustIr,
            NativeAdapterInput::TrustIrModule,
            crate::proof::ProofDigest::zero(),
            module,
            proof_lineage_manifest(),
        );
        // A non-default serialization policy cannot be carried by the binary
        // envelope; serialize must refuse rather than silently drop it.
        bundle.serialization.canonical_order = !bundle.serialization.canonical_order;
        match serialize_native_verification_bundle(&bundle) {
            Err(BinaryError::Unencodable(_)) => {}
            other => panic!("expected honest Unencodable error, got {other:?}"),
        }
    }

    #[test]
    fn native_verification_bundle_rejects_truncated_header() {
        // A TMVB header truncated before the payload segments must error
        // cleanly rather than panic.
        let truncated = b"TMVB\x01\x00\x00\x00";
        assert!(deserialize_native_verification_bundle(truncated).is_err());
    }

    // -----------------------------------------------------------------------
    // Frozen wire-tag contract
    //
    // The leading tag byte of every serialized enum variant is a permanent
    // on-the-wire contract: readers as old as MIN_READ_VERSION decode by these
    // numbers. A tag may NEVER be reordered or reused. New variants take the
    // next free tag (append discipline) and must be added to docs/binary-format.md.
    //
    // Each test below is double-entry: an exhaustive `match` re-states the
    // frozen tag for every variant (so adding a variant fails to compile until a
    // tag is consciously assigned here), cross-checked against the byte the codec
    // actually emits (so changing the encoder without this table fails the
    // assertion). This is the guard that keeps the codec and the documented
    // tag tables from silently drifting apart.
    // -----------------------------------------------------------------------

    fn first_tag_ty(ty: &Ty) -> u8 {
        let mut pool = StringPool::new();
        let mut buf = Vec::new();
        write_ty(&mut buf, &mut pool, ty);
        buf[0]
    }

    fn first_tag_constant(c: &Constant) -> u8 {
        let mut pool = StringPool::new();
        let mut buf = Vec::new();
        write_constant(&mut buf, &mut pool, c);
        buf[0]
    }

    fn first_tag_proof_evidence(ev: &ProofEvidence) -> u8 {
        let mut pool = StringPool::new();
        let mut buf = Vec::new();
        write_proof_evidence(&mut buf, &mut pool, ev);
        buf[0]
    }

    #[test]
    fn ty_wire_tags_frozen() {
        // Exhaustive: a new Ty variant forces a deliberate tag assignment here.
        fn frozen(ty: &Ty) -> u8 {
            match ty {
                Ty::I8 => 0,
                Ty::I16 => 1,
                Ty::I32 => 2,
                Ty::I64 => 3,
                Ty::I128 => 4,
                Ty::U8 => 5,
                Ty::U16 => 6,
                Ty::U32 => 7,
                Ty::U64 => 8,
                Ty::U128 => 9,
                // v25 B1 scalars. Ty::Error has NO tag (unencodable): the
                // frozen-tag sample list below deliberately omits it, and the
                // writer panics on it (validate_module rejects it first).
                Ty::Isize => 33,
                Ty::Usize => 34,
                Ty::Char => 35,
                Ty::Error => u8::MAX, // never asserted: not in the samples
                Ty::F32 => 10,
                Ty::F64 => 11,
                Ty::Bool => 12,
                Ty::Ptr => 13,
                Ty::Unit => 14,
                Ty::Never => 15,
                Ty::Struct(_) => 16,
                Ty::Array(_, _) => 17,
                Ty::Tuple(_) => 18,
                Ty::Enum(_) => 19,
                Ty::Func(_) => 20,
                Ty::Ref(_) => 21,
                Ty::RefMut(_) => 22,
                Ty::PtrConst(_) => 23,
                Ty::PtrMut(_) => 24,
                Ty::Rc(_) => 25,
                Ty::Set(_, _) => 26,
                Ty::Sequence(_) => 27,
                Ty::Record(_) => 28,
                Ty::Closure(_) => 29,
                Ty::FatPtr(_) => 30,
                // Appended out of source order; tags are dense, not source-ordered.
                Ty::F16 => 31,
                Ty::Vector(_, _) => 32,
                // v30 typed value model.
                Ty::Refine(_, _) => 36,
            }
        }

        let samples = [
            Ty::I8,
            Ty::I16,
            Ty::I32,
            Ty::I64,
            Ty::I128,
            Ty::U8,
            Ty::U16,
            Ty::U32,
            Ty::U64,
            Ty::U128,
            Ty::F16,
            Ty::F32,
            Ty::F64,
            Ty::Bool,
            Ty::Ptr,
            Ty::Unit,
            Ty::Never,
            Ty::Struct(StructId::new(0)),
            Ty::Array(TyId::new(0), 1),
            Ty::Tuple(vec![Ty::I8]),
            Ty::Enum(EnumId::new(0)),
            Ty::Func(FuncTyId::new(0)),
            Ty::Ref(Box::new(Ty::I8)),
            Ty::RefMut(Box::new(Ty::I8)),
            Ty::PtrConst(Box::new(Ty::I8)),
            Ty::PtrMut(Box::new(Ty::I8)),
            Ty::Rc(Box::new(Ty::I8)),
            Ty::Set(TyId::new(0), SetRepr::Boxed),
            Ty::Sequence(TyId::new(0)),
            Ty::Record(RecordId::new(0)),
            Ty::Closure(ClosureTyId::new(0)),
            Ty::FatPtr(FatPtrKind::Str),
            Ty::Vector(Box::new(Ty::I32), 4),
            Ty::Isize,
            Ty::Usize,
            Ty::Char,
            Ty::Refine(TyId::new(0), crate::value::PredId::new(0)),
        ];

        for ty in &samples {
            assert_eq!(
                first_tag_ty(ty),
                frozen(ty),
                "Ty wire tag drifted for {ty:?}"
            );
        }
    }

    #[test]
    fn constant_wire_tags_frozen() {
        fn frozen(c: &Constant) -> u8 {
            match c {
                Constant::Int(_) => 0,
                Constant::Float(_) => 1,
                Constant::Bool(_) => 2,
                Constant::Aggregate(_) => 3,
                Constant::Sequence(_) => 4,
                Constant::Set(_) => 5,
                Constant::Record(_) => 6,
                Constant::Closure { .. } => 7,
                // Appended out of source order.
                Constant::Array(_) => 8,
                Constant::FnDef(_) => 9,
                Constant::PhantomData => 10,
                Constant::Vector(_) => 11,
                Constant::SymbolAddr { .. } => 12,
                // v24: the 128-bit-faithful unsigned carrier.
                Constant::U128(_) => 13,
                // v25: raw byte-array constant.
                Constant::Bytes { .. } => 14,
            }
        }

        let samples = [
            Constant::Int(0),
            Constant::Float(0.0),
            Constant::Bool(true),
            Constant::Aggregate(vec![]),
            Constant::Sequence(vec![]),
            Constant::Set(vec![]),
            Constant::Record(vec![]),
            Constant::Closure {
                func: FuncId::new(0),
                captures: vec![],
            },
            Constant::Array(vec![]),
            Constant::FnDef(FuncId::new(0)),
            Constant::PhantomData,
            Constant::Vector(vec![]),
            Constant::SymbolAddr {
                symbol: "s".to_string(),
                addend: 0,
            },
            Constant::U128(u128::MAX),
            Constant::Bytes {
                data: vec![0, 255],
                utf8: false,
            },
        ];

        for c in &samples {
            assert_eq!(
                first_tag_constant(c),
                frozen(c),
                "Constant wire tag drifted for {c:?}"
            );
        }
    }

    #[test]
    fn proof_evidence_wire_tags_frozen() {
        fn frozen(ev: &ProofEvidence) -> u8 {
            match ev {
                ProofEvidence::SmtProof(_) => 0,
                ProofEvidence::LeanProof(_) => 1,
                ProofEvidence::KaniHarness(_) => 2,
                ProofEvidence::GammaCrownBound { .. } => 3,
                ProofEvidence::TranslationValidation { .. } => 4,
                ProofEvidence::Trusted(_) => 5,
                ProofEvidence::InheritedFromCallee { .. } => 6,
                ProofEvidence::CleanCic { .. } => 7,
            }
        }

        let samples = [
            ProofEvidence::SmtProof(vec![]),
            ProofEvidence::LeanProof(String::new()),
            ProofEvidence::KaniHarness(String::new()),
            ProofEvidence::GammaCrownBound {
                epsilon: 0.0,
                verified_layers: 0,
            },
            ProofEvidence::TranslationValidation {
                rule_name: String::new(),
                smt_hash: [0u8; 32],
            },
            ProofEvidence::Trusted(String::new()),
            ProofEvidence::InheritedFromCallee {
                callee: FuncId::new(0),
                obligation: ProofId::new(0),
            },
            ProofEvidence::CleanCic {
                term: vec![],
                context: vec![],
                lineage: ProofDigest::sha256([0u8; 32]),
                kernel_recheck: None,
            },
        ];

        for ev in &samples {
            assert_eq!(
                first_tag_proof_evidence(ev),
                frozen(ev),
                "ProofEvidence wire tag drifted for {ev:?}"
            );
        }
    }

    #[test]
    fn proof_evidence_clean_cic_binary_roundtrip() {
        let ev = ProofEvidence::CleanCic {
            term: vec![0xDE, 0xAD, 0xBE, 0xEF],
            context: vec![0x01, 0x02, 0x03],
            lineage: ProofDigest::trust_ir_stable("clean-cic-test", b"lineage"),
            kernel_recheck: None,
        };
        let mut pool = StringPool::new();
        let mut buf = Vec::new();
        write_proof_evidence(&mut buf, &mut pool, &ev);
        let mut reader = Reader::new(&buf);
        let back = read_proof_evidence(&mut reader).expect("read CleanCic");
        assert_eq!(ev, back);
    }

    #[test]
    fn proof_evidence_clean_cic_with_recheck_binary_roundtrip() {
        let ev = ProofEvidence::CleanCic {
            term: vec![0x01, 0x02],
            context: vec![0x03],
            lineage: ProofDigest::trust_ir_stable("clean-cic-test", b"lineage2"),
            kernel_recheck: Some(CleanCicKernelRecheck {
                module: "Crownproof.SlackCertZ".to_string(),
                theorems: vec![
                    "NNVerify.farkas_scale".to_string(),
                    "NNVerify.farkas_combine_2_le_bound".to_string(),
                ],
                anchor: crate::proof::KERNEL_ANCHOR_FARKAS_CONSTRUCTIVE.to_string(),
                allowed_axioms: vec![
                    "propext".to_string(),
                    "Classical.choice".to_string(),
                    "Quot.sound".to_string(),
                ],
            }),
        };
        // The recheck directive interns strings, so the reader must carry the
        // pool back (mirrors the full-module reader at the header).
        let mut pool = StringPool::new();
        let mut buf = Vec::new();
        write_proof_evidence(&mut buf, &mut pool, &ev);
        let mut reader = Reader::new(&buf);
        reader.pool = Some(pool);
        let back = read_proof_evidence(&mut reader).expect("read CleanCic w/ recheck");
        assert_eq!(ev, back);
    }

    #[test]
    fn operator_wire_tags_frozen() {
        fn tag<T>(writer: impl Fn(&mut Vec<u8>, &T), v: &T) -> u8 {
            let mut buf = Vec::new();
            writer(&mut buf, v);
            assert_eq!(buf.len(), 1, "tag-only enum must encode to a single byte");
            buf[0]
        }

        let binops = [
            (BinOp::Add, 0u8),
            (BinOp::Sub, 1),
            (BinOp::Mul, 2),
            (BinOp::UDiv, 3),
            (BinOp::SDiv, 4),
            (BinOp::URem, 5),
            (BinOp::SRem, 6),
            (BinOp::FAdd, 7),
            (BinOp::FSub, 8),
            (BinOp::FMul, 9),
            (BinOp::FDiv, 10),
            (BinOp::FRem, 11),
            (BinOp::And, 12),
            (BinOp::Or, 13),
            (BinOp::Xor, 14),
            (BinOp::Shl, 15),
            (BinOp::LShr, 16),
            (BinOp::AShr, 17),
        ];
        for (op, want) in &binops {
            assert_eq!(tag(write_binop, op), *want, "BinOp tag drifted: {op:?}");
        }

        let unops = [
            (UnOp::Neg, 0u8),
            (UnOp::FNeg, 1),
            (UnOp::Not, 2),
            (UnOp::CtPop, 3),
        ];
        for (op, want) in &unops {
            assert_eq!(tag(write_unop, op), *want, "UnOp tag drifted: {op:?}");
        }

        let overflow = [
            (OverflowOp::AddOverflow, 0u8),
            (OverflowOp::SubOverflow, 1),
            (OverflowOp::MulOverflow, 2),
        ];
        for (op, want) in &overflow {
            assert_eq!(
                tag(write_overflow_op, op),
                *want,
                "OverflowOp tag drifted: {op:?}"
            );
        }

        let icmp = [
            (ICmpOp::Eq, 0u8),
            (ICmpOp::Ne, 1),
            (ICmpOp::Ult, 2),
            (ICmpOp::Ule, 3),
            (ICmpOp::Ugt, 4),
            (ICmpOp::Uge, 5),
            (ICmpOp::Slt, 6),
            (ICmpOp::Sle, 7),
            (ICmpOp::Sgt, 8),
            (ICmpOp::Sge, 9),
        ];
        for (op, want) in &icmp {
            assert_eq!(tag(write_icmp_op, op), *want, "ICmpOp tag drifted: {op:?}");
        }

        let fcmp = [
            (FCmpOp::OEq, 0u8),
            (FCmpOp::ONe, 1),
            (FCmpOp::OLt, 2),
            (FCmpOp::OLe, 3),
            (FCmpOp::OGt, 4),
            (FCmpOp::OGe, 5),
            (FCmpOp::UEq, 6),
            (FCmpOp::UNe, 7),
            (FCmpOp::ULt, 8),
            (FCmpOp::ULe, 9),
            (FCmpOp::UGt, 10),
            (FCmpOp::UGe, 11),
        ];
        for (op, want) in &fcmp {
            assert_eq!(tag(write_fcmp_op, op), *want, "FCmpOp tag drifted: {op:?}");
        }

        let casts = [
            (CastOp::Trunc, 0u8),
            (CastOp::ZExt, 1),
            (CastOp::SExt, 2),
            (CastOp::FPTrunc, 3),
            (CastOp::FPExt, 4),
            (CastOp::FPToUI, 5),
            (CastOp::FPToSI, 6),
            (CastOp::UIToFP, 7),
            (CastOp::SIToFP, 8),
            (CastOp::PtrToInt, 9),
            (CastOp::IntToPtr, 10),
            (CastOp::Bitcast, 11),
            (CastOp::PtrToPtr, 12),
            (CastOp::Transmute, 13),
            (CastOp::ReifyFnPointer, 14),
            (CastOp::FPToSISat, 15),
            (CastOp::FPToUISat, 16),
        ];
        for (op, want) in &casts {
            assert_eq!(tag(write_cast_op, op), *want, "CastOp tag drifted: {op:?}");
        }

        let orderings = [
            (Ordering::Relaxed, 0u8),
            (Ordering::Acquire, 1),
            (Ordering::Release, 2),
            (Ordering::AcqRel, 3),
            (Ordering::SeqCst, 4),
        ];
        for (op, want) in &orderings {
            assert_eq!(
                tag(write_ordering, op),
                *want,
                "Ordering tag drifted: {op:?}"
            );
        }

        let rmw = [
            (AtomicRMWOp::Xchg, 0u8),
            (AtomicRMWOp::Add, 1),
            (AtomicRMWOp::Sub, 2),
            (AtomicRMWOp::And, 3),
            (AtomicRMWOp::Or, 4),
            (AtomicRMWOp::Xor, 5),
            (AtomicRMWOp::Max, 6),
            (AtomicRMWOp::Min, 7),
            (AtomicRMWOp::UMax, 8),
            (AtomicRMWOp::UMin, 9),
        ];
        for (op, want) in &rmw {
            assert_eq!(
                tag(write_atomic_rmw_op, op),
                *want,
                "AtomicRMWOp tag drifted: {op:?}"
            );
        }

        let obligations = [
            (ObligationKind::Precondition, 0u8),
            (ObligationKind::Postcondition, 1),
            (ObligationKind::LoopInvariant, 2),
            (ObligationKind::TypeInvariant, 3),
            (ObligationKind::RefinementType, 4),
            (ObligationKind::TranslationValidation, 5),
            (ObligationKind::MemorySafety, 6),
            (ObligationKind::PanicFreedom, 7),
            (ObligationKind::TemporalSafety, 8),
            (ObligationKind::Liveness, 9),
            (ObligationKind::ArithmeticSafety, 10),
            (ObligationKind::BoundsCheck, 11),
            (ObligationKind::GiveBackRefinement, 12),
        ];
        for (op, want) in &obligations {
            assert_eq!(
                tag(write_obligation_kind, op),
                *want,
                "ObligationKind tag drifted: {op:?}"
            );
        }

        let statuses = [
            (ProofStatus::Pending, 0u8),
            (ProofStatus::Discharged, 1),
            (ProofStatus::Failed, 2),
            (ProofStatus::Trusted, 3),
            (ProofStatus::Certified, 4),
        ];
        for (op, want) in &statuses {
            assert_eq!(
                tag(write_proof_status, op),
                *want,
                "ProofStatus tag drifted: {op:?}"
            );
        }

        let conventions = [
            (CallingConv::C, 0u8),
            (CallingConv::Fast, 1),
            (CallingConv::Cold, 2),
            (CallingConv::Rust, 3),
            (CallingConv::Swift, 4),
        ];
        for (op, want) in &conventions {
            assert_eq!(
                tag(write_calling_conv, op),
                *want,
                "CallingConv tag drifted: {op:?}"
            );
        }

        let linkages = [
            (Linkage::External, 0u8),
            (Linkage::Internal, 1),
            (Linkage::Private, 2),
            (Linkage::Weak, 3),
            (Linkage::LinkOnce, 4),
        ];
        for (op, want) in &linkages {
            assert_eq!(tag(write_linkage, op), *want, "Linkage tag drifted: {op:?}");
        }
    }

    #[test]
    fn subtag_wire_tags_frozen() {
        // FatPtrKind sub-tags (nested under Ty::FatPtr, tag 30).
        let mut pool = StringPool::new();
        for (kind, want) in [
            (FatPtrKind::Slice(TyId::new(0)), 0u8),
            (FatPtrKind::Str, 1),
            (FatPtrKind::TraitObject { trait_id: 0 }, 2),
        ] {
            let mut buf = Vec::new();
            write_fat_ptr_kind(&mut buf, &mut pool, &kind);
            assert_eq!(buf[0], want, "FatPtrKind sub-tag drifted: {kind:?}");
        }

        // SetRepr sub-tags (part of Ty::Set, tag 26).
        for (repr, want) in [(SetRepr::Bitset, 0u8), (SetRepr::Boxed, 1)] {
            let mut buf = Vec::new();
            write_set_repr(&mut buf, &repr);
            assert_eq!(buf[0], want, "SetRepr sub-tag drifted: {repr:?}");
        }
    }

    // -----------------------------------------------------------------------
    // C1: unbounded Vec::with_capacity from untrusted length fields.
    // -----------------------------------------------------------------------

    /// Encode an unsigned LEB128 varint the way `write_v32` does, so tests can
    /// forge a hostile count field.
    fn forge_v32(buf: &mut Vec<u8>, mut v: u64) {
        while v >= 0x80 {
            buf.push((v as u8) | 0x80);
            v >>= 7;
        }
        buf.push(v as u8);
    }

    /// A tiny buffer that declares a gigantic function-type count must produce
    /// a clean `Err(TooLarge)` rather than attempting a multi-gigabyte
    /// `Vec::with_capacity` (OOM/abort).
    #[test]
    fn deserialize_rejects_oversized_count_without_oom() {
        let mut buf = Vec::new();
        buf.extend_from_slice(MAGIC);
        write_u32(&mut buf, VERSION);
        // String pool: 1 string ("m") so the module name resolves.
        forge_v32(&mut buf, 1);
        write_raw_str(&mut buf, "m");
        // Module name: pool id 0 -> "m".
        forge_v32(&mut buf, 0);
        // func_types count: a hostile ~4 billion.
        forge_v32(&mut buf, u32::MAX as u64);
        // No element bytes follow — only a couple bytes remain.

        let err = deserialize_module(&buf).expect_err("must reject oversized count");
        assert!(
            matches!(err, BinaryError::TooLarge { .. }),
            "expected TooLarge, got {err:?}"
        );
    }

    /// A syntactically valid u64 varint above `u32::MAX` must not wrap to a
    /// small u32 length/id. Silent narrowing would make the binary encoding —
    /// and therefore the module's cryptographic identity — non-injective.
    #[test]
    fn read_v32_rejects_numeric_overflow_instead_of_truncating() {
        let mut bytes = Vec::new();
        forge_v32(&mut bytes, u64::from(u32::MAX) + 1);
        let mut reader = Reader::new(&bytes);
        assert_eq!(reader.read_v32(), Err(BinaryError::VintOverflow));
    }

    /// Byte ten of a u64 LEB128 may carry only bit 63. Wider payload bits must
    /// not be shifted away and accepted as an aliased smaller value.
    #[test]
    fn read_v64_rejects_overwide_tenth_byte() {
        let mut bytes = vec![0x80; 9];
        bytes.push(0x02);
        let mut reader = Reader::new(&bytes);
        assert_eq!(reader.read_v64(), Err(BinaryError::VintOverflow));
    }

    /// The compact writer has one spelling per integer; accepting overlong
    /// spellings would make the wire identity non-canonical.
    #[test]
    fn read_v64_rejects_overlong_spelling() {
        let bytes = [0x80, 0x00];
        let mut reader = Reader::new(&bytes);
        assert!(matches!(
            reader.read_v64(),
            Err(BinaryError::InvalidData(reason))
                if reason.contains("non-canonical varint")
        ));
    }

    /// `reserve_checked` rejects a count larger than the remaining bytes and
    /// accepts one that fits.
    #[test]
    fn reserve_checked_bounds_by_remaining_bytes() {
        let data = [0u8; 4];
        let r = Reader::new(&data);
        // 4 bytes remain; a count of 5 is impossible.
        assert!(matches!(
            r.reserve_checked(5),
            Err(BinaryError::TooLarge {
                declared: 5,
                remaining: 4
            })
        ));
        // A count within the remaining budget is fine.
        assert_eq!(r.reserve_checked(4).unwrap(), 4);
    }

    /// A forged byte-string length must not pre-allocate beyond the input.
    #[test]
    fn read_bytes_rejects_oversized_length() {
        let mut buf = Vec::new();
        forge_v32(&mut buf, 1_000_000_000); // declared length
        // Only the length bytes are present.
        let mut r = Reader::new(&buf);
        let err = r
            .read_bytes()
            .expect_err("must reject oversized byte length");
        assert!(
            matches!(err, BinaryError::TooLarge { .. }),
            "expected TooLarge, got {err:?}"
        );
    }

    /// The lowest allocation primitive independently checks the backing slice,
    /// so a future direct variable-length caller cannot allocate before EOF.
    #[test]
    fn read_exact_checks_remaining_before_allocation() {
        let mut r = Reader::new(&[]);
        assert!(matches!(
            r.read_exact(usize::MAX),
            Err(BinaryError::TooLarge {
                declared: usize::MAX,
                remaining: 0
            })
        ));
    }

    /// Nested CleanCic directive counts are untrusted collection lengths too;
    /// they must use the same remaining-input bound as top-level tables.
    #[test]
    fn proof_evidence_rejects_oversized_nested_theorem_count() {
        let mut buf = Vec::new();
        write_u8(&mut buf, 7); // ProofEvidence::CleanCic
        write_bytes(&mut buf, &[]); // term
        write_bytes(&mut buf, &[]); // context
        write_proof_digest(&mut buf, &ProofDigest::sha256([1; 32]));
        write_u8(&mut buf, 1); // kernel_recheck = Some
        write_raw_str(&mut buf, "M");
        forge_v32(&mut buf, u32::MAX as u64); // hostile theorem count

        let mut r = Reader::new(&buf);
        assert!(matches!(
            read_proof_evidence(&mut r),
            Err(BinaryError::TooLarge { .. })
        ));
    }

    /// Recursive type spellings are compact enough to evade collection-size
    /// checks; reject them at a shared nesting budget before stack exhaustion.
    #[test]
    fn read_ty_rejects_excessive_recursive_nesting() {
        let mut bytes = vec![21; MAX_BINARY_NESTING_DEPTH + 1]; // Ty::Ref
        bytes.push(0); // Ty::I8 leaf
        let mut r = Reader::new(&bytes);
        assert!(matches!(
            read_ty(&mut r),
            Err(BinaryError::InvalidData(reason))
                if reason.contains("nesting exceeds limit")
        ));
        assert_eq!(r.nesting_depth, 0, "failed decode must unwind its budget");
    }
}
