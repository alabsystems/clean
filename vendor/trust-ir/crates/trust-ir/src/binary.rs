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

use std::io::{self, Cursor, Read as IoRead, Write as IoWrite};

use sha2::{Digest, Sha256};

use crate::canonicalize::FunctionCanonicalPlan;
#[cfg(test)]
use crate::constant::Constant;
use crate::constant::ConstantG;
#[cfg(test)]
use crate::inst::Inst;
use crate::inst::{
    AllocOrigin, AssertKind, AssertOverflowOp, AtomicRMWOp, BinOp, CastOp, FCmpOp, ICmpOp, InstG,
    Ordering, OverflowOp, PanicLocation, PanicSite, SwitchCase, UnOp,
};
use crate::level::{NoExt, TemplateRef};
#[cfg(test)]
use crate::node::InstrNode;
use crate::node::InstrNodeG;
use crate::proof::{
    CleanCicKernelRecheck, Divergence, ObligationKind, ProofAnnotation, ProofCertificate,
    ProofCertificateRef, ProofContext, ProofDigest, ProofDigestAlgorithm, ProofEvidence,
    ProofFormula, ProofLineageId, ProofLineageManifest, ProofLineageNode, ProofObligation,
    ProofObligationSourceIdentity, ProofObligationSourceRange, ProofReplayIdentity, ProofStatus,
    ProofTransform, ProofTransformStage, PublicObligationIdentity,
};
#[cfg(test)]
use crate::ty::FuncTy;
use crate::ty::{
    ClosureTy, EnumDef, EnumDefG, EnumLayoutDescriptor, EnumTagEncoding, EnumTagRepr, EnumVariant,
    EnumVariantG, FatPtrKind, FieldDef, FieldDefG, FuncTyG, RecordDef, SetRepr, StructDef,
    StructDefG, StructRepr, Ty, TyG, TypeOrigin,
};
use crate::value::{
    BlockId, ClosureTyId, EnumId, FuncId, FuncTyId, GlobalId, ProofId, ProofTag, RecordId,
    ScopeData, SourceSpan, StructId, TyId, ValueId,
};
use crate::{
    ArgExt, BlockG, CallingConv, Endianness, FuncAttrs, FunctionG, FunctionSummary, GlobalG,
    Linkage, Module, ModuleG, ParamAttrs, PassMode, Producer, SourceBindingProvenance,
    SourceLoopProvenance, SourcePlace, SourceProvenance, StructPassingPolicy, TargetInfo, TlsModel,
};
#[cfg(test)]
use crate::{Block, Function, Global};

use std::collections::{HashMap, HashSet};

mod observed;
mod pool;
pub use observed::retire_wire_image_refusals_observed;
pub(crate) use observed::{
    observed_checked_module_identity, observed_module_identity, observed_source_function_identity,
    observed_wire_image_refusals,
};

use pool::{SealedStringPool, StringPoolBuilder};

// The single spelling lives in `codec`, so `sniff_format` and this codec
// cannot disagree about what a TrustIr binary module starts with.
const MAGIC: &[u8; 8] = &crate::codec::TRUST_IR_BINARY_MAGIC;
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
// (Superseded 2026-09-21 by WS4.5's enum half: the text grammar now carries
// the descriptor too, as `layout(<encoding> size=N align=N offsets=[[..], ..])`,
// and refuses one that contradicts its own enum. The variant `field_names`
// remain text-lossy, so binary and serde are still the only transports for
// THOSE. This wire format is UNCHANGED either way.)
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
// v38 (container-tail fat pointers, ADDITIVE): `FatPtrKind::ContainerLen` at
//   fat-pointer-kind tag 3, read-gated on `version >= 38`. It spells a pointer
//   whose pointee CONTAINS a DST in tail position rather than being one — the
//   `*const ArcInner<str>` inside `Arc<str>`. rustc lays it out fat with
//   `usize` metadata, identically to `Str`, and the kinds are distinct only in
//   what the DATA pointer addresses: `Str` points at string CONTENT, this
//   points at the CONTAINER header whose tail is the DST. That is why the
//   producer could not reuse `Str` — it would encode a falsehood — and signed
//   an anonymous `(ptr, i64)` tuple instead, recording this variant as the
//   follow-up.
//
//   The tuple had no layout rule (`ty_layout_shape` covers the EMPTY tuple
//   only), so every type transitively containing a fat pointer had an
//   unresolvable layout and the v31 enum-layout validator failed closed on it.
//   Measured 2026-08-27 on the locked producer census: `enum E { A, B(Arc<str>) }`
//   alone produced two `ConstTypeMismatch` rows, and the same shape made
//   `modules_invalid` non-zero for the first time in the series.
//
//   The stable DIGEST tag is 3 as well, deliberately not `Str`'s 1: the digest
//   is a content-derived identity and two different meanings must never hash
//   equal.
// v39 adds nominal dialect types at type tag 37, with exact namespace/name/
// version identity and no machine representation. Modules without such types
// retain byte-identical v38 encoding, including their header and string pool.
// v40 (container-tail fat pointers, dyn half, ADDITIVE):
//   `FatPtrKind::ContainerVtable` at fat-pointer-kind tag 4, read-gated on
//   `version >= 40`. The `dyn`-tail sibling of v38's `ContainerLen`: a pointer
//   whose pointee CONTAINS a `dyn Trait` in tail position rather than being
//   one — the `*const ArcInner<dyn Any>` inside `Arc<dyn Any>`. rustc lays it
//   out fat with a VTABLE-pointer metadata word, identically to `TraitObject`,
//   and the kinds are distinct only in what the DATA pointer addresses:
//   `TraitObject` points at the dispatched OBJECT, this points at the
//   CONTAINER header whose tail is the `dyn`. Its metadata is an opaque vtable
//   word and NEVER a length, so it is classified with `TraitObject` and never
//   with `Slice`/`Str`/`ContainerLen`. It carries no trait id: nothing
//   dispatches through it, and an id would assert an identity it lacks.
//
//   Before it the producer had no honest spelling and failed closed to
//   `Ty::Unit` (`container_pointee_ty`, `PointeeMeta::Vtable => None`), which
//   left `NonNull<ArcInner<dyn Any>>` without a coherent size. Measured
//   2026-09-08 on seal trust-f2887e0d (nn-autodiff): a struct holding an
//   `Arc<dyn Any + Send + Sync>` made every enum containing it fail final
//   module validation with `ConstTypeMismatch { .. layout UNRESOLVABLE ..
//   has no size layout metadata }`.
//
//   The stable DIGEST tag is 4 as well, deliberately not `TraitObject`'s 2,
//   for the v38 reason: two different meanings must never hash equal.
//
//   Writer selection follows the v39 rule: the string-collection walk calls
//   `raise_to(40)` when a `ContainerVtable` occurs, so a legacy
//   module still writes v38, a dialect-only module v39, and any module with a
//   `ContainerVtable` v40 (the max of the two when both occur). The explicit
//   `RawV38` / `CanonicalV38` projections refuse any module whose minimum
//   version exceeds 38: `BinaryProjectionError::DialectTypeRequiresV39` for a
//   dialect-only module, `::ContainerVtableRequiresV40` for any v40 module.
//   Historical seal-line blobs that carried sub-tag 4 under a v39 header were
//   never released and are NOT readable: v39 means nominal dialect types only.
// v41 (the two-language contract surface, ADDITIVE). One writer-selected
// version covering four groups; the string-collection walk calls
// `raise_to(41)` whenever a module USES any of them, so a module
// that uses none still writes exactly the v38/v39/v40 bytes it wrote before.
// Every v41 read is gated `version >= 41`.
//
//   * CODEGEN LICENSE — `Function.body_gate: Option<BodyGate>`, a three-valued
//     tag (0 `None` = no licensing claim, 1 `Ungated` = codegen MUST refuse,
//     2 `Gated` + pooled authority) and `Function.display_path`. At v41 the tag
//     is written for EVERY function, so `None` stays spellable and a decoded
//     module never gains an affirmative claim it did not state. A v41-or-later
//     producer must emit 1 or 2 for every bodied function; a bodied 0 at v41+
//     is refused on the decoded path (`validate_module_as_decoded`), and a
//     faithful re-emission of pre-v41 content never gets there, because the
//     writer selects the minimum lossless version.
//     Not identity-bearing for `executable_content_digest_v1`: that projection
//     writes tag 0 and an absent path, so licensing a verified image never
//     moves the identity the license names.
//   * TYPED CONTRACT CLAUSES — `ProofFormula.bindings` (name -> `ClauseSort` +
//     `ClausePlace`; empty reads as UNBINDABLE, never a wildcard),
//     `FunctionSummary.decreases`, `FunctionSummary.backed_by`,
//     `ObligationKind::{Termination 13, Ownership 14, Custom 15 + two pooled
//     strings}`, `ProofCertificate.assurance` (a `CoverageBound` projected from
//     its evidence bundle, with the bundle's request digest).
//   * CROSS-CRATE IDENTITY — `Module.imports` (trailing section after
//     `global_asm`), `ExternRef`, and `ProofEvidence::InheritedFromCallee` with
//     `external: Some(..)` at NEW evidence tag 8. Tag 6 keeps its exact
//     two-varint payload, so an older reader REFUSES a cross-crate inheritance
//     with `InvalidTag(8)` rather than misreading it as local.
//   * ABI / LINKAGE — `Linkage::{AvailableExternally 5, ExternalWeak 6,
//     WeakOdr 7, LinkOnceOdr 8}`, `Global.{section, visibility, retained}`,
//     `FuncAttrs.naked` (flags bit 4) and `FuncAttrs.target_features`, and
//     `Module.global_asm`.
//
// LINEAGE NOTE. This batch was developed as "v39" on a line that diverged from
// the one that shipped v39 (nominal dialect types) and v40 (`ContainerVtable`).
// It was never pushed, so no blob in the wild carries that numbering; it lands
// here as v41 on top of both. Its own copy of `ContainerVtable` was dropped in
// favour of the shipped v40 one.
// v42 adds concrete tuple descriptors after the v41 imports section. A
// nonempty tuple table selects v42; all earlier payloads retain their order.
// Private tuple-only v41 blobs were never published and are not accepted as
// the public v41 contract-surface format.
// v43 (nominal opaque runtime handles, ADDITIVE). `Ty::Handle(HandleTy{name,runtime})`
// at type tag 38 (0x26): pooled name, pooled runtime path; read-gated `version >= 43`.
// One pointer word (layout = Ptr), NOT pointer-like, NEVER equal to Ptr: trust-ir-build
// pins (name, runtime) to `TRUSTED_HANDLE_RUNTIMES`, admits only pinned bodyless
// External C declarations as origins, permits exact-typed transport only. Writer selects
// 43 only when a handle occurs; RawV38/CanonicalV38 refuse (`HandleTypeRequiresV43`).
// A handle lives in the TYPE table, which every version already writes ahead of
// the v41 imports section and the v42 tuple table, so nothing is reordered: a
// module carrying both a tuple table and a handle writes the same section order
// under a v43 header (highest requirement wins).
//
//   LINEAGE NOTE. This batch was developed as "v42" while origin shipped its
//   own v42 (declared tuple layouts, above) — the second version collision of
//   this program, after the v39 one. The tuple layouts were pushed and have
//   conformance goldens, so they keep 42; the handle type was unpushed and
//   lands here as v43. No blob in the wild carries a handle under a v42 header.
//
//   Why a type and not a `Ty::Dialect` row or a bare `Ptr`: a `Ptr` can be
//   forged by `IntToPtr`, `Bitcast`, `Load`, a constant, or a field read, so a
//   runtime handle spelled `Ptr` has no origin guarantee at all; a `Dialect`
//   type has no machine representation, so a backend cannot pass one to a C
//   entry point. A handle is the third thing: representation-bearing (one
//   word) and origin-pinned (only the validator's pinned declarations may
//   produce or consume one). The stable DIGEST tag is 38 as well, and
//   `TyShape::Handle` digests as shape tag 26; both enter a digest only for a
//   module that carries a handle, so no existing identity moves.
//
//   The reader validates the pair lexically (`HandleTy::validate`,
//   `InvalidData`) exactly as it does a dialect identity; whether the pair
//   names a TRUSTED runtime is the validator's decision, never the codec's.
//
// v44 (portable import identity, ADDITIVE; roadmap WS4.10, F-084 + the F-117
// format half; reserved 6caf775d). `ModuleImport.scheme: IdentityScheme` — one
// tag byte (0 V2, 1 V3) appended to every import row, read-gated
// `version >= 44`; a row decoded from v41..=v43 is V2. Writer selects 44 only
// when some row is not V2, so a module whose rows are all V2 keeps its v41..=v43
// bytes exactly; RawV38/CanonicalV38 refuse (`ImportSchemeRequiresV44`). The
// row lives in the v41 imports section, which precedes the v42 tuple table, so
// nothing is reordered. The scheme names the digest construction the row's
// digest was taken under: V2 = `trust_ir.module.v2` over the whole encoding;
// V3 = `trust_ir.module.v3` over the encoding with every `Module.files` string
// projected to "" (length kept) — the portable identity `Module::stable_digest`
// now computes. The verifier hashes the candidate under the ROW's scheme, so
// no pre-v44 row changes meaning.
//
// v45 (the ABI surface, ADDITIVE; roadmap WS3.10 + WS3.11 + WS3.12 + WS3.14(b),
// the WS8.5 "ABI" reservation group; reserved 79783f80). Everything below is
// read-gated `version >= 45`, and the writer selects 45 only when a module
// uses one of them, so a module using none keeps its v38..=v44 bytes exactly;
// RawV38/CanonicalV38 refuse (`AbiSurfaceRequiresV45`).
//   * WS3.10 (F-053): `Function.section` (presence byte + pooled string),
//     `Function.visibility` (the v41 `Visibility` tag) and `Function.retained`
//     (bool), appended after the v41 `display_path`, mirroring `Global`.
//   * WS3.12 (F-059): `CallingConv` tags 5..=11 (`CUnwind`, `SysV64`, `Win64`,
//     `Aapcs`, `EfiApi`, `VectorCall`, `RustCold`) on a function or a
//     `CallIndirect`; a pre-v45 header carrying one is `InvalidTag`.
//   * WS3.14(b) (F-056): `EnumTagRepr::U128` (tag 9) and `::I128` (tag 10),
//     the 128-bit tag lanes. `U128` spells only `0..=i128::MAX` (a
//     discriminant is an `i128`); inference keeps the 64-bit cap, so only an
//     explicit repr hint selects one. The lane is 16 bytes SIZE, and its
//     ALIGNMENT comes from the target scalar table, never from the size.
//   * WS3.11 (F-054): per-slot ABI facts. `ParamAttrs.ext` rides flag bits 5
//     and 6 (`zeroext` / `signext`, mutually exclusive), `ParamAttrs.pass` is
//     a presence-tagged `PassMode` record after `align` (tags 0 unrecorded,
//     1 Ignore, 2 Direct, 3 Pair, 4 Cast + lane types, 5 Indirect + on_stack),
//     and `FuncAttrs.ret` is one more `ParamAttrs` record after the v41
//     target features. `read_param_attrs` now REFUSES an unallocated flag bit
//     at the blob's version instead of dropping it.
//
// NOT YET ON THE WIRE — `ScopeData.inlined_at` (WS4.19, F-082): the lexical
// scope inlining chain (call-site span + callee display path) exists in memory
// and in the text / JSON / MessagePack formats, but no binary version carries
// it. Its carrier joins the next open wire batch (a reservation first, per
// `docs/wire-allocation.md`); until then every binary writer REFUSES a module
// whose scope table carries a link (`InlinedScopeChainUnencodable`) instead of
// dropping it.
//
// NOT YET ON THE WIRE — `Module.completeness` (WS5.3b, F-090): the producer's
// three-valued completeness claim (none / complete / partial + unlowered rows)
// exists in memory and in the text / JSON / MessagePack formats, but no binary
// version carries it. Its carrier (a trailing section after the v42 tuple
// table, tag 0 none / 1 complete / 2 partial + rows, read-gated on its
// version) joins the next open wire batch after a reservation; until then
// every binary writer REFUSES a module carrying a claim
// (`CompletenessClaimUnencodable`) instead of dropping it, and a decoded
// module always reads `None` — never `Complete`.
//
// v44 AND LATER ARE RESERVED BEFORE THEY ARE WRITTEN (roadmap WS8.5, DG-14).
// `crates/trust-ir/wire_versions.tsv` is the reservation ledger: one row per
// version (retired / shipped / refused / reserved). A number is claimed by
// pushing a `reserved` row to trust-ir main BEFORE any read gate, writer
// selection or golden spells it — the two collisions above (v39, v42) were two
// lines writing the same unreserved number. Numbers go out one per feature
// group, in reservation order. The `wire_version_ledger` unit test at the end
// of this file (CI gate `wire-version-ledger`) binds the ledger to `VERSION`,
// `MIN_READ_VERSION`, every `*_FORMAT_VERSION` constant here (by source scan)
// and the reader's real accept/refuse behaviour.
//
// v46 (typed spec carrier, ADDITIVE; roadmap WS4.14, F-014 carrier half;
// reserved b9755a79 as v47, renumbered to v48 by 113a1c82 and taken to
// the lowest open number 46 by 6d3f5303). The `SpecModule`
// surface stops being opaque text:
//   * `SpecVar.sort: Option<ClauseSort>` — a presence byte plus a clause sort,
//     written inside the existing per-variable record;
//   * `SpecInvariant.typed: Option<ProofFormula>` — the SAME first-order
//     clause carrier contract clauses already use, written inside the
//     per-invariant record. No second grammar, no CIC core, no binder;
//   * `SpecModule.temporal: Vec<SpecTemporal>` — a trailing block after the
//     v27 enforcement byte, one `TemporalForm` tag (0 Always, 1 Eventually,
//     2 LeadsTo, 3 WeakFair, 4 StrongFair) plus its first-order leaves;
//   * `ProofKind::CleanTheorem { name }` at proof-kind tag 1, read-gated so a
//     v45-or-older header carrying tag 1 is refused with `InvalidTag(1)`;
//   * `ClausePlace::SpecVar { index }` / `SpecVarNext { index }` at clause
//     place tags 6 and 7 — the spec-variable index space. Both are REFUSED by
//     the function-summary and module-obligation validators, which have no
//     such index space;
//   * `ProofObligation.spec: Option<SpecObligationRef>` — the named temporal
//     property a `Liveness`/`TemporalSafety` obligation discharges, appended
//     after the v34 `site`.
// All six are read-gated `version >= 46`, and the writer selects 46 only when
// one of them is USED, so a module carrying none keeps its v38..=v45 bytes
// exactly. `RawV38`/`CanonicalV38` refuse (`SpecCarrierRequiresV46`).
// `obligation_content_digest` moves to `trust_ir.obligation.digest.v7`: the
// `spec` backref changes WHICH property an obligation states, exactly as v41's
// `bindings`/`decreases` changed what a contract MEANS.
// v47 (the crystal lane's destructor instruction, ADDITIVE; reserved by takeover
// c654a054 — see wire-allocations.toml). `Inst::Drop
// { ty, ptr }` at instruction tag 57: the dropped type, then the pointer
// operand. Read-gated `version >= 47`, so a v46-or-older header carrying tag 57
// is refused with `InvalidTag(57)` rather than silently promoted. The writer
// selects 47 only when a module contains a drop, so every other module keeps
// its v38..=v46 bytes exactly. `RawV38`/`CanonicalV38` refuse
// (`DropInstRequiresV47`). Both executable models REFUSE the instruction (no
// destructor model): the reference interpreter with a type error, the Lean
// model with `unsupported.destructor`.
//
//   LINEAGE NOTE. This instruction was developed as "v40" on the crystal lane's
//   fork of trust-ir (branch crystal/wave-ds-loose-tree), which diverged from
//   main at 01354303 before main shipped its own v40 (`ContainerVtable`). Blobs
//   carrying that numbering exist only inside the Trust crystal lane's build;
//   a v40-labelled blob from that fork is NOT readable here (tag 57 below v47
//   is refused), and it lands here as v47.
// v48 (the crystal lane's WEAK compare-exchange, ADDITIVE; reserved by takeover
// c654a054). `Inst::CmpXchg` gains a trailing `weak`
// flag. The strength is the TAG: a strong compare-exchange keeps tag 13 and
// its exact bytes in every format (text `cmpxchg`, serde skips `weak: false`),
// and a weak one is instruction tag 58 with tag 13's payload, read-gated
// `version >= 48`. The writer selects 48 only when a module contains a weak
// one; `RawV38`/`CanonicalV38` refuse (`WeakCmpXchgRequiresV48`). Both
// executable models REFUSE a weak compare-exchange (it may fail spuriously,
// a nondeterministic choice neither model makes): the interpreter with a type
// error, the Lean model with `unsupported.weak_cmpxchg`. Developed as "v41"
// on the crystal lane's fork, where it collided with the contract surface.
// v49 (the crystal lane's UNWRITTEN aggregate lane, ADDITIVE; reserved by
// takeover c654a054). `Constant::Uninit` at constant tag
// 15, tag only (the lane's type is its position in the enclosing aggregate).
// Read-gated `version >= 49`; the writer selects 49 only when a constant
// carries one; `RawV38`/`CanonicalV38` refuse (`UninitLaneRequiresV49`). The
// stable digest spells it with tag 15 too; it enters a digest only for a
// module that carries one. trust-ir-build admits it only as a DIRECT lane of
// an `Inst::Const` struct/tuple aggregate. Developed as "v42" on the crystal
// lane's fork, where it collided with the declared tuple layouts.
// v50 (the constant-size uniform array, ADDITIVE; reserved ae94794d as v54 and
// taken to the lowest open number 50 by 4a143d18). Two new tags, both
// read-gated `version >= 50`:
//   * `Constant::Splat { elem, len }` at Constant tag 16 — the element (one
//     constant) then `len` as a fixed u64. A `len < 2` payload is REFUSED at
//     decode (the §3 one-spelling rule: zero or one copy is the list spelling
//     `Constant::Array`), exactly as a non-canonical `U128` is;
//   * `Inst::ArraySplat { ty, value }` at Inst tag 59 — the `Array(e, n)` type
//     then the one operand.
// Neither encoding grows with the array length. The writer selects 50 only
// when one of them occurs, so a module carrying neither keeps its v38..=v49
// bytes exactly; `RawV38`/`CanonicalV38` refuse (`ArraySplatRequiresV50`).
// Developed unpushed as "v47" on 4f09dab8 (reservation 7f46e798, never
// pushed), before the crystal lane shipped v47..=v49; no blob carries that
// numbering outside the development branch.
// v51 (the INST wire batch, ADDITIVE; reserved dbd8c262). Every instruction and
// sub-op that existed in the enums ahead of its wire tag gets one, so the
// binary writer — and with it the infallible `Module::stable_digest` — has a
// spelling for everything a producer can emit. Ten tags, all read-gated
// `version >= 51`:
//   * `Inst::MakeAggregate { ty, variant, fields }` at Inst tag 60 (WS3.5) —
//     the aggregate type, the variant as a presence byte plus a v32, then the
//     lane list as a vec of value ids;
//   * `Inst::MemCopy { dst, src, bytes, overlap }` at Inst tag 61 (WS3.20) —
//     three operands, then `overlap` as a bool byte (1 = memmove);
//   * `Inst::MemSet { dst, byte, bytes }` at Inst tag 62 (WS3.20) — three
//     operands;
//   * `BinOp::RotL` / `RotR` / `FCopySign` at BinOp tags 23 / 24 / 25 and
//     `UnOp::CtLz` / `CtTz` / `BSwap` / `BitReverse` at UnOp tags 9..=12
//     (WS3.20), inside the unchanged `Inst::BinOp` / `Inst::UnOp` payloads.
// The writer selects 51 only when one of them occurs, so every other module
// keeps its v38..=v50 bytes exactly; `RawV38`/`CanonicalV38` refuse
// (`InstWireBatchRequiresV51`). Before this version the writer PANICKED on all
// ten (the `unencodable` clause, the `write_inst` arms), so no blob carrying
// one exists at any older header, and no digest of such a module existed to
// change.
// v52 (the assert panic kind, ADDITIVE; plan item P "Panics, faithfully" of
// the Trust superproject's sole-compile-path plan; reserved and taken over to
// the lowest open number in the commit before the code). `Inst::Assert`
// gains `kind: AssertKind`. The kind is the TAG, as `CmpXchg.weak` is:
//   * `AssertKind::Unspecified` keeps Inst tag 29 and its exact historical
//     bytes (the condition only), at every version, so every older blob
//     decodes to an `Unspecified` assert and every module without a kinded
//     assert keeps its bytes and its digest;
//   * any other kind is Inst tag 63, read-gated `version >= 52`: the
//     condition, then the kind as one AssertKind tag byte (0 Overflow, 1
//     DivByZero, 2 RemByZero, 3 BoundsCheck, 4 MisalignedPtr, 5 NullPtr)
//     and its payload — an AssertOverflowOp byte (0 Add .. 7 Neg) for
//     Overflow, two value ids (`index`, `len` / `required`, `found`) for
//     BoundsCheck / MisalignedPtr. `Unspecified` has NO AssertKind byte, so
//     tag 63 cannot spell it and each assert has exactly one encoding.
// The writer selects 52 only when a kinded assert occurs; `RawV38` /
// `CanonicalV38` refuse (`AssertKindRequiresV52`).
// v53 (typed call-unwind boundaries, ADDITIVE): appended Inst variants
// `CallCannotUnwind` (tag 64) and `CallIndirectCannotUnwind` (tag 65), both
// read-gated `version >= 53`. Their operands are the corresponding ordinary
// call operands, but the normative no-crossing unwind boundary is not a
// no-panic proof. Every codec must preserve the distinct constructor. A
// consumer unable to enforce this boundary MUST refuse it, including in
// functions with no handlers (`refuse/call_unwind_boundary_not_enforceable`).
// Old-version labels carrying either tag MUST be refused by the reader
// (`refuse/blob_call_boundary_below_its_version`,
// `refuse/blob_indirect_call_boundary_below_its_version`). Ordinary Call tags,
// payloads and selected versions are unchanged. Legacy projections refuse
// with `CallUnwindBoundaryRequiresV53` rather than erase the boundary.
// v54 (the panic site, ADDITIVE; amendment P, the second half of plan item P,
// `docs/SPEC_RATIFICATIONS.md` §19.1; reserved and taken over to the lowest
// open number in the two commits before the code; renumbered 53 -> 54, tags
// 64/65 -> 66/67, at its merge with main, where v53 had landed first). `Inst::Assert` gains
// `site: Option<PanicSite { entry, location }>` and `Inst::AssertInvoke`
// is new. Again the site is the TAG:
//   * tags 29 and 63 keep spelling the SITELESS asserts, byte for byte, so
//     every older blob decodes with `site: None` and every module without a
//     site keeps its bytes and its digest;
//   * a sited assert of ANY kind is Inst tag 66, read-gated `version >= 54`:
//     the condition, a kind-presence byte (0 `Unspecified`, 1 an AssertKind
//     byte and its payload follow; any other byte is `InvalidTag`), the entry
//     (a v32 function id, as a `Call` callee), then the location — a
//     PanicLocation byte (0 `Global` + a v32 global id, 1 `Value` + a
//     projected value id; any other byte is `InvalidTag`);
//   * `Inst::AssertInvoke` is Inst tag 67 under the same gate: tag 66's
//     payload, then `normal_dest`, the `normal_args` vec and `unwind_dest`
//     in `Invoke`'s order.
// The writer selects 54 only when a site occurs; `RawV38` / `CanonicalV38`
// refuse (`PanicSiteRequiresV54`).
// v55 (executable drops, ADDITIVE; amendment D Part 1,
// `docs/SPEC_RATIFICATIONS.md` §20; reserved as v59 and taken over to the
// lowest open number in the two commits before the code). Two additions,
// both read-gated `version >= 55`:
//   * the module DROP-GLUE TABLE, a trailing section after the v42 tuple
//     layouts: a v32 row count, then per row the glue (a v32 function id,
//     as a `Call` callee) and the dropped type (an inline type). The reader
//     refuses, as `InvalidData` and before any validator runs, a glue id not
//     strictly greater than the previous row's and a key equal to an earlier
//     row's (`refuse/blob_drop_glue_not_canonical`); whether a glue id names
//     a function, and its signature, are the validator's questions
//     (function ids are sparse keys, not positions). A header below 55
//     decodes with an empty table, so its drops stay unresolved;
//   * `Inst::DropInvoke` at Inst tag 68: `Drop`'s payload (the type, then the
//     pointer operand), then `normal_dest`, the `normal_args` vec and
//     `unwind_dest` in `Invoke`'s order.
// `Inst::Drop` keeps tag 57 and its v47 bytes. The writer selects 55 only
// when a module carries a table row or a `DropInvoke`, so every other module
// (every v47 module whose drops are unresolved included) keeps its bytes and
// its digests; `RawV38` / `CanonicalV38` refuse (`DropGlueRequiresV55`). The
// executable-content identity KEEPS the section: the table changes what a
// `Drop` executes, so `executable_content_digest_v1` moves with it.
// v56 (the unwinding twins, ADDITIVE; amendment D Part 2,
// `docs/SPEC_RATIFICATIONS.md` §21; reserved as v60 and taken over to the
// lowest open number in the two commits before the code).
// `Inst::InvokeIndirect` is new at Inst tag 69, read-gated `version >= 56`:
// `CallIndirect`'s tag-19 payload (the callee value, the signature id, the
// argument vec, the calling-convention byte), then `normal_dest`, the
// `normal_args` vec and `unwind_dest` in `Invoke`'s order. A non-C
// convention also raises the writer to the ABI surface, as on a
// `CallIndirect`. The writer selects 56 only when a module carries one, so
// every other module keeps its bytes and its digests; `RawV38` /
// `CanonicalV38` refuse (`UnwindTwinsRequiresV56`). Part 2's other half,
// unwinding as an exit under `PanicStrategy::Unwind`, is semantics only and
// changes no byte.
// v58 (nominal identity, ADDITIVE; roadmap WS3.9 / WS3.13, F-128 plan-of-record
// half + F-055; reserved 68602783 as v46, moved to v47 by 113a1c82, to v48 by
// takeover 6d3f5303, to v51 by takeover c654a054, taken to the lowest open
// number 50 by takeover ea68b453, moved back to 51 by takeover 4a143d18 when
// array-splat took 50, moved to 53 when the INST wire batch (v51) and the
// assert panic kind (v52) took the lowest open numbers by takeover and landed
// first, and moved to 58 when the call-unwind boundary (v53), the panic site
// (v54), drop glue (v55), the unwind twins (v56) and the generic-template
// floor (v57) did the same). Two trailing per-def fields and one trailing
// module section, each read-gated `version >= 58`:
//
//   * `StructDef.origin` / `EnumDef.origin`: `Option<TypeOrigin>`, one
//     presence byte then a variant tag (0 `Rust { stable_crate_id,
//     def_path_hash, args_digest }`, 1 `Clean { decl, env_digest }`). The key
//     names the SOURCE ENTITY a definition is the image of, so a linker can
//     tell two structurally identical types apart and can see one entity
//     carried by two producers. It never ADMITS: a comparator may only SPLIT
//     on it or REFUSE on it, and an absent key compares structurally as
//     before.
//
//   * `Module.closure_layouts`: declared byte images for `Ty::Closure`,
//     written after the v55 drop-glue table (itself after the v42 tuple
//     table) with exactly the tuple table's coherence rules.
//
// Both are selected only when USED, so a module with no keys and no closure
// layouts keeps its v38..=v57 bytes exactly; RawV38/CanonicalV38 refuse with
// `NominalIdentityRequiresV58`.
// v59 (typed effect summaries and world epochs, ADDITIVE; roadmap WS1.14,
// F-013; reserved 6f202fa4 as v52, moved to 54 by the takeovers 4a143d18
// and 2caf23fa, to 53 when 73ca45ff released an obsolete reservation below
// it, to 60 as the INST wire batch (v51), the assert panic kind (v52), the
// call-unwind boundary (v53), the panic site (v54), drop glue (v55), the
// unwind twins (v56) and the generic-template floor (v57) took the lowest
// open numbers and landed first, and back to 59 when ruling WA-4 released
// typed-signature-abi; nominal identity landed v58 ahead of it). Two
// carriers, both read-gated `version >= 59`,
// and the writer selects 59 only when one is USED, so a module using neither
// keeps its earlier bytes exactly; `RawV38`/`CanonicalV38` refuse
// (`EffectSummaryRequiresV59`).
//   * `FunctionSummary.effects: Option<EffectSummary>` — a presence byte
//     appended to every summary record (after the v41 `backed_by`), then the
//     `reads` and `writes` `EffectSet`s (tag 0 Nothing, 1 Places + a count +
//     the places, 2 Everything; an `EffectPlace` is tag 0 ParamPointee + index
//     or 1 Global + global id) and four strict bool bytes (`allocates`,
//     `frees`, `may_unwind`, `io`; anything but 0/1 is `InvalidTag`). `None`
//     (byte 0) is UNRECORDED, never "no effects".
//   * `ClausePlace::WorldPre` / `WorldPost` at clause-place tags 8 and 9 — the
//     entry and exit epochs of the ambient world. A v58-or-older header
//     carrying either tag is refused with `InvalidTag`.
// `obligation_content_digest` moves to `trust_ir.obligation.digest.v8`: the
// effect summary changes what a contract MEANS.
// v60 (typed signature placement, `SIGNATURE_ABI_FORMAT_VERSION`): see that
// constant and `docs/binary-format.md`.
// v61 (the certificate-binding carrier and the evidenced codegen license,
// ADDITIVE; reserved 07fb5515 (the version) and d46593b1 (body-gate tag 3 and
// the `trust_ir.function.body.v1` domain) — the two proof-surface identity
// carriers WS1.12 deferred to "the proof-surface wire batch", roadmap
// WS6.7(b); moved 60 -> 61 when typed signature placement landed v60 first). (1) `CleanCicKernelRecheck.binding: Option<CertificateBinding>` is a
// presence byte after the directive's `allowed_axioms`, then the binding in
// struct order: the environment and statement digests, a presence-prefixed
// `origin_module` digest, a presence-prefixed `source` (`decl` string +
// closure digest), the `callees` link symbols, and a presence-prefixed WS1.13
// island (`environment`: its declaration bytes, length-framed and opaque, then
// the digest it records, both carried verbatim). Read-gated
// `version >= 61`: an older blob decodes every directive UNBOUND (the
// pre-binding meaning), and a presence tag other than 0/1 is `InvalidTag`.
// The writer selects 61 only for a module that carries a binding or an
// evidenced license, so every other module keeps its older bytes exactly;
// `RawV38`/`CanonicalV38` refuse (`CertificateBindingRequiresV61`). Before
// this version no binary writer could encode a bound certificate and every
// fallible entry point refused the module rather than narrow the binding to
// `None` (`CertificateBindingUnencodable`, now retired with its message).
// (2) `BodyGate::Gated { evidence: Some(GateEvidence { obligation,
// body_digest }) }` is body-gate tag 3: the pooled authority, the obligation
// id, the body digest. Tag 2 keeps the evidence-free license byte for byte;
// tag 3 under an older header is `InvalidTag(3)`. The executable projection
// strips the license with its evidence, and `body_digest` is
// `Module::function_body_digest` over that projection, so stamping the
// evidence never moves the digest it cites.
// v62 (the entry-state pointee clause place, ADDITIVE; roadmap DG-63, the
// trust-ir prerequisite of WS5.5; reserved 98c73c99 as v61 behind the
// then-open v59 effect-summaries and v60 certificate-binding reservations;
// moved 61 -> 62 when typed signature placement took v60 and certificate
// binding v61 first, so it lands after both, in number order).
// `ClausePlace::ParamPointeeEntry { index }` at
// clause-place tag 10, then a v32 parameter index, wherever a clause binding
// is written (a summary clause, an obligation formula, a spec carrier). It is
// the value at entry behind a `&T` / `&mut T` parameter: the place a
// `requires *x > 0` or an `old(*x)` binds, which no place could name before
// (`Param` is the reference itself, `MutParamExit` the value at exit).
// Read-gated `version >= 62`, so an older header carrying tag 10 is refused
// with `InvalidTag(10)` (`refuse/blob_param_pointee_place_below_its_version`)
// rather than read. The writer selects 62 only when a binding USES the place,
// so every other module keeps its bytes and its digests; `RawV38` /
// `CanonicalV38` refuse (`ParamPointeePlaceRequiresV62`), which heads the
// highest-wins chain. No digest domain moves: the stable preimages spell the
// place with the same fresh tag byte, so no older preimage changes.
// v67 (tensor region, ADDITIVE; PKG-U13a, Trust TENSOR-REOPEN). The tensor
// region's first slice, one type and one instruction, both appended:
// `Ty::Tensor(elem, rank)` at type tag 41 (0x29) — a v32 rank, then the
// element type, exactly as `Vector` spells its lanes and element — and
// `Inst::TensorContract { ty, lhs, rhs, batch, contract }` at Inst tag 71
// (0x47) — the result type, the two operand ids, then each axis-pair list
// (`batch`, then `contract`) as a v32 count followed by a v32 left axis and a
// v32 right axis per pair. Both tags are read-gated `version >= 67`
// (`TENSOR_FORMAT_VERSION`): an old-version label carrying either is refused
// by the reader with `InvalidTag(41)` / `InvalidTag(71)` rather than read
// (`refuse/blob_tensor_below_its_version`). The type fixes ONLY the element
// type and the rank; each extent is a run-time value the tensor carries, so
// the codec checks no shape. Whether the element is an integer and whether a
// contraction's ranks and axes agree are the validator's to decide
// (`InvalidTensorType`, `InvalidTensorContract`), never the codec's. The
// writer selects 67 only when a tensor type occurs anywhere a type is spelled
// or a contraction occurs, so every other module keeps its older bytes and
// digests; `RawV38` / `CanonicalV38` refuse (`TensorRequiresV67`) rather than
// erase the tensor, next below the v68 refusal in the highest-wins chain. No digest
// domain moves: the stable preimages spell the type with the same fresh tag,
// so only a module that carries a tensor gets a new spelling.
// v68 (tensor map, reduce and view, ADDITIVE; PKG-U13c). Three instructions,
// appended: `Inst::TensorMap { ty, args, body }` at Inst tag 72 (0x48) — the
// result type, the operand ids as a counted list, then the body as a counted
// list of `TensorMapNode`s (one tag byte: 0 BinOp, 1 UnOp, 2 ICmp, 3 Select,
// 4 Cast; then the scalar instruction's own fields in its own order, the
// operator by its scalar wire tag and each lane a v32); `Inst::TensorReduce
// { ty, src, op, axes, order }` at tag 73 (0x49) — the result type, the
// source id, a `TensorReduceOp` byte (0 Add .. 8 UMax), the axes as a counted
// v32 list and a `TensorReduceOrder` byte (0 RowMajor); and
// `Inst::TensorView { ty, src, params, exprs, shape, index, fill }` at tag 74
// (0x4A) — the result type, the source id, the parameter ids as a counted
// list, the coordinate function as a counted list of `TensorIndexExpr`s (one
// tag byte: 0 Lit then a v64, 1 Param / 2 SrcExtent / 3 Coord then a v32,
// 4 Add .. 10 Max then two v32 node ids), the shape and the index as counted
// v32 lists, then the fill as 0, or 1 and a value id. All three tags are
// read-gated `version >= 68` (`TENSOR_MAP_REDUCE_VIEW_FORMAT_VERSION`), so an
// older header carrying one is `InvalidTag(72..=74)`
// (`refuse/blob_tensor_map_reduce_view_below_its_version`). The codec checks
// no typing, lane, axis or node rule: those are the validator's
// (`InvalidTensorMap`, `InvalidTensorReduce`, `InvalidTensorView`). The writer
// selects 68 only when one of the three occurs, so every other module keeps
// its bytes and digests; `RawV38` / `CanonicalV38` refuse
// (`TensorMapReduceViewRequiresV68`). No digest domain moves.
// v69 (tensor gather and scatter, ADDITIVE; PKG-U13d, SPEC_RATIFICATIONS
// §26). Two instructions, appended: `Inst::TensorGather { ty, data, coords }`
// at Inst tag 75 (0x4B) — the result type, the data id, then the coordinate
// tensor ids as a counted list; and `Inst::TensorScatter { ty, init, src,
// coords }` at tag 76 (0x4C) — the result type, the initial tensor's id, the
// source id, then the coordinate tensor ids as a counted list. Both tags are
// read-gated `version >= 69` (`TENSOR_GATHER_SCATTER_FORMAT_VERSION`), so an
// older header carrying one is `InvalidTag(75 | 76)`
// (`refuse/blob_tensor_gather_scatter_below_its_version`). The codec checks no
// rank, element or arity rule: those are the validator's
// (`InvalidTensorGather`, `InvalidTensorScatter`). The writer selects 69 only
// when one of the two occurs, so every other module keeps its bytes and
// digests; `RawV38` / `CanonicalV38` refuse
// (`TensorGatherScatterRequiresV69`). No digest domain moves.
// v70 (content-addressed weight blobs, ADDITIVE; PKG-U13e,
// `docs/SPEC_RATIFICATIONS.md` §27). Two additions, both read-gated
// `version >= 70` (`TENSOR_BLOB_FORMAT_VERSION`):
//   * `Constant::TensorBlob { digest, dims }` at Constant tag 18 (0x12; 17 is
//     the template extension's): the 32 digest bytes, then the extents as a
//     counted list of fixed-width `u64`s. An older header carrying tag 18 is
//     `InvalidTag(18)` (`refuse/blob_tensor_blob_below_its_version`);
//   * the module BLOB TABLE, a trailing section after the v58 closure
//     layouts: a row count, then per row the 32 digest bytes and the counted
//     bytes. The reader refuses, as `InvalidData` and before any validator
//     runs, a digest not strictly greater than the previous row's, so each
//     digest is listed once (`refuse/blob_tensor_blob_table_not_canonical`);
//     whether a row's bytes hash to its digest, and whether a constant's
//     digest names a row, are the validator's questions (`InvalidBlobTable`,
//     `MissingBlob`), asked again by both engines where a constant reads it.
// The writer selects 70 only when a module carries a tensor blob constant or
// a table row, so every other module keeps its bytes and its digests;
// `RawV38` / `CanonicalV38` refuse (`TensorBlobRequiresV70`), which heads the
// highest-wins chain. The module identity (`stable_digest`) and the
// executable-content identity KEEP the section, so a changed weight is a
// changed module; a function body's identity does not, because its image
// holds no table (the body names the digest, never the bytes). No digest
// domain moves: the blob digest is plain SHA-256 of the bytes.
/// Latest format version supported by this build. Writers select v38 for
/// legacy modules, v39 only when a nominal dialect type occurs, v40 only when a
/// `FatPtrKind::ContainerVtable` occurs, and v41 only when a contract-surface
/// feature (see the v41 ledger entry) occurs. Declared tuple layouts select
/// v42, a nominal opaque runtime handle selects v43, and an import row
/// recorded under a non-V2 identity scheme selects v44. Any ABI-surface fact
/// (function visibility / section / retention, per-argument ABI facts, the
/// v45 calling conventions, 128-bit enum tag reprs) selects v45, and any v46
/// typed spec-carrier feature selects v46. An `Inst::Drop` selects v47, a
/// WEAK `Inst::CmpXchg` selects v48, a `Constant::Uninit` lane selects v49,
/// a `Constant::Splat` or an `Inst::ArraySplat` selects v50, and any member of
/// the INST wire batch (`MakeAggregate`, `MemCopy`, `MemSet`, and the
/// `RotL`/`RotR`/`FCopySign`/`CtLz`/`CtTz`/`BSwap`/`BitReverse` sub-ops)
/// selects v51. A kinded `Inst::Assert` (any `AssertKind` but `Unspecified`)
/// selects v52. Typed non-propagating call boundaries select v53, a
/// panic site (a sited `Inst::Assert` or any `Inst::AssertInvoke`) selects
/// v54, a drop-glue table row or an `Inst::DropInvoke` selects v55, and an
/// `Inst::InvokeIndirect` selects v56.
///
/// v57 is a template blob's version floor (amendment S): no level-R content is
/// new at it, so no module writes it, and the level-R reader accepts its
/// header (one wire counter; a template is a separate `TRUST_IS` artifact).
///
/// A nominal type-origin key or a declared closure layout selects v58.
///
/// A typed effect summary or a world-epoch clause place selects v59.
/// Retained callable source-to-carrier ABI placement evidence selects v60.
///
/// A certificate binding (`CleanCicKernelRecheck.binding`) or an evidenced
/// license (`BodyGate::Gated { evidence: Some(..) }`) selects v61.
///
/// A clause binding of the entry-state pointee place
/// (`ClausePlace::ParamPointeeEntry`) selects v62.
///
/// An `Inst::MakeClosure` selects v63, an addressable layout-only storage
/// type (`Ty::Storage`) v64, a variant-free nominal enum or a
/// single-inhabited enum layout (`EnumTagEncoding::SingleInhabited`) v65, and
/// a declared closure frame's nominal origin
/// (`ClosureLayoutDescriptor.origin`) v66.
///
/// A tensor type (`Ty::Tensor`, anywhere a type is spelled) or an
/// `Inst::TensorContract` selects v67 (`TENSOR_FORMAT_VERSION`), and an
/// `Inst::TensorMap`, `Inst::TensorReduce` or `Inst::TensorView` v68
/// (`TENSOR_MAP_REDUCE_VIEW_FORMAT_VERSION`), and an `Inst::TensorGather` or
/// `Inst::TensorScatter` v69 (`TENSOR_GATHER_SCATTER_FORMAT_VERSION`), and a
/// `Constant::TensorBlob` or a blob table row v70
/// (`TENSOR_BLOB_FORMAT_VERSION`).
///
/// `VERSION` may only equal the highest `shipped` row of
/// `crates/trust-ir/wire_versions.tsv`; raising it without flipping that
/// reserved row to `shipped` fails the `wire_version_ledger` test.
pub const VERSION: u32 = 70;
/// Latest supported TrustIR binary wire-format version.
pub const FORMAT_VERSION: u32 = VERSION;
/// Baseline encoding retained for modules without v39 nominal dialect types
/// or v40 `FatPtrKind::ContainerVtable` fat pointers.
pub const BASE_FORMAT_VERSION: u32 = 38;
const DIALECT_TYPE_FORMAT_VERSION: u32 = 39;
/// Format version selected when a `FatPtrKind::ContainerVtable` occurs.
pub const CONTAINER_VTABLE_FORMAT_VERSION: u32 = 40;
/// Format version selected when a module uses any v41 contract-surface feature:
/// the codegen license, typed contract clauses, cross-crate identity, or the
/// ABI/linkage residue.
pub const CONTRACT_SURFACE_FORMAT_VERSION: u32 = 41;
/// Concrete tuple descriptors are an additive trailing section.
pub const TUPLE_LAYOUT_FORMAT_VERSION: u32 = 42;
/// Format version selected when a nominal opaque runtime handle
/// (`Ty::Handle`, type tag 38) occurs anywhere in the module.
pub const HANDLE_TYPE_FORMAT_VERSION: u32 = 43;
/// Addressable layout-only storage, type tag 40.
pub const STORAGE_LAYOUT_FORMAT_VERSION: u32 = 64;
/// Payload-only enum image with an explicit sole inhabited variant selector.
pub const SINGLE_INHABITED_ENUM_FORMAT_VERSION: u32 = 65;
/// Format version selected when any `Module.imports` row is recorded under an
/// identity scheme other than the legacy V2 (`ModuleImport.scheme`, WS4.10).
pub const IMPORT_SCHEME_FORMAT_VERSION: u32 = 44;
/// Format version selected when a module uses any ABI-surface fact (roadmap
/// WS3.10/WS3.11/WS3.12/WS3.14(b)): function visibility / section /
/// retention, per-argument ABI facts, a v45 calling convention, or a 128-bit
/// enum tag representation.
pub const ABI_SURFACE_FORMAT_VERSION: u32 = 45;
/// Format version selected when a module uses any v46 typed spec-carrier
/// feature: a `SpecVar.sort`, a `SpecInvariant.typed`, a `SpecModule.temporal`
/// property, a `ProofKind::CleanTheorem` binding, or a `ProofObligation.spec`
/// temporal backref.
pub const SPEC_CARRIER_FORMAT_VERSION: u32 = 46;
/// Crystal lane (wave-DS): format version selected when an `Inst::Drop` (instruction tag 57)
/// occurs. Raised PER MODULE by `collect_inst_strings`, so a module that drops nothing keeps
/// the version it wrote before, byte for byte. The lane numbered this v40 on its own lineage,
/// where it collided with `CONTAINER_VTABLE_FORMAT_VERSION`; on main it is v47.
pub const DROP_INST_FORMAT_VERSION: u32 = 47;
/// Crystal lane (D3): format version selected when a WEAK `Inst::CmpXchg` occurs (instruction
/// tag 58, carrying tag 13's payload). Raised PER MODULE by `collect_inst_strings`, exactly as
/// `DROP_INST_FORMAT_VERSION` is, so a module whose every compare-exchange is strong keeps
/// tag 13 and the version it wrote before, byte for byte. The lane numbered this v41 on its
/// own lineage, where it collided with `CONTRACT_SURFACE_FORMAT_VERSION`; on main it is v48.
pub const WEAK_CMPXCHG_FORMAT_VERSION: u32 = 48;
/// Crystal lane (E3b): format version selected when a `Constant::Uninit` lane occurs
/// (constant tag 15, the first free constant byte after `Constant::Bytes`'s 14). Raised PER
/// MODULE by `collect_constant_strings`, so a module with no unwritten lane keeps the version it
/// wrote before, byte for byte. The lane numbered this v42 on its own lineage, where it
/// collided with `TUPLE_LAYOUT_FORMAT_VERSION`; on main it is v49.
pub const UNINIT_LANE_FORMAT_VERSION: u32 = 49;
/// Format version selected when a module carries the constant-size uniform
/// array: a `Constant::Splat` (Constant tag 16) anywhere a constant is written,
/// or an `Inst::ArraySplat` (Inst tag 59).
pub const ARRAY_SPLAT_FORMAT_VERSION: u32 = 50;
/// Format version selected when a module carries a member of the INST wire
/// batch: an `Inst::MakeAggregate` (Inst tag 60), an `Inst::MemCopy` (61), an
/// `Inst::MemSet` (62), a `BinOp::RotL` / `RotR` / `FCopySign` (BinOp tags
/// 23..=25) or a `UnOp::CtLz` / `CtTz` / `BSwap` / `BitReverse` (UnOp tags
/// 9..=12). Raised PER MODULE by `collect_inst_strings`, so a module with none
/// of them keeps the version it wrote before, byte for byte.
pub const INST_WIRE_BATCH_FORMAT_VERSION: u32 = 51;
/// Format version selected when a module carries a KINDED `Inst::Assert`
/// (plan item P: Inst tag 63, the condition, then an `AssertKind`). Raised
/// PER MODULE by `collect_inst_strings`, so a module whose every assert is
/// `AssertKind::Unspecified` keeps tag 29 and the version it wrote before,
/// byte for byte.
pub const ASSERT_KIND_FORMAT_VERSION: u32 = 52;

/// Typed non-propagating call boundaries. Ordinary calls keep their old tags
/// and bytes; only CallCannotUnwind / CallIndirectCannotUnwind raise the header.
pub const CALL_UNWIND_BOUNDARY_FORMAT_VERSION: u32 = 53;

#[cfg(test)]
#[path = "binary/call_unwind_boundary_tests.rs"]
mod call_unwind_boundary_tests;

/// Format version selected when a module carries a panic site (amendment P:
/// a sited `Inst::Assert`, Inst tag 66, or an `Inst::AssertInvoke`, tag 67).
/// Raised PER MODULE by `collect_inst_strings`, so a module without a site
/// keeps the version it wrote before, byte for byte, and its digest.
pub const PANIC_SITE_FORMAT_VERSION: u32 = 54;

/// Format version selected when a module carries a drop-glue table row
/// (amendment D: the trailing `Module.drop_glue` section) or an
/// `Inst::DropInvoke` (Inst tag 68). Raised PER MODULE by
/// `collect_strings_into` / `collect_inst_strings`, so a module with neither
/// keeps the version it wrote before, byte for byte, and its digests.
pub const DROP_GLUE_FORMAT_VERSION: u32 = 55;

#[cfg(test)]
#[path = "binary/drop_glue_tests.rs"]
mod drop_glue_tests;

/// Format version selected when a module carries an `Inst::InvokeIndirect`
/// (amendment D, Part 2: Inst tag 69, `CallIndirect`'s unwinding twin).
/// Raised PER MODULE by `collect_inst_strings`, so a module without one
/// keeps the version it wrote before, byte for byte, and its digests.
pub const UNWIND_TWINS_FORMAT_VERSION: u32 = 56;

/// The version floor of a TEMPLATE blob (amendment S, `docs/SPEC_RATIFICATIONS.md`
/// §22): magic `TRUST_IS`, then the module sections written by the same
/// writers at `X = TemplateRef`, where `Ty` tag 39 and `Constant` tag 17 spell
/// `Ext`. A template is written at `max(TEMPLATE_FORMAT_VERSION, the content's
/// minimum lossless version)`; the level-R reader refuses a template by magic,
/// and tags 39 / 17 at every version even under a forged module magic, because
/// the level-R extension (`NoExt`) has no value to read.
pub const TEMPLATE_FORMAT_VERSION: u32 = 57;

/// The magic of a template blob (amendment S); a module blob's is `TRUST_IR`.
pub const TEMPLATE_MAGIC: &[u8; 8] = &crate::codec::TRUST_IS_TEMPLATE_MAGIC;

/// The `Ty` tag of the extension variant: template blobs only.
const TY_EXT_TAG: u8 = 39;
/// The `Constant` tag of the extension variant: template blobs only.
const CONSTANT_EXT_TAG: u8 = 17;

/// How a level's extension is written and read. Level R (`NoExt`) never
/// writes (it has no value) and REFUSES the extension tag on read, at every
/// version; level S (`TemplateRef`) writes the reference's tag and id.
trait WireExt: crate::level::Extension + Sized {
    /// Whether this level has an extension value at all. The level-R reader
    /// does not, so its `Ty` / `Constant` matches fall through to their own
    /// `InvalidTag` refusal arm for tags 39 / 17.
    fn reads_ext() -> bool;
    fn write_ext(buf: &mut impl BinarySink, ext: &Self);
    fn read_ext(r: &mut Reader<'_>) -> Result<Self, BinaryError>;
}

impl WireExt for NoExt {
    fn reads_ext() -> bool {
        false
    }

    fn write_ext(_buf: &mut impl BinarySink, ext: &Self) {
        ext.unreachable()
    }

    fn read_ext(_r: &mut Reader<'_>) -> Result<Self, BinaryError> {
        Err(BinaryError::InvalidData(
            "the level-R reader has no extension value to read".to_string(),
        ))
    }
}

impl WireExt for TemplateRef {
    fn reads_ext() -> bool {
        true
    }

    fn write_ext(buf: &mut impl BinarySink, ext: &Self) {
        match ext {
            TemplateRef::Param(param) => {
                write_u8(buf, 0);
                write_v32(buf, param.index());
            }
            TemplateRef::Hole(hole) => {
                write_u8(buf, 1);
                write_v32(buf, hole.index());
            }
        }
    }

    fn read_ext(r: &mut Reader<'_>) -> Result<Self, BinaryError> {
        match r.read_u8()? {
            0 => Ok(TemplateRef::Param(crate::value::ParamId::new(
                r.read_v32()?,
            ))),
            1 => Ok(TemplateRef::Hole(crate::value::HoleId::new(r.read_v32()?))),
            t => Err(BinaryError::InvalidTag(t)),
        }
    }
}

#[cfg(test)]
#[path = "binary/unwind_twins_tests.rs"]
mod unwind_twins_tests;

/// Format version selected when a `StructDef`/`EnumDef` carries a nominal
/// [`crate::ty::TypeOrigin`] key, or the module declares a closure layout.
/// Both are additive and both land under one reserved number (the "nominal
/// identity" group of the WS8.5 ledger).
pub const NOMINAL_IDENTITY_FORMAT_VERSION: u32 = 58;
/// Roadmap WS1.14 (F-013): format version selected when a module carries a
/// typed effect summary (`FunctionSummary.effects`) or binds a world epoch
/// (`ClausePlace::WorldPre` / `WorldPost`, clause-place tags 8 and 9). Raised
/// PER MODULE by the string collector, so a module using neither keeps the
/// version it wrote before, byte for byte.
pub const EFFECT_SUMMARY_FORMAT_VERSION: u32 = 59;
/// Typed callable ABI facts. The descriptor is a bounded canonical named-field
/// payload; it has no numeric enum tags and is part of every content digest.
pub const SIGNATURE_ABI_FORMAT_VERSION: u32 = 60;
/// Format version selected when any `CleanCicKernelRecheck.binding` (the
/// WS1.12a `CertificateBinding`) or any evidenced license
/// (`BodyGate::Gated { evidence: Some(..) }`, WS1.12(c)) is present. Raised
/// PER MODULE during string collection, so a module with neither keeps the
/// version it wrote before, byte for byte. Reserved 07fb5515 / d46593b1
/// (roadmap WS6.7(b): the proof-surface identity carriers WS1.12 deferred).
pub const CERTIFICATE_BINDING_FORMAT_VERSION: u32 = 61;

/// Format version selected when a clause binding names the entry-state
/// pointee of a reference parameter (`ClausePlace::ParamPointeeEntry`,
/// clause-place tag 10; roadmap DG-63). Raised PER MODULE by the formula
/// string collector, wherever a binding is carried, so a module that binds no
/// such place keeps the version it wrote before, byte for byte, and its
/// digests.
pub const PARAM_POINTEE_PLACE_FORMAT_VERSION: u32 = 62;

/// Runtime SSA closure construction (Inst tag 70).
pub const MAKE_CLOSURE_FORMAT_VERSION: u32 = 63;
/// Nominal source identity on a declared closure capture frame.
pub const CLOSURE_ORIGIN_FORMAT_VERSION: u32 = 66;
/// The tensor region's first slice (PKG-U13a, Trust DECISION_QUEUE
/// TENSOR-REOPEN): `Ty::Tensor` (Ty tag 41) and `Inst::TensorContract` (Inst
/// tag 71).
pub const TENSOR_FORMAT_VERSION: u32 = 67;
/// The tensor region's map, reduction and view (PKG-U13c): `Inst::TensorMap`
/// (Inst tag 72), `Inst::TensorReduce` (73) and `Inst::TensorView` (74).
pub const TENSOR_MAP_REDUCE_VIEW_FORMAT_VERSION: u32 = 68;
/// The tensor region's gather and scatter (PKG-U13d): `Inst::TensorGather`
/// (Inst tag 75) and `Inst::TensorScatter` (76).
pub const TENSOR_GATHER_SCATTER_FORMAT_VERSION: u32 = 69;
/// Content-addressed weight blobs (PKG-U13e): `Constant::TensorBlob`
/// (Constant tag 18) and the module blob table, a trailing section after the
/// v58 closure layouts.
pub const TENSOR_BLOB_FORMAT_VERSION: u32 = 70;
/// The `Constant` tag of a content-addressed tensor (v70).
const CONSTANT_TENSOR_BLOB_TAG: u8 = 18;

#[cfg(test)]
#[path = "binary/tensor_blob_tests.rs"]
mod tensor_blob_tests;
#[cfg(test)]
#[path = "binary/tensor_gather_scatter_tests.rs"]
mod tensor_gather_scatter_tests;
#[cfg(test)]
#[path = "binary/tensor_map_reduce_view_tests.rs"]
mod tensor_map_reduce_view_tests;
#[cfg(test)]
#[path = "binary/tensor_region_tests.rs"]
mod tensor_region_tests;

#[cfg(test)]
#[path = "binary/param_pointee_place_tests.rs"]
mod param_pointee_place_tests;
// The public projection axes below name the v38 representation explicitly.
// A wire-version bump must therefore rename/review those axes rather than
// silently changing the bytes they select.
const PROJECTED_MODULE_BINARY_VERSION: u32 = 38;
const _: () = assert!(
    BASE_FORMAT_VERSION == PROJECTED_MODULE_BINARY_VERSION,
    "v38-named module projections require an explicit wire-version review"
);
/// Oldest wire version a reader of this build accepts (the v24 read-floor
/// move). Reported by `trust_ir::BUILD_IDENTITY`.
pub(crate) const MIN_READ_VERSION: u32 = 23;
/// Versions inside `MIN_READ_VERSION..=VERSION` that are nonetheless REFUSED on
/// read: the ambiguous-lineage range (see the VERSION ledger). Reported by
/// `trust_ir::BUILD_IDENTITY`; the reader's header check uses this constant.
pub(crate) const AMBIGUOUS_LINEAGE_VERSIONS: std::ops::RangeInclusive<u32> = 26..=28;

/// The header version a binary blob DECLARED, as the reader validated and
/// kept it — decode PROVENANCE, returned by
/// [`deserialize_module_with_wire_version`] BESIDE the module and never
/// inside it.
///
/// A [`Module`] carries no field for this, on purpose: a field would change
/// the module's serde shape (and spend the one trailing conditionally-skipped
/// positional-MessagePack slot), and it would put decode provenance into
/// content identity, where it does not belong — two blobs at different
/// versions that decode to the same module ARE the same module, and
/// [`Module::stable_digest`] says so (`wire_version_is_not_module_content`
/// measures it). So the version travels next to the module, in this type.
///
/// # Only the decoder can mint one
///
/// The field is private and there is no constructor. The sole producer is the
/// binary reader, at the point where it has checked the header against the
/// accepted set (`MIN_READ_VERSION..=VERSION` minus the ambiguous-lineage
/// range) — so a `WireVersion` in hand is a version some blob actually
/// declared and this build actually read, and rustc refuses a fabricated
/// one. That is what lets `trust_ir_build::validate_module_as_decoded` state
/// a rule over the PRODUCING version at all: [`crate::BodyGate`]'s producer
/// conformance rule (a v41-or-later producer emits `Ungated` or `Gated` for
/// every bodied function; a bodied wire tag `0` at v41+ is refused) was
/// "not format-enforceable" only while the decoder dropped this number.
///
/// # What it does not prove
///
/// That the declaring producer was honest or conforming — the header is the
/// writer's claim, and a rule read against it says what a producer CLAIMING
/// this version must have done, refusing the blob when it did not. And it
/// says nothing about a module reached by any other route: hand-built, parsed
/// from text / JSON / MessagePack, or decoded through [`deserialize_module`],
/// which drops the version. Such a module has no `WireVersion`, so no
/// version-phrased rule can apply to it; that residual is stated here on the
/// type rather than papered over.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct WireVersion(u32);

impl WireVersion {
    /// The declared header version, inside `MIN_READ_VERSION..=VERSION` and
    /// outside the ambiguous-lineage range.
    #[must_use]
    pub fn get(self) -> u32 {
        self.0
    }

    /// True iff the blob was written at [`CONTRACT_SURFACE_FORMAT_VERSION`]
    /// (v41) or later: the versions whose function records carry the
    /// three-valued `body_gate` tag, and whose producers are therefore bound
    /// by the rule that a bodied function's tag is `1` or `2`, never `0`.
    #[must_use]
    pub fn claims_contract_surface(self) -> bool {
        self.0 >= CONTRACT_SURFACE_FORMAT_VERSION
    }
}

impl core::fmt::Display for WireVersion {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "v{}", self.0)
    }
}
use crate::Visibility;
use crate::imports::IdentityScheme;
use crate::proof::{ClauseBinding, ClausePlace, ClauseSort, CoverageAssurance, CoverageBound};
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

/// Function-body normalization used by a projected binary plan.
///
/// Adaptive variants choose the minimum lossless format during string
/// collection. Version-limited variants reject types unavailable in that
/// format; legacy-only modules retain their existing v38 bytes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ModuleBinaryBody {
    /// Preserve function bodies, selecting the minimum lossless wire format.
    Raw,
    /// Canonicalize bodies, selecting the minimum lossless wire format.
    Canonical,
    /// Preserve function block order, SSA IDs, and parameter-attribute rows.
    RawV38,
    /// Apply TrustIR's v38 canonical block/SSA/parameter-attribute form.
    /// Functions already proven to have that exact form use the borrowed raw
    /// walk without allocating per-function block-order or SSA-remap tables.
    CanonicalV38,
}

/// Symbol and function-table normalization used by a projected binary plan.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ModuleSymbolProjection<'a> {
    /// Preserve every source name and the declared function-table order.
    Exact,
    /// Use a fixed module name, stable `FuncId`-ordered functions, ID-based
    /// function names, and original-ordinal-based global names.
    StableIdOrdinalNames {
        module_name: &'a str,
        function_prefix: &'a str,
        global_prefix: &'a str,
    },
}

/// Proof-obligation rows retained by a projected binary plan.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ModuleObligationRows<'a> {
    /// Retain the declared proof-obligation table exactly.
    All,
    /// Omit exactly the uniquely named IDs without renumbering retained IDs.
    ///
    /// Validation rejects references retained inside this [`Module`]. It
    /// cannot inspect separate proof-lineage manifests, verification bundles,
    /// cache records, or other caller-owned sidecars; callers must update or
    /// reject those external references as part of the same identity change.
    OmitIds(&'a [ProofId]),
}

/// Closed, deterministic axes for a projected module encoding.
///
/// This describes an identity image, not a proof-carrying transformation of
/// the source [`Module`]. In particular, it does not produce lineage or a
/// certificate relating the image to the source module.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ModuleBinaryOptions<'a> {
    pub body: ModuleBinaryBody,
    pub symbols: ModuleSymbolProjection<'a>,
    pub obligations: ModuleObligationRows<'a>,
}

impl Default for ModuleBinaryOptions<'_> {
    fn default() -> Self {
        Self {
            body: ModuleBinaryBody::RawV38,
            symbols: ModuleSymbolProjection::Exact,
            obligations: ModuleObligationRows::All,
        }
    }
}

/// A fail-closed error in an explicitly requested binary projection.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BinaryProjectionError {
    /// A v38 projection cannot represent the module's nominal dialect types.
    DialectTypeRequiresV39,
    /// A v38 projection cannot represent the module's `ContainerVtable` fat
    /// pointers (v40); a module carrying both nominal dialect types and a
    /// `ContainerVtable` reports this variant, the higher requirement.
    ContainerVtableRequiresV40,
    /// A v38 projection cannot represent the module's v41 contract-surface
    /// content (codegen license, typed clauses, cross-crate identity, or the
    /// ABI/linkage residue). The highest requirement wins.
    ContractSurfaceRequiresV41,
    /// A v38 projection cannot represent the module's declared tuple layouts
    /// (v42).
    TupleLayoutRequiresV42,
    /// A v38 projection cannot represent the module's nominal opaque runtime
    /// handles (v43).
    HandleTypeRequiresV43,
    /// A v38 projection cannot represent an import row recorded under an
    /// identity scheme other than the legacy V2 (`ModuleImport.scheme`, v44).
    ImportSchemeRequiresV44,
    /// A v38 projection cannot represent the module's v45 ABI-surface facts
    /// (function visibility / section / retention, per-argument ABI facts, a
    /// v45 calling convention, or a 128-bit enum tag repr).
    AbiSurfaceRequiresV45,
    /// NO binary version can represent a lexical-scope inlining chain
    /// (`ScopeData.inlined_at`, WS4.19) yet: its carrier is a member of the
    /// next open wire batch and no number has been reserved for it. Every
    /// projection refuses such a module rather than dropping the chain
    /// (`ScopeData` docs; the infallible entry points panic with this text).
    InlinedScopeChainUnencodable {
        function: u32,
        scope: u32,
    },
    /// A v38 projection cannot represent the module's typed spec carrier: a
    /// `SpecVar.sort`, a `SpecInvariant.typed`, a `SpecModule.temporal`
    /// property, a `ProofKind::CleanTheorem` binding, a spec-variable clause
    /// place, or a `ProofObligation.spec` backref (v46).
    SpecCarrierRequiresV46,
    /// A v38 projection cannot represent the module's `Inst::Drop` (v47, the
    /// crystal lane's destructor instruction).
    DropInstRequiresV47,
    /// A v38 projection cannot represent a WEAK `Inst::CmpXchg` (v48, the
    /// crystal lane's D3 flag; tag 58).
    WeakCmpXchgRequiresV48,
    /// A v38 projection cannot represent an unwritten aggregate lane
    /// (`Constant::Uninit`, v49, the crystal lane's E3b).
    UninitLaneRequiresV49,
    /// A v38 projection cannot represent the module's constant-size uniform
    /// arrays: a `Constant::Splat` or an `Inst::ArraySplat` (v50).
    ArraySplatRequiresV50,
    /// A v38 projection cannot represent a member of the INST wire batch
    /// (v51): an `Inst::MakeAggregate`, `Inst::MemCopy` or `Inst::MemSet`, or
    /// a `BinOp::RotL` / `RotR` / `FCopySign` or `UnOp::CtLz` / `CtTz` /
    /// `BSwap` / `BitReverse` sub-op.
    InstWireBatchRequiresV51,
    /// A v38 projection cannot represent a KINDED `Inst::Assert` (plan item
    /// P, v52): an `AssertKind` other than `Unspecified`.
    AssertKindRequiresV52,
    /// A legacy projection cannot erase a normative call unwind boundary.
    CallUnwindBoundaryRequiresV53,
    /// A v38 projection cannot represent a panic site (amendment P, v54): a
    /// sited `Inst::Assert` or an `Inst::AssertInvoke`.
    PanicSiteRequiresV54,
    /// A v38 projection cannot represent executable drops (amendment D, v55):
    /// a drop-glue table row or an `Inst::DropInvoke`.
    DropGlueRequiresV55,
    /// A v38 projection cannot represent an `Inst::InvokeIndirect` (amendment
    /// D, Part 2, v56).
    UnwindTwinsRequiresV56,
    /// A v38 projection cannot represent a nominal type-origin key
    /// (`StructDef::origin` / `EnumDef::origin`) or a declared closure layout
    /// (`Module::closure_layouts`), both v58.
    NominalIdentityRequiresV58,
    /// A v38 projection cannot represent a typed effect summary
    /// (`FunctionSummary.effects`) or a world-epoch clause place
    /// (`ClausePlace::WorldPre` / `WorldPost`) — v59, roadmap WS1.14.
    EffectSummaryRequiresV59,
    /// A legacy projection cannot preserve typed callable ABI claims.
    SignatureAbiRequiresCurrentFormat,
    /// The typed descriptor exceeds the same resource limits used by its reader.
    SignatureAbiUnencodable {
        signature: usize,
        detail: String,
    },
    /// A v38 projection cannot represent a certificate binding
    /// (`CleanCicKernelRecheck.binding`, WS1.12a) or an evidenced license
    /// (body-gate tag 3, WS1.12(c)) — v61. A projection never narrows either
    /// to `None`.
    CertificateBindingRequiresV61,
    /// A v38 projection cannot represent a clause binding of the entry-state
    /// pointee place (`ClausePlace::ParamPointeeEntry`, v62, roadmap DG-63).
    ParamPointeePlaceRequiresV62,
    /// A v38 projection cannot represent runtime closure construction (v63).
    MakeClosureRequiresV63,
    StorageRequiresV64,
    /// A legacy projection cannot erase a declared closure's nominal source identity.
    ClosureOriginRequiresV66,
    /// A v38 projection cannot represent the tensor region (v67, PKG-U13a): a
    /// `Ty::Tensor` anywhere a type is spelled, or an `Inst::TensorContract`.
    TensorRequiresV67,
    /// A v38 projection cannot represent a tensor map, reduction or view
    /// (v68, PKG-U13c).
    TensorMapReduceViewRequiresV68,
    /// A v38 projection cannot represent a tensor gather or scatter (v69,
    /// PKG-U13d).
    TensorGatherScatterRequiresV69,
    /// A v38 projection cannot represent a content-addressed weight blob (v70,
    /// PKG-U13e): a `Constant::TensorBlob` or a blob table row. Heads the
    /// highest-wins chain.
    TensorBlobRequiresV70,
    /// NO binary version can represent a module completeness claim
    /// (`Module.completeness`, WS5.3b) yet: its carrier is a member of the
    /// next open wire batch and no number has been reserved for it. Every
    /// projection refuses such a module rather than dropping the claim (the
    /// infallible entry points panic with this text).
    CompletenessClaimUnencodable,
    /// NO binary version has a tag for this construct yet: an instruction
    /// ahead of its wire tag ([`Inst::binary_wire_gap`]; `site` names the
    /// node) or an enum variant the writer's tag table marks unencodable
    /// (`site` is `None`). Heads the writer's refusal precedence.
    ConstructAheadOfWireTag {
        construct: &'static str,
        site: Option<WireNodeSite>,
    },
    /// The producer-internal `Ty::Error` (a fail-closed typing placeholder)
    /// has no wire spelling at any version. JSON and MessagePack carry it;
    /// `validate_module` refuses it; the binary writer refuses it by this
    /// name (D1a).
    ProducerInternalType,
    /// Geometry cannot be represented by the Storage type at any target width.
    InvalidStorageGeometry(crate::StorageLayout),
    /// A count — a table, list, string or byte length — past the binary
    /// format's `u32` limit, which every reader refuses (`read_v32`:
    /// `VintOverflow`). `what` names the counted field as the writer spells
    /// it. Last in the writer's refusal precedence (D1a).
    CountExceedsFormat {
        what: &'static str,
        count: u64,
    },
    DuplicateOmission(ProofId),
    UnknownOmission(ProofId),
    AmbiguousOmission(ProofId),
    NonPendingOmission(ProofId),
    RetainedReference {
        obligation: ProofId,
        location: &'static str,
    },
}

/// Where a node the binary writer has no tag for sits: the function's id,
/// the block's id and the node's position in the block body.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct WireNodeSite {
    pub function: u32,
    pub block: u32,
    pub index: usize,
}

impl core::fmt::Display for BinaryProjectionError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Self::DialectTypeRequiresV39 => {
                f.write_str("nominal dialect types require a v39 binary projection")
            }
            Self::ContainerVtableRequiresV40 => {
                f.write_str("container-vtable fat pointers require a v40 binary projection")
            }
            Self::ContractSurfaceRequiresV41 => f.write_str(
                "codegen-license, typed-contract, cross-crate or linkage content requires a v41 \
                 binary projection",
            ),
            Self::TupleLayoutRequiresV42 => {
                f.write_str("declared tuple layouts require a v42 binary projection")
            }
            Self::HandleTypeRequiresV43 => {
                f.write_str("nominal opaque runtime handle types require a v43 binary projection")
            }
            Self::ImportSchemeRequiresV44 => f.write_str(
                "an import row recorded under a non-v2 identity scheme requires a v44 binary \
                 projection",
            ),
            Self::AbiSurfaceRequiresV45 => f.write_str(
                "function visibility/section/retention, per-argument ABI facts, a v45 calling \
                 convention or a 128-bit enum tag repr requires a v45 binary projection",
            ),
            Self::InlinedScopeChainUnencodable { function, scope } => write!(
                f,
                "{}",
                inlined_scope_chain_unencodable_message(*function, *scope as usize)
            ),
            Self::SpecCarrierRequiresV46 => f.write_str(
                "typed spec-carrier content (a variable sort, a typed invariant, a temporal \
                 property, a Clean-theorem proof binding, a spec-variable clause place or an \
                 obligation spec backref) requires a v46 binary projection",
            ),
            Self::DropInstRequiresV47 => f.write_str(
                "a destructor instruction (Inst::Drop) requires a v47 binary projection",
            ),
            Self::UninitLaneRequiresV49 => f.write_str(
                "an unwritten aggregate lane (Constant::Uninit) requires a v49 binary projection",
            ),
            Self::EffectSummaryRequiresV59 => f.write_str(
                "a typed effect summary (FunctionSummary.effects) or a world-epoch clause place \
                 (ClausePlace::WorldPre / WorldPost) requires a v59 binary projection",
            ),
            Self::CertificateBindingRequiresV61 => f.write_str(
                "a certificate binding (CleanCicKernelRecheck.binding) or an evidenced license \
                 (BodyGate::Gated { evidence }) requires a v61 binary projection",
            ),
            Self::WeakCmpXchgRequiresV48 => f.write_str(
                "a weak compare-exchange (Inst::CmpXchg { weak: true }) requires a v48 binary \
                 projection",
            ),
            Self::ArraySplatRequiresV50 => f.write_str(
                "a constant-size uniform array (Constant::Splat or Inst::ArraySplat) requires \
                 a v50 binary projection",
            ),
            Self::InstWireBatchRequiresV51 => f.write_str(
                "an INST wire batch member (Inst::MakeAggregate, Inst::MemCopy, Inst::MemSet, \
                 BinOp::RotL/RotR/FCopySign or UnOp::CtLz/CtTz/BSwap/BitReverse) requires a v51 \
                 binary projection",
            ),
            Self::SignatureAbiUnencodable { signature, detail } => {
                write!(f, "signature ABI {signature} is unencodable: {detail}")
            }
            Self::SignatureAbiRequiresCurrentFormat => f.write_str(
                "typed signature ABI claims require the current signature ABI binary format",
            ),
            Self::AssertKindRequiresV52 => f.write_str(
                "a kinded assert (Inst::Assert with an AssertKind other than Unspecified) \
                 requires a v52 binary projection",
            ),
            Self::CallUnwindBoundaryRequiresV53 => {
                f.write_str("a non-propagating call boundary requires a v53 binary projection")
            }
            Self::PanicSiteRequiresV54 => f.write_str(
                "a panic site (a sited Inst::Assert or an Inst::AssertInvoke) requires a v54 \
                 binary projection",
            ),
            Self::DropGlueRequiresV55 => f.write_str(
                "a drop-glue table row or an Inst::DropInvoke requires a v55 binary projection",
            ),
            Self::UnwindTwinsRequiresV56 => {
                f.write_str("an Inst::InvokeIndirect requires a v56 binary projection")
            }
            Self::NominalIdentityRequiresV58 => f.write_str(
                "a nominal type-origin key or a declared closure layout requires a v58 binary \
                 projection",
            ),
            Self::StorageRequiresV64 => f.write_str("storage-only layout requires wire v64"),
            Self::ClosureOriginRequiresV66 => {
                f.write_str("closure source identity requires wire v66")
            }
            Self::TensorBlobRequiresV70 => f.write_str(
                "a content-addressed weight blob (Constant::TensorBlob or a blob table row) \
                 requires a v70 binary projection",
            ),
            Self::TensorGatherScatterRequiresV69 => f.write_str(
                "a tensor gather or scatter (Inst::TensorGather, Inst::TensorScatter) requires \
                 a v69 binary projection",
            ),
            Self::TensorMapReduceViewRequiresV68 => f.write_str(
                "a tensor map, reduction or view (Inst::TensorMap, Inst::TensorReduce, \
                 Inst::TensorView) requires a v68 binary projection",
            ),
            Self::TensorRequiresV67 => f.write_str(
                "a tensor type (Ty::Tensor) or a tensor contraction (Inst::TensorContract) \
                 requires a v67 binary projection",
            ),
            Self::MakeClosureRequiresV63 => {
                f.write_str("an Inst::MakeClosure requires a v63 binary projection")
            }
            Self::ParamPointeePlaceRequiresV62 => f.write_str(
                "a clause binding of the entry-state pointee place \
                 (ClausePlace::ParamPointeeEntry) requires a v62 binary projection",
            ),
            Self::CompletenessClaimUnencodable => {
                f.write_str(COMPLETENESS_CLAIM_UNENCODABLE_MESSAGE)
            }
            Self::ConstructAheadOfWireTag { construct, site } => {
                f.write_str(&no_wire_tag_message(construct, site.as_ref()))
            }
            Self::ProducerInternalType => f.write_str(PRODUCER_INTERNAL_TYPE_UNENCODABLE_MESSAGE),
            Self::InvalidStorageGeometry(layout) => write!(
                f,
                "invalid storage geometry: size {}, alignment {}",
                layout.size_bytes, layout.align_bytes
            ),
            Self::CountExceedsFormat { what, count } => {
                f.write_str(&count_exceeds_format_message(what, *count))
            }
            Self::DuplicateOmission(id) => {
                write!(f, "proof obligation {} was requested twice", id.index())
            }
            Self::UnknownOmission(id) => {
                write!(f, "proof obligation {} does not exist", id.index())
            }
            Self::AmbiguousOmission(id) => write!(
                f,
                "proof obligation {} is not a unique table row",
                id.index()
            ),
            Self::NonPendingOmission(id) => write!(
                f,
                "proof obligation {} is not pending and cannot be omitted",
                id.index()
            ),
            Self::RetainedReference {
                obligation,
                location,
            } => write!(
                f,
                "cannot omit proof obligation {} referenced by retained {location}",
                obligation.index()
            ),
        }
    }
}

impl std::error::Error for BinaryProjectionError {}

struct ModuleWireView {
    module_name: Option<String>,
    function_order: Vec<usize>,
    function_names: Option<Vec<String>>,
    global_names: Option<Vec<String>>,
    // `None` in the outer option means raw-body mode. `None` per function in
    // canonical mode is the allocation-free identity fast path; a full plan
    // is retained only for functions that actually need rewriting or whose
    // legacy behavior cannot be proven identical cheaply.
    canonical_functions: Option<Vec<Option<FunctionCanonicalPlan>>>,
    obligation_rows: Vec<usize>,
    proof_sidecars: ModuleProofSidecars,
    // Canonical materialization normally drops provenance when it rewrites a
    // body. An identity-only projection does not mutate the source module, so
    // executable-content v1 retains this independently observed field.
    retain_source_provenance: bool,
    // Whether `Function.body_gate` / `Function.display_path` reach the wire.
    // Every public `ModuleBinaryOptions` projection is faithful (`Exact`);
    // only the executable-content identity omits them, because a codegen
    // license is a verdict ABOUT that image and must not move it.
    codegen_license: ModuleCodegenLicense,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ModuleProofSidecars {
    Exact,
    Omit,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ModuleCodegenLicense {
    Exact,
    Omit,
}

impl ModuleWireView {
    fn try_new(
        module: &Module,
        options: ModuleBinaryOptions<'_>,
    ) -> Result<Self, BinaryProjectionError> {
        let (module_name, function_order, function_names, global_names) = match options.symbols {
            ModuleSymbolProjection::Exact => {
                (None, (0..module.functions.len()).collect(), None, None)
            }
            ModuleSymbolProjection::StableIdOrdinalNames {
                module_name,
                function_prefix,
                global_prefix,
            } => {
                let mut function_order: Vec<usize> = (0..module.functions.len()).collect();
                function_order.sort_by_key(|&index| module.functions[index].id.index());
                let function_names = module
                    .functions
                    .iter()
                    .map(|function| format!("{function_prefix}{}", function.id.index()))
                    .collect();
                let global_names = (0..module.globals.len())
                    .map(|index| format!("{global_prefix}{index}"))
                    .collect();
                (
                    Some(module_name.to_owned()),
                    function_order,
                    Some(function_names),
                    Some(global_names),
                )
            }
        };
        let canonical_functions = match options.body {
            ModuleBinaryBody::Raw | ModuleBinaryBody::RawV38 => None,
            ModuleBinaryBody::Canonical | ModuleBinaryBody::CanonicalV38 => Some(
                module
                    .functions
                    .iter()
                    .map(FunctionCanonicalPlan::new_if_needed)
                    .collect(),
            ),
        };

        let obligation_rows =
            projected_obligation_rows(module, options.obligations, canonical_functions.as_deref())?;
        Ok(Self {
            module_name,
            function_order,
            function_names,
            global_names,
            canonical_functions,
            obligation_rows,
            proof_sidecars: ModuleProofSidecars::Exact,
            retain_source_provenance: false,
            codegen_license: ModuleCodegenLicense::Exact,
        })
    }

    /// The v1 executable-content identity projection.
    ///
    /// This deliberately bypasses `ModuleObligationRows::OmitIds`: the whole
    /// module-level proof sidecar is absent from this identity, while retained
    /// on-IR `ProofRef` annotations remain part of the function bodies. A
    /// projected image can therefore contain references without their proof
    /// rows and is an identity preimage only, never a standalone module.
    ///
    /// The codegen license (`Function.body_gate`, `Function.display_path`) is
    /// likewise projected away: the string collector neither raises the
    /// version for it nor pools its strings, and the writer emits gate tag 0
    /// with an absent path whenever some OTHER v41 feature keeps the image at
    /// v41. So a module whose only v41 feature is the license projects to the
    /// exact pre-v41 bytes of the same module unlicensed. The two walks are
    /// handed the SAME `include_codegen_license` flag, and if the writer ever
    /// spelled a license string the collector skipped, the sealed table has
    /// no id for it and `SealedStringPool::id_of` refuses by name. The
    /// converse — a collector that raises or pools where the writer does not
    /// — is invisible to the sealed table; the byte equality claimed above is
    /// what pins it, asserted by
    /// `executable_content_projection_strips_the_codegen_license`.
    fn executable_content_v1(module: &Module) -> Self {
        Self {
            module_name: None,
            function_order: (0..module.functions.len()).collect(),
            function_names: None,
            global_names: None,
            canonical_functions: Some(
                module
                    .functions
                    .iter()
                    .map(FunctionCanonicalPlan::new_if_needed)
                    .collect(),
            ),
            obligation_rows: Vec::new(),
            proof_sidecars: ModuleProofSidecars::Omit,
            retain_source_provenance: true,
            codegen_license: ModuleCodegenLicense::Omit,
        }
    }

    fn module_name<'a, X: WireExt>(&'a self, module: &'a ModuleG<X>) -> &'a str {
        self.module_name.as_deref().unwrap_or(&module.name)
    }

    fn function_name<'a, X: WireExt>(
        &'a self,
        function: &'a FunctionG<X>,
        index: usize,
    ) -> &'a str {
        self.function_names
            .as_ref()
            .map_or(&function.name, |names| &names[index])
    }

    fn global_name<'a, X: WireExt>(&'a self, global: &'a GlobalG<X>, index: usize) -> &'a str {
        self.global_names
            .as_ref()
            .map_or(&global.name, |names| &names[index])
    }

    fn canonical_function(&self, index: usize) -> Option<&FunctionCanonicalPlan> {
        self.canonical_functions
            .as_ref()
            .and_then(|functions| functions[index].as_ref())
    }

    fn includes_proof_sidecars(&self) -> bool {
        self.proof_sidecars == ModuleProofSidecars::Exact
    }

    fn includes_codegen_license(&self) -> bool {
        self.codegen_license == ModuleCodegenLicense::Exact
    }
}

fn projected_obligation_rows(
    module: &Module,
    rows: ModuleObligationRows<'_>,
    canonical_functions: Option<&[Option<FunctionCanonicalPlan>]>,
) -> Result<Vec<usize>, BinaryProjectionError> {
    let ModuleObligationRows::OmitIds(requested) = rows else {
        return Ok((0..module.proof_obligations.len()).collect());
    };

    #[derive(Default)]
    struct OmissionMatch {
        count: usize,
        only_status: Option<ProofStatus>,
        request_was_validated: bool,
    }

    // Index the requested IDs once, then scan the obligation table once. The
    // validation loop below remains in request order so Unknown/Ambiguous/
    // NonPending/Duplicate error precedence matches the former nested scan.
    let mut omitted = HashMap::<ProofId, OmissionMatch>::with_capacity(requested.len());
    for &id in requested {
        omitted.entry(id).or_default();
    }
    for row in &module.proof_obligations {
        if let Some(summary) = omitted.get_mut(&row.id) {
            summary.count += 1;
            if summary.count == 1 {
                summary.only_status = Some(row.status);
            }
        }
    }
    for &id in requested {
        let summary = omitted
            .get_mut(&id)
            .expect("every requested omission must have an index entry");
        if summary.request_was_validated {
            return Err(BinaryProjectionError::DuplicateOmission(id));
        }
        summary.request_was_validated = true;
        match summary.count {
            0 => return Err(BinaryProjectionError::UnknownOmission(id)),
            1 => {
                if summary.only_status != Some(ProofStatus::Pending) {
                    return Err(BinaryProjectionError::NonPendingOmission(id));
                }
            }
            _ => return Err(BinaryProjectionError::AmbiguousOmission(id)),
        }
    }
    if omitted.is_empty() {
        return Ok((0..module.proof_obligations.len()).collect());
    }
    let first_omitted = requested
        .iter()
        .copied()
        .min()
        .expect("a non-empty omission index has a requested ID");
    validate_omitted_obligation_references(module, &omitted, first_omitted, canonical_functions)?;
    Ok(module
        .proof_obligations
        .iter()
        .enumerate()
        .filter_map(|(index, row)| (!omitted.contains_key(&row.id)).then_some(index))
        .collect())
}

fn validate_omitted_obligation_references<V>(
    module: &Module,
    omitted: &HashMap<ProofId, V>,
    first_omitted: ProofId,
    canonical_functions: Option<&[Option<FunctionCanonicalPlan>]>,
) -> Result<(), BinaryProjectionError> {
    let retained = |id: ProofId, location| {
        if omitted.contains_key(&id) {
            Err(BinaryProjectionError::RetainedReference {
                obligation: id,
                location,
            })
        } else {
            Ok(())
        }
    };
    for (function_index, function) in module.functions.iter().enumerate() {
        let provenance_is_retained = function.source_provenance.is_some()
            && canonical_functions.is_none_or(|plans| {
                plans[function_index]
                    .as_ref()
                    .is_none_or(|plan| plan.preserve_source_provenance)
            });
        if provenance_is_retained {
            retained(first_omitted, "source-provenance carrier")?;
        }
        for annotation in &function.proofs {
            if let Some(id) = annotation.backing_obligation() {
                retained(id, "function proof annotation")?;
            }
        }
        // v61: a license's evidence cites an obligation by id; omitting that
        // row would leave the projected license citing nothing.
        if let Some(evidence) = function
            .body_gate
            .as_ref()
            .and_then(crate::BodyGate::evidence)
        {
            retained(evidence.obligation, "codegen license evidence")?;
        }
        for block in &function.blocks {
            for node in &block.body {
                for annotation in &node.proofs {
                    if let Some(id) = annotation.backing_obligation() {
                        retained(id, "instruction proof annotation")?;
                    }
                }
                if let Some(context) = &node.proof_context {
                    for &id in &context.assumes {
                        retained(id, "proof-context assumption")?;
                    }
                    for &id in &context.establishes {
                        retained(id, "proof-context establishment")?;
                    }
                }
            }
        }
    }
    for certificate in &module.proof_certificates {
        retained(certificate.obligation, "proof certificate")?;
        if let ProofEvidence::InheritedFromCallee { obligation, .. } = &certificate.evidence {
            retained(*obligation, "inherited proof evidence")?;
        }
    }
    for diagnostic in &module.obligation_diagnostics {
        retained(diagnostic.obligation, "obligation diagnostic")?;
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// Writer helpers
// ---------------------------------------------------------------------------

/// Internal destination for the binary encoder.
///
/// Keeping the wire walk independent of `Vec<u8>` lets callers count or hash
/// the exact encoding without first materializing a second whole-module byte
/// buffer. The sink is deliberately infallible here: adapters for fallible
/// writers retain the first error and report it after the shared wire walk.
///
/// **The writer's refusal rule, stated once (D1a).** A construct with no wire
/// image is refused by the writer's OWN arm, through [`Self::refuse`]; a count
/// past the format's `u32` is reported by [`write_count`], through
/// [`Self::note_over_limit`]. Each arm then CONTINUES and writes nothing for
/// that construct, so a recording sink sees every refusal of the walk. What
/// a refusal MEANS is the sink's role:
///
/// * a BLOB sink ([`BlobSink`] behind `serialize_module` / `to_vec`, and
///   [`IoSink`] behind `write_to`) RECORDS both, and its entry returns the
///   refusal instead of the image. The materializing entries run the check
///   walk first, so a refused image is never allocated; `write_to` streams
///   in one pass and reports the record at the end (its partial output is
///   discarded on `Err`). No blob path panics (D1b);
/// * an IDENTITY sink (the SHA-256 sinks, [`CountingSink`],
///   [`CallbackSink`]) panics on a construct and ignores a count, so module
///   identity is total over counts and the count's `write_v64` spelling
///   keeps it injective past the limit;
/// * the CHECK sink ([`CheckSink`]) records them, reads no payload, and is
///   the one pre-check every entry point runs
///   ([`Module::wire_image_refusal`]).
///
/// Neither hook has a default body: every sink states its role, and a
/// forwarding sink (`&mut S`, [`BufferedBinarySink`]) forwards — a default
/// would let a forwarder silently drop a refusal.
trait BinarySink {
    fn append_bytes(&mut self, bytes: &[u8]);

    /// The writer met a construct with no wire image.
    fn refuse(&mut self, refusal: WireRefusal);

    /// The writer spelled a count past the format's `u32` limit.
    fn note_over_limit(&mut self, what: &'static str, count: u64);

    fn push(&mut self, byte: u8) {
        self.append_bytes(core::slice::from_ref(&byte));
    }

    fn extend_from_slice(&mut self, bytes: &[u8]) {
        self.append_bytes(bytes);
    }
}

/// A raw byte buffer: the sink of the non-module serializers (a lineage
/// manifest, a template, the bundle header) and of tests, where both hooks
/// panic. No module blob entry writes through it: they write through a
/// recording [`BlobSink`].
impl BinarySink for Vec<u8> {
    fn append_bytes(&mut self, bytes: &[u8]) {
        Vec::extend_from_slice(self, bytes);
    }

    fn refuse(&mut self, refusal: WireRefusal) {
        refusal.panic_unencodable()
    }

    fn note_over_limit(&mut self, what: &'static str, count: u64) {
        panic!("{}", count_exceeds_format_message(what, count))
    }
}

impl<S: BinarySink + ?Sized> BinarySink for &mut S {
    fn append_bytes(&mut self, bytes: &[u8]) {
        (**self).append_bytes(bytes);
    }

    fn refuse(&mut self, refusal: WireRefusal) {
        (**self).refuse(refusal);
    }

    fn note_over_limit(&mut self, what: &'static str, count: u64) {
        (**self).note_over_limit(what, count);
    }
}

/// Fixed scratch used to coalesce scalar wire writes for streaming consumers.
/// Large byte/string payloads bypass it after any pending prefix is flushed.
const BINARY_STREAM_BUFFER_BYTES: usize = 4 * 1024;

struct BufferedBinarySink<S, const CAPACITY: usize> {
    inner: S,
    bytes: [u8; CAPACITY],
    len: usize,
}

impl<S: BinarySink, const CAPACITY: usize> BufferedBinarySink<S, CAPACITY> {
    fn new(inner: S) -> Self {
        assert!(CAPACITY > 0, "binary sink buffer must not be empty");
        Self {
            inner,
            bytes: [0; CAPACITY],
            len: 0,
        }
    }

    fn flush(&mut self) {
        if self.len != 0 {
            self.inner.append_bytes(&self.bytes[..self.len]);
            self.len = 0;
        }
    }

    fn finish(&mut self) {
        self.flush();
    }
}

impl<S: BinarySink, const CAPACITY: usize> BinarySink for BufferedBinarySink<S, CAPACITY> {
    fn append_bytes(&mut self, bytes: &[u8]) {
        if bytes.len() >= CAPACITY {
            self.flush();
            self.inner.append_bytes(bytes);
            return;
        }
        if bytes.len() > CAPACITY - self.len {
            self.flush();
        }
        let end = self.len + bytes.len();
        self.bytes[self.len..end].copy_from_slice(bytes);
        self.len = end;
    }

    // A refusal writes no bytes, so it needs no flush to keep its order.
    fn refuse(&mut self, refusal: WireRefusal) {
        self.inner.refuse(refusal);
    }

    fn note_over_limit(&mut self, what: &'static str, count: u64) {
        self.inner.note_over_limit(what, count);
    }
}

struct Sha256UpdateSink<'a>(&'a mut Sha256);

/// An IDENTITY sink (see [`BinarySink`]).
impl BinarySink for Sha256UpdateSink<'_> {
    fn append_bytes(&mut self, bytes: &[u8]) {
        self.0.update(bytes);
    }

    fn refuse(&mut self, refusal: WireRefusal) {
        refusal.panic_unencodable()
    }

    fn note_over_limit(&mut self, _what: &'static str, _count: u64) {}
}

#[derive(Default)]
struct CountingSink {
    len: usize,
}

/// An IDENTITY sink (see [`BinarySink`]): `encoded_len` and the
/// length-prefixed digests count with it.
impl BinarySink for CountingSink {
    fn append_bytes(&mut self, bytes: &[u8]) {
        self.len = self
            .len
            .checked_add(bytes.len())
            .expect("encoded module length must fit usize");
    }

    fn refuse(&mut self, refusal: WireRefusal) {
        refusal.panic_unencodable()
    }

    fn note_over_limit(&mut self, _what: &'static str, _count: u64) {}
}

struct CallbackSink<'a, F>(&'a mut F);

impl<F> BinarySink for CallbackSink<'_, F>
where
    F: FnMut(&[u8]),
{
    fn append_bytes(&mut self, bytes: &[u8]) {
        (self.0)(bytes);
    }

    /// An IDENTITY sink: `for_each_chunk` streams the executable-content
    /// digest. An over-limit image streams; every reader refuses it.
    fn refuse(&mut self, refusal: WireRefusal) {
        refusal.panic_unencodable()
    }

    fn note_over_limit(&mut self, _what: &'static str, _count: u64) {}
}

/// A BLOB sink over an arbitrary writer (`write_to`): it records a refusal
/// instead of panicking, like [`BlobSink`], and keeps the writer's first I/O
/// error.
struct IoSink<'a, W: ?Sized> {
    writer: &'a mut W,
    error: Option<io::Error>,
    refusals: CheckSink,
}

impl<'a, W: IoWrite + ?Sized> IoSink<'a, W> {
    fn new(writer: &'a mut W) -> Self {
        Self {
            writer,
            error: None,
            refusals: CheckSink::default(),
        }
    }

    /// The writer's first I/O error, else a recorded refusal as
    /// `InvalidData` carrying the [`BinaryProjectionError`].
    fn finish(self) -> io::Result<()> {
        if let Some(error) = self.error {
            return Err(error);
        }
        self.refusals
            .into_result()
            .map(|_| ())
            .map_err(|refusal| io::Error::new(io::ErrorKind::InvalidData, refusal))
    }
}

impl<W: IoWrite + ?Sized> BinarySink for IoSink<'_, W> {
    fn append_bytes(&mut self, bytes: &[u8]) {
        if self.error.is_none()
            && let Err(error) = self.writer.write_all(bytes)
        {
            self.error = Some(error);
        }
    }

    fn refuse(&mut self, refusal: WireRefusal) {
        self.refusals.refuse(refusal);
    }

    fn note_over_limit(&mut self, what: &'static str, count: u64) {
        self.refusals.note_over_limit(what, count);
    }
}

/// The BLOB sink behind `serialize_module` and the plans' `to_vec`: the
/// image's bytes, and a [`CheckSink`] that records (never panics on) a
/// refusal, so the entry returns the refusal instead of the image.
struct BlobSink {
    bytes: Vec<u8>,
    refusals: CheckSink,
}

impl BlobSink {
    fn with_capacity(capacity: usize) -> Self {
        Self {
            bytes: Vec::with_capacity(capacity),
            refusals: CheckSink::default(),
        }
    }

    /// The image, or the first recorded refusal by precedence.
    fn finish(self) -> Result<Vec<u8>, BinaryProjectionError> {
        self.refusals.into_result()?;
        Ok(self.bytes)
    }
}

impl BinarySink for BlobSink {
    fn append_bytes(&mut self, bytes: &[u8]) {
        self.bytes.extend_from_slice(bytes);
    }

    fn refuse(&mut self, refusal: WireRefusal) {
        self.refusals.refuse(refusal);
    }

    fn note_over_limit(&mut self, what: &'static str, count: u64) {
        self.refusals.note_over_limit(what, count);
    }
}

/// The writer's refusal precedence, which consumers pin (trust's
/// `native_request_metadata_tests`, ty's wire-identity tests): an
/// instruction or variant ahead of its wire tag, then a lexical-scope
/// inlining chain link, then a completeness claim, then a typed signature
/// ABI past its encoding limits, then `Ty::Error`, then a count. Lower rank
/// wins. A newly refused class is ranked after every class a pre-check
/// already reported, so it never displaces a verdict a consumer pinned. (A
/// certificate binding ranked between the completeness claim and the
/// signature ABI until wire v61 gave it a carrier; retiring the class moves
/// no other class's relative order.)
const WIRE_REFUSAL_RANKS: usize = 7;
const COUNT_REFUSAL_RANK: usize = 5;

/// A construct the binary writer has no wire image for, as its own arm
/// reports it to [`BinarySink::refuse`].
#[derive(Debug, Clone, PartialEq, Eq)]
enum WireRefusal {
    /// An instruction ahead of its wire tag (`site` is the node), or a
    /// variant a `tag_enum!` table marks unencodable (`site` is `None`).
    NoWireTag {
        construct: &'static str,
        site: Option<WireNodeSite>,
    },
    /// A lexical scope's inlining chain link (WS4.19). `scope` is the
    /// position in the function's scope table, untruncated.
    InlinedScopeChain {
        function: u32,
        scope: usize,
    },
    /// A module completeness claim (WS5.3b).
    CompletenessClaim,
    /// A typed signature ABI (wire v60) past the encoding limits its reader
    /// enforces (`SignatureAbi::validate_encoding_limits`). `signature` is
    /// its row in `Module.func_types`, used or not.
    SignatureAbi {
        signature: usize,
        detail: String,
    },
    /// The producer-internal `Ty::Error`.
    ProducerInternalType,
    InvalidStorageGeometry(crate::StorageLayout),
}

impl WireRefusal {
    /// The refusal as the fallible entry points report it, with its rank.
    /// One match states both, so the two cannot disagree.
    fn ranked(self) -> (usize, BinaryProjectionError) {
        match self {
            Self::NoWireTag { construct, site } => (
                0,
                BinaryProjectionError::ConstructAheadOfWireTag { construct, site },
            ),
            Self::InlinedScopeChain { function, scope } => {
                match crate::value::table_index(scope, "lexical scope") {
                    Ok(scope) => (
                        1,
                        BinaryProjectionError::InlinedScopeChainUnencodable { function, scope },
                    ),
                    // A link past `u32::MAX` sits in a scope table whose
                    // count is itself past the format's limit; that count is
                    // the refusal the public error can name.
                    Err(_) => (
                        COUNT_REFUSAL_RANK,
                        BinaryProjectionError::CountExceedsFormat {
                            what: "Function.scopes",
                            count: scope as u64,
                        },
                    ),
                }
            }
            Self::CompletenessClaim => (2, BinaryProjectionError::CompletenessClaimUnencodable),
            Self::SignatureAbi { signature, detail } => (
                3,
                BinaryProjectionError::SignatureAbiUnencodable { signature, detail },
            ),
            Self::ProducerInternalType => (4, BinaryProjectionError::ProducerInternalType),
            Self::InvalidStorageGeometry(layout) => {
                (6, BinaryProjectionError::InvalidStorageGeometry(layout))
            }
        }
    }

    /// The text an infallible (identity or blob) sink panics with: the same
    /// text each arm panicked with before D1a, so no consumer reading a panic
    /// payload sees a change.
    fn message(&self) -> String {
        match self {
            Self::NoWireTag { construct, site } => no_wire_tag_message(construct, site.as_ref()),
            Self::InlinedScopeChain { function, scope } => {
                inlined_scope_chain_unencodable_message(*function, *scope)
            }
            Self::CompletenessClaim => COMPLETENESS_CLAIM_UNENCODABLE_MESSAGE.to_owned(),
            Self::SignatureAbi { .. } => self.clone().ranked().1.to_string(),
            Self::ProducerInternalType => PRODUCER_INTERNAL_TYPE_UNENCODABLE_MESSAGE.to_owned(),
            Self::InvalidStorageGeometry(..) => self.clone().ranked().1.to_string(),
        }
    }

    /// An infallible sink's answer to a refusal: the module has no image.
    fn panic_unencodable(&self) -> ! {
        panic!("{}", self.message())
    }
}

/// The CHECK sink: the writer run as the one pre-check. It reads no payload
/// (it counts a byte slice's length and nothing else), hashes nothing, and
/// keeps the FIRST refusal of each precedence rank. The count is the image's
/// exact length, so a blob entry allocates once.
#[derive(Default)]
struct CheckSink {
    first: [Option<BinaryProjectionError>; WIRE_REFUSAL_RANKS],
    len: usize,
}

impl CheckSink {
    fn record(&mut self, rank: usize, refusal: BinaryProjectionError) {
        if let Some(slot) = self.first.get_mut(rank)
            && slot.is_none()
        {
            *slot = Some(refusal);
        }
    }

    /// The highest-precedence refusal, else the image's exact length (a
    /// length past `usize` saturates: it is only an allocation hint, and the
    /// allocation then fails as any oversized one does).
    fn into_result(self) -> Result<usize, BinaryProjectionError> {
        match self.first.into_iter().flatten().next() {
            Some(refusal) => Err(refusal),
            None => Ok(self.len),
        }
    }
}

impl BinarySink for CheckSink {
    fn append_bytes(&mut self, bytes: &[u8]) {
        self.len = self.len.saturating_add(bytes.len());
    }

    fn refuse(&mut self, refusal: WireRefusal) {
        let (rank, refusal) = refusal.ranked();
        self.record(rank, refusal);
    }

    fn note_over_limit(&mut self, what: &'static str, count: u64) {
        self.record(
            COUNT_REFUSAL_RANK,
            BinaryProjectionError::CountExceedsFormat { what, count },
        );
    }
}

/// Every refusal class the binary writer meets in `module`'s exact (raw,
/// full) encoding, the first of each, in precedence order: the writer over a
/// [`CheckSink`]. [`Module::wire_image_refusal`] is its first element.
pub(crate) fn wire_image_refusals(module: &Module) -> Vec<BinaryProjectionError> {
    let pool = collect_strings(module);
    let mut sink = CheckSink::default();
    write_module_with_pool(module, None, &pool, &mut sink);
    sink.first.into_iter().flatten().collect()
}

fn write_u8(buf: &mut impl BinarySink, v: u8) {
    buf.push(v);
}

fn write_bool(buf: &mut impl BinarySink, v: bool) {
    buf.push(if v { 1 } else { 0 });
}

fn write_u32(buf: &mut impl BinarySink, v: u32) {
    buf.extend_from_slice(&v.to_le_bytes());
}

fn write_u64(buf: &mut impl BinarySink, v: u64) {
    buf.extend_from_slice(&v.to_le_bytes());
}

fn write_v64(buf: &mut impl BinarySink, mut v: u64) {
    while v >= 0x80 {
        buf.push((v as u8) | 0x80);
        v >>= 7;
    }
    buf.push(v as u8);
}

/// Spell a count (a table, list, string or byte length): THE statement of the
/// format's count limit (D1a). The count is written as the `write_v64` varint
/// of its exact value — byte-identical to the historical `write_v32` spelling
/// for every count up to `u32::MAX`, and still injective above it, so module
/// identity never aliases two lengths — and a count past `u32::MAX`, which
/// every reader refuses (`read_v32`: `VintOverflow`), is reported to the
/// sink ([`BinarySink::note_over_limit`]) before it is spelled. `what` names
/// the counted field in the refusal.
fn write_count(buf: &mut impl BinarySink, what: &'static str, count: usize) {
    // `usize` is at most 64 bits on every target Rust supports, so this
    // widening cast is exact.
    let count = count as u64;
    if count > u64::from(u32::MAX) {
        buf.note_over_limit(what, count);
    }
    write_v64(buf, count);
}

fn write_i128(buf: &mut impl BinarySink, v: i128) {
    buf.extend_from_slice(&v.to_le_bytes());
}

fn write_u128(buf: &mut impl BinarySink, v: u128) {
    buf.extend_from_slice(&v.to_le_bytes());
}

fn write_v32(buf: &mut impl BinarySink, v: u32) {
    write_v64(buf, v as u64);
}

fn write_value_id(buf: &mut impl BinarySink, id: ValueId) {
    write_v32(buf, id.index());
}

fn write_block_id(buf: &mut impl BinarySink, id: BlockId) {
    write_v32(buf, id.index());
}

fn write_ty_id(buf: &mut impl BinarySink, id: TyId) {
    write_v32(buf, id.index());
}

fn write_func_id(buf: &mut impl BinarySink, id: FuncId) {
    write_v32(buf, id.index());
}

fn write_func_ty_id(buf: &mut impl BinarySink, id: FuncTyId) {
    write_v32(buf, id.index());
}

fn write_closure_ty_id(buf: &mut impl BinarySink, id: ClosureTyId) {
    write_v32(buf, id.index());
}

fn write_struct_id(buf: &mut impl BinarySink, id: StructId) {
    write_v32(buf, id.index());
}

fn write_enum_id(buf: &mut impl BinarySink, id: EnumId) {
    write_v32(buf, id.index());
}

fn write_record_id(buf: &mut impl BinarySink, id: RecordId) {
    write_v32(buf, id.index());
}

fn write_proof_id(buf: &mut impl BinarySink, id: ProofId) {
    write_v32(buf, id.index());
}

fn write_f64(buf: &mut impl BinarySink, v: f64) {
    buf.extend_from_slice(&v.to_le_bytes());
}

fn write_raw_str(buf: &mut impl BinarySink, s: &str) {
    write_count(buf, "string length", s.len());
    buf.extend_from_slice(s.as_bytes());
}

/// Spell `s` as its index in the already-emitted string table. The pool is
/// sealed, so this can only look an id up — and `id_of` refuses, by name, a
/// string the collection walk did not intern.
fn write_str(buf: &mut impl BinarySink, pool: &SealedStringPool, s: &str) {
    // `write_v64` of a pool id is the `write_v32` spelling for every id the
    // format can carry; an id past `u32::MAX` needs a string table past the
    // format's count, which `write_count` reports.
    write_v64(buf, pool.id_of(s));
}

fn write_bytes(buf: &mut impl BinarySink, data: &[u8]) {
    write_count(buf, "byte string", data.len());
    buf.extend_from_slice(data);
}

fn write_opt_u64(buf: &mut impl BinarySink, v: Option<u64>) {
    match v {
        None => write_u8(buf, 0),
        Some(val) => {
            write_u8(buf, 1);
            write_v64(buf, val);
        }
    }
}

fn write_opt_v32(buf: &mut impl BinarySink, v: Option<u32>) {
    match v {
        None => write_u8(buf, 0),
        Some(val) => {
            write_u8(buf, 1);
            write_v32(buf, val);
        }
    }
}

fn write_opt_str(buf: &mut impl BinarySink, pool: &SealedStringPool, v: Option<&str>) {
    match v {
        None => write_u8(buf, 0),
        Some(s) => {
            write_u8(buf, 1);
            write_str(buf, pool, s);
        }
    }
}

/// v58: a nominal identity key selects v58 and pools the Clean declaration
/// name. Absent keys leave both the version and the pool untouched, which is
/// what keeps an unkeyed module's bytes identical to its pre-v58 encoding.
fn collect_type_origin_strings(origin: Option<&TypeOrigin>, pool: &mut StringPoolBuilder) {
    let Some(origin) = origin else {
        return;
    };
    pool.raise_to(NOMINAL_IDENTITY_FORMAT_VERSION);
    if let TypeOrigin::Clean { decl, .. } = origin {
        pool.intern(decl);
    }
}

/// Walk `module` once, filling the string table and settling the header
/// version, and hand back the SEALED table the write walk indexes. The write
/// walk cannot add to what this returns, so every string it spells is one
/// this walk interned.
fn collect_strings(module: &Module) -> SealedStringPool {
    collect_strings_with_view(module, None)
}

fn collect_strings_with_view(module: &Module, view: Option<&ModuleWireView>) -> SealedStringPool {
    collect_strings_into(module, view, StringPoolBuilder::new())
}

fn collect_strings_into<X: WireExt>(
    module: &ModuleG<X>,
    view: Option<&ModuleWireView>,
    mut pool: StringPoolBuilder,
) -> SealedStringPool {
    if !module.closure_layouts.is_empty() {
        pool.raise_to(NOMINAL_IDENTITY_FORMAT_VERSION);
        for descriptor in &module.closure_layouts {
            if descriptor.origin.is_some() {
                pool.raise_to(CLOSURE_ORIGIN_FORMAT_VERSION);
                collect_type_origin_strings(descriptor.origin.as_ref(), &mut pool);
            }
        }
    }
    if !module.tuple_layouts.is_empty() {
        pool.raise_to(TUPLE_LAYOUT_FORMAT_VERSION);
    }
    // v55 (amendment D): a module with a drop-glue row writes the trailing
    // section; each key is an inline type whose strings the sealed pool must
    // hold (and which may itself raise the header, e.g. a handle key).
    if !module.drop_glue.is_empty() {
        pool.raise_to(DROP_GLUE_FORMAT_VERSION);
        for entry in &module.drop_glue {
            collect_type_identity_strings(&entry.ty, &mut pool);
        }
    }
    // v70: a module with a blob table row writes the trailing section.
    if !module.blobs.is_empty() {
        pool.raise_to(TENSOR_BLOB_FORMAT_VERSION);
    }
    // The v30 universe / predicate tables carry constants too (scalar-only
    // when well-formed). Walk them like every other constant carrier, so a
    // gated constant tag (v49 `Uninit`, v50 `Splat`) can never be written under a header
    // that refuses it, even for a module the validator would reject.
    for universe in &module.universes {
        if let crate::pred::Universe::Members(items) = universe {
            for item in items {
                collect_constant_strings(item, &mut pool);
            }
        }
    }
    for pred in &module.predicates {
        if let crate::pred::Pred::FiniteSet(items) = pred {
            for item in items {
                collect_constant_strings(item, &mut pool);
            }
        }
    }
    let include_proof_sidecars = view.is_none_or(ModuleWireView::includes_proof_sidecars);
    pool.intern(view.map_or(&module.name, |view| view.module_name(module)));
    for ty in &module.types {
        collect_type_strings(ty, &mut pool);
    }
    for signature in &module.func_types {
        if signature.abi.is_some() {
            pool.raise_to(SIGNATURE_ABI_FORMAT_VERSION);
        }
        for ty in signature.params.iter().chain(&signature.returns) {
            collect_type_strings(ty, &mut pool);
        }
    }
    for closure in &module.closure_types {
        for ty in &closure.captures {
            collect_type_strings(ty, &mut pool);
        }
    }

    if let Some(ti) = &module.target_info {
        pool.intern(&ti.triple);
        // Stable ABI identifier (VERSION >= 20).
        if let Some(abi) = &ti.abi {
            pool.intern(abi);
        }
    }

    // Debug-info source-file table paths (VERSION >= 9). Under the v3
    // identity projection each path is spelled `""` (length kept).
    for path in &module.files {
        let spelled = pool.debug_file(path);
        pool.intern(spelled);
    }

    // Obligation-diagnostic strings (VERSION >= 11).
    if include_proof_sidecars {
        for d in &module.obligation_diagnostics {
            pool.intern(&d.message);
            if let Some(detail) = &d.detail {
                pool.intern(detail);
            }
        }
    }

    for sd in &module.structs {
        pool.intern(&sd.name);
        for fd in &sd.fields {
            pool.intern(&fd.name);
            collect_type_strings(&fd.ty, &mut pool);
        }
        collect_type_origin_strings(sd.origin.as_ref(), &mut pool);
    }

    for ed in &module.enums {
        if ed.variants.is_empty()
            || ed.layout.as_ref().is_some_and(|layout| {
                matches!(layout.encoding, EnumTagEncoding::SingleInhabited { .. })
            })
        {
            pool.raise_to(SINGLE_INHABITED_ENUM_FORMAT_VERSION);
        }
        // v45 (WS3.14(b)): a 128-bit tag repr — the explicit hint or a niche
        // lane — raises the writer, so no pre-v45 blob carries tag 9 or 10.
        if ed.repr.is_some_and(EnumTagRepr::is_abi_surface)
            || matches!(
                &ed.layout,
                Some(layout) if matches!(
                    &layout.encoding,
                    crate::ty::EnumTagEncoding::Niche { niche_ty, .. }
                        if niche_ty.is_abi_surface()
                )
            )
        {
            raise_to_abi_surface(&mut pool);
        }
        pool.intern(&ed.name);
        for v in &ed.variants {
            pool.intern(&v.name);
            for ty in &v.fields {
                collect_type_strings(ty, &mut pool);
            }
            for name in &v.field_names {
                pool.intern(name);
            }
        }
        collect_type_origin_strings(ed.origin.as_ref(), &mut pool);
    }

    for rd in &module.records {
        pool.intern(&rd.name);
        for fd in &rd.fields {
            pool.intern(&fd.name);
            collect_type_strings(&fd.ty, &mut pool);
        }
    }

    for (index, g) in module.globals.iter().enumerate() {
        pool.intern(view.map_or(&g.name, |view| view.global_name(g, index)));
        collect_type_strings(&g.ty, &mut pool);
        if let Some(c) = &g.initializer {
            collect_constant_strings(c, &mut pool);
        }
        // v41 global ABI residue.
        if g.section.is_some()
            || g.visibility != Visibility::Default
            || g.retained
            || g.linkage.requires_contract_surface()
        {
            raise_to_contract_surface(&mut pool);
        }
        if let Some(section) = &g.section {
            pool.intern(section);
        }
    }

    if let Some(view) = view {
        for &index in &view.function_order {
            let function = &module.functions[index];
            collect_function_strings(
                function,
                view.function_name(function, index),
                view.canonical_function(index),
                view.retain_source_provenance,
                view.includes_codegen_license(),
                &mut pool,
            );
        }
    } else {
        for function in &module.functions {
            collect_function_strings(function, &function.name, None, false, true, &mut pool);
        }
    }

    // v41 module-level sections.
    if !module.global_asm.is_empty() || !module.imports.is_empty() {
        raise_to_contract_surface(&mut pool);
    }
    for asm in &module.global_asm {
        pool.intern(asm);
    }
    for import in &module.imports {
        pool.intern(&import.name);
        if let Some(Producer::Other(producer)) = &import.producer {
            pool.intern(producer);
        }
        // v44: a row recorded under any scheme but the legacy V2 needs the
        // per-row scheme tag. A table of V2 rows keeps its v41..=v43 bytes.
        if !import.scheme.is_v2() {
            pool.raise_to(IMPORT_SCHEME_FORMAT_VERSION);
        }
    }

    if include_proof_sidecars {
        if let Some(view) = view {
            for &index in &view.obligation_rows {
                collect_proof_obligation_strings(&module.proof_obligations[index], &mut pool);
            }
        } else {
            for obligation in &module.proof_obligations {
                collect_proof_obligation_strings(obligation, &mut pool);
            }
        }

        for pc in &module.proof_certificates {
            pool.intern(&pc.prover);
            collect_evidence_strings(&pc.evidence, &mut pool);
            if pc.assurance.is_some() {
                raise_to_contract_surface(&mut pool);
            }
            if let ProofEvidence::InheritedFromCallee {
                external: Some(reference),
                ..
            } = &pc.evidence
            {
                raise_to_contract_surface(&mut pool);
                pool.intern(&reference.symbol);
            }
        }
    }

    for sm in &module.spec_modules {
        collect_spec_module_strings(sm, &mut pool);
    }

    pool.seal()
}

/// Raise the writer to v41. Every v41 write is gated on this, so a module that
/// uses no contract-surface feature keeps its pre-v41 bytes exactly.
fn raise_to_contract_surface(pool: &mut StringPoolBuilder) {
    pool.raise_to(CONTRACT_SURFACE_FORMAT_VERSION);
}

fn contract_surface(pool: &SealedStringPool) -> bool {
    pool.minimum_version() >= CONTRACT_SURFACE_FORMAT_VERSION
}

/// Raise the writer to v45 (the ABI surface). Every v45 write is gated on
/// [`abi_surface`], so a module using no ABI-surface fact keeps its pre-v45
/// bytes exactly.
fn raise_to_abi_surface(pool: &mut StringPoolBuilder) {
    pool.raise_to(ABI_SURFACE_FORMAT_VERSION);
}

fn abi_surface(pool: &SealedStringPool) -> bool {
    pool.minimum_version() >= ABI_SURFACE_FORMAT_VERSION
}

/// v41: intern every pooled string a clause's typed bindings reach. `Datatype`
/// sorts nest, so this recurses. A missed intern no longer mints an id for a
/// decoder to choke on: `write_str` only looks an id up, so the WRITER panics
/// by name in `SealedStringPool::id_of` and no bytes exist at all.
fn collect_clause_sort_strings(sort: &ClauseSort, pool: &mut StringPoolBuilder) {
    match sort {
        ClauseSort::Array(k, v) => {
            collect_clause_sort_strings(k, pool);
            collect_clause_sort_strings(v, pool);
        }
        ClauseSort::Datatype { name, constructors } => {
            pool.intern(name);
            for (ctor, fields) in constructors {
                pool.intern(ctor);
                for (field, field_sort) in fields {
                    pool.intern(field);
                    collect_clause_sort_strings(field_sort, pool);
                }
            }
        }
        ClauseSort::Bool
        | ClauseSort::Int
        | ClauseSort::BitVec(_)
        | ClauseSort::Float { .. }
        | ClauseSort::RoundingMode => {}
    }
}

fn collect_proof_formula_strings(formula: &ProofFormula, pool: &mut StringPoolBuilder) {
    pool.intern(&formula.schema);
    pool.intern(&formula.payload);
    if let Some(smtlib) = &formula.smtlib {
        pool.intern(smtlib);
    }
    if let Some(sort) = &formula.sort {
        pool.intern(sort);
    }
    if !formula.bindings.is_empty() {
        raise_to_contract_surface(pool);
        for (name, binding) in &formula.bindings {
            pool.intern(name);
            collect_clause_sort_strings(&binding.sort, pool);
            // v46: the spec-variable places have no encoding before v46, so a
            // formula that uses one selects the version wherever it is carried.
            if matches!(
                binding.place,
                ClausePlace::SpecVar { .. } | ClausePlace::SpecVarNext { .. }
            ) {
                pool.raise_to(SPEC_CARRIER_FORMAT_VERSION);
            }
            // v59: the world epochs likewise have no encoding before v59.
            if matches!(
                binding.place,
                ClausePlace::WorldPre | ClausePlace::WorldPost
            ) {
                pool.raise_to(EFFECT_SUMMARY_FORMAT_VERSION);
            }
            // v62: likewise the entry-state pointee place (roadmap DG-63).
            if matches!(binding.place, ClausePlace::ParamPointeeEntry { .. }) {
                pool.raise_to(PARAM_POINTEE_PLACE_FORMAT_VERSION);
            }
        }
    }
}

/// The `source_provenance` a projection spells for `function`: ONE decision,
/// read by both walks. Spelling this predicate twice is precisely the
/// collector/writer disagreement the sealed table cannot see in the direction
/// where the collection walk pools more than the writer spells (see the
/// contract-surface comment below), so it is not spelled twice.
fn projected_source_provenance<'f, X>(
    function: &'f FunctionG<X>,
    canonical: Option<&FunctionCanonicalPlan>,
    retain_source_provenance: bool,
) -> Option<&'f SourceProvenance> {
    function.source_provenance.as_ref().filter(|_| {
        retain_source_provenance
            || canonical.is_none_or(|projection| projection.preserve_source_provenance)
    })
}

fn collect_function_strings<X: WireExt>(
    function: &FunctionG<X>,
    name: &str,
    canonical: Option<&FunctionCanonicalPlan>,
    retain_source_provenance: bool,
    include_codegen_license: bool,
    pool: &mut StringPoolBuilder,
) {
    pool.intern(name);
    // v41 function-level contract surface. When the projection omits the
    // codegen license, neither `body_gate` nor `display_path` may raise the
    // version or pool a string; `write_function` is handed the same flag and
    // makes the same choice. The sealed table catches ONE direction of a
    // disagreement: if the writer spells a license string this walk skipped,
    // `id_of` panics by name. It does not catch the other direction at all —
    // a raise or an intern HERE that the writer does not match still emits a
    // v41 header and shifts every later string id, with nothing for the
    // sealed pool to object to. What pins that direction is a test:
    // `executable_content_projection_strips_the_codegen_license` asserts the
    // license-only image is byte-identical to the same module unlicensed and
    // that its header is `BASE_FORMAT_VERSION`. MEASURED 2026-09-20 —
    // forcing `licensed = true` here, writer untouched, compiles silently and
    // fails that assertion (`left: 41, right: 38`), nothing else.
    let licensed = include_codegen_license
        && (function.body_gate.is_some() || function.display_path.is_some());
    if licensed
        || function.attrs.naked
        || !function.attrs.target_features.is_empty()
        || function.linkage.requires_contract_surface()
    {
        raise_to_contract_surface(pool);
    }
    if include_codegen_license {
        if let Some(crate::BodyGate::Gated {
            authority,
            evidence,
        }) = &function.body_gate
        {
            pool.intern(authority);
            // v61: an evidenced license is tag 3, carried by the
            // proof-surface version, for THIS module only.
            if evidence.is_some() {
                pool.raise_to(CERTIFICATE_BINDING_FORMAT_VERSION);
            }
        }
        if let Some(path) = &function.display_path {
            pool.intern(path);
        }
    }
    for feature in &function.attrs.target_features {
        pool.intern(feature);
    }
    // v45 (WS3.10): function symbol attributes. Written on EVERY projection —
    // they are facts about the executable image, not a verdict about it.
    if function.has_symbol_attributes()
        || function.calling_conv.is_abi_surface()
        || function.attrs.uses_abi_surface()
    {
        raise_to_abi_surface(pool);
    }
    // v45 (WS3.11): a `PassMode::Cast` names lane types, which pool their
    // identity strings exactly like any other type.
    for slot in function.attrs.params.iter().chain([&function.attrs.ret]) {
        if let Some(crate::PassMode::Cast { pieces }) = &slot.pass {
            for piece in pieces {
                collect_type_strings(piece, pool);
            }
        }
    }
    if let Some(section) = &function.section {
        pool.intern(section);
    }
    if let Some(canonical) = canonical {
        for &block_index in &canonical.block_order {
            let block = &function.blocks[block_index];
            for (_, ty) in &block.params {
                collect_type_strings(ty, pool);
            }
            for node in &block.body {
                collect_inst_strings(&node.inst, pool);
            }
        }
    } else {
        for block in &function.blocks {
            for (_, ty) in &block.params {
                collect_type_strings(ty, pool);
            }
            for node in &block.body {
                collect_inst_strings(&node.inst, pool);
            }
        }
    }
    if let Some(summary) = &function.summary {
        for clause in summary
            .requires
            .iter()
            .chain(summary.ensures.iter())
            .chain(summary.decreases.iter())
        {
            collect_proof_formula_strings(clause, pool);
        }
        for parameter in &summary.params {
            pool.intern(parameter);
        }
        if !summary.decreases.is_empty() || summary.backed_by.is_some() {
            raise_to_contract_surface(pool);
        }
        if let Some(reference) = &summary.backed_by {
            pool.intern(&reference.symbol);
        }
        // v59: an effect summary pools no string; it only selects the version
        // that can spell it.
        if summary.effects.is_some() {
            pool.raise_to(EFFECT_SUMMARY_FORMAT_VERSION);
        }
    }
    if let Some(names) = &function.value_names {
        for (_, name) in names {
            pool.intern(name);
        }
    }
    let source_provenance =
        projected_source_provenance(function, canonical, retain_source_provenance);
    if let Some(provenance) = source_provenance {
        for source_loop in &provenance.loops {
            for binding in &source_loop.bindings {
                pool.intern(&binding.name);
            }
        }
    }
    if let Some(Producer::Other(producer)) = &function.producer {
        pool.intern(producer);
    }
}

/// The collection half of [`write_obligation_kind`].
fn collect_obligation_kind_strings(kind: &ObligationKind, pool: &mut StringPoolBuilder) {
    match kind {
        ObligationKind::Termination | ObligationKind::Ownership => raise_to_contract_surface(pool),
        ObligationKind::Custom { namespace, name } => {
            raise_to_contract_surface(pool);
            pool.intern(namespace);
            pool.intern(name);
        }
        _ => {}
    }
}

fn collect_proof_obligation_strings(obligation: &ProofObligation, pool: &mut StringPoolBuilder) {
    pool.intern(&obligation.description);
    collect_obligation_kind_strings(&obligation.kind, pool);
    if let Some(formula) = &obligation.formula {
        collect_proof_formula_strings(formula, pool);
    }
    if let Some(source) = &obligation.source {
        pool.intern(&source.source_id);
        pool.intern(&source.assertion_id);
        if let Some(public) = &source.public {
            pool.intern(&public.obligation_id);
        }
    }
    if let Some(spec) = &obligation.spec {
        pool.raise_to(SPEC_CARRIER_FORMAT_VERSION);
        pool.intern(&spec.machine);
        pool.intern(&spec.temporal);
    }
}

/// The collection half of [`write_spec_module`]: every string that writer
/// spells, interned here while the table is still open.
fn collect_spec_module_strings(sm: &crate::spec::SpecModule, pool: &mut StringPoolBuilder) {
    pool.intern(&sm.name);
    for v in &sm.vars {
        pool.intern(&v.name);
        pool.intern(&v.ty);
        if let Some(sort) = &v.sort {
            pool.raise_to(SPEC_CARRIER_FORMAT_VERSION);
            collect_clause_sort_strings(sort, pool);
        }
    }
    for a in &sm.actions {
        pool.intern(a);
    }
    for inv in &sm.invariants {
        pool.intern(&inv.name);
        pool.intern(&inv.formula);
        if let Some(typed) = &inv.typed {
            pool.raise_to(SPEC_CARRIER_FORMAT_VERSION);
            collect_proof_formula_strings(typed, pool);
        }
    }
    for anchor in &sm.anchors {
        pool.intern(&anchor.machine);
        pool.intern(&anchor.action);
        pool.intern(&anchor.rust_symbol);
        pool.intern(&anchor.span);
        if let Some(p) = &anchor.project {
            pool.intern(p);
        }
    }
    for w in &sm.waivers {
        pool.intern(&w.machine);
        pool.intern(&w.action);
        pool.intern(&w.reason);
    }
    for p in &sm.proofs {
        pool.intern(&p.machine);
        pool.intern(&p.action);
        pool.intern(&p.proof_name);
        if let crate::spec::ProofKind::CleanTheorem { name } = &p.kind {
            pool.raise_to(SPEC_CARRIER_FORMAT_VERSION);
            pool.intern(name);
        }
    }
    if !sm.temporal.is_empty() {
        pool.raise_to(SPEC_CARRIER_FORMAT_VERSION);
    }
    for property in &sm.temporal {
        pool.intern(&property.name);
        if let Some(action) = property.form.action() {
            pool.intern(action);
        }
        for (formula, _) in property.form.formulas() {
            collect_proof_formula_strings(formula, pool);
        }
    }
    if let crate::spec::SpecOrigin::External(path) = &sm.origin {
        pool.intern(path);
    }
}

fn collect_constant_strings<X: WireExt>(c: &ConstantG<X>, pool: &mut StringPoolBuilder) {
    match c {
        // v50: the reader gates Constant tag 16, so the writer must raise the
        // header wherever a splat is written (any depth, any carrier).
        ConstantG::Splat { elem, .. } => {
            pool.raise_to(ARRAY_SPLAT_FORMAT_VERSION);
            collect_constant_strings(elem, pool);
        }
        ConstantG::Aggregate(elems)
        | ConstantG::Array(elems)
        | ConstantG::Vector(elems)
        | ConstantG::Sequence(elems)
        | ConstantG::Set(elems) => {
            for e in elems {
                collect_constant_strings(e, pool);
            }
        }
        ConstantG::Record(fields) => {
            for (name, val) in fields {
                pool.intern(name);
                collect_constant_strings(val, pool);
            }
        }
        ConstantG::Closure { captures, .. } => {
            for c in captures {
                collect_constant_strings(c, pool);
            }
        }
        ConstantG::SymbolAddr { symbol, .. } => {
            pool.intern(symbol);
        }
        // Crystal lane (E3b): a module containing an unwritten lane is v49; one that does not
        // is untouched.
        ConstantG::Uninit => {
            pool.raise_to(UNINIT_LANE_FORMAT_VERSION);
        }
        // v70: the reader gates Constant tag 18 likewise.
        ConstantG::TensorBlob { .. } => pool.raise_to(TENSOR_BLOB_FORMAT_VERSION),
        _ => {}
    }
}

fn collect_type_identity_strings<X: WireExt>(ty: &TyG<X>, pool: &mut StringPoolBuilder) {
    match ty {
        TyG::Dialect(ty) => {
            pool.raise_to(DIALECT_TYPE_FORMAT_VERSION);
            pool.intern(&ty.namespace);
            pool.intern(&ty.name);
        }
        // v40: the writer must raise the header for every feature the reader
        // gates, or it emits a self-inconsistent blob (sub-tag 4 under a v38
        // header, which `read_fat_ptr_kind` refuses with `InvalidTag(4)`).
        TyG::FatPtr(FatPtrKind::ContainerVtable) => {
            pool.raise_to(CONTAINER_VTABLE_FORMAT_VERSION);
        }
        // v43: same discipline — raise the header for the feature the reader
        // gates, or the writer emits tag 38 under a header that refuses it.
        TyG::Storage(_) => pool.raise_to(STORAGE_LAYOUT_FORMAT_VERSION),
        // v67: type tag 41 is read-gated, so any tensor occurrence raises the
        // header; its element is an inline child `visit_types` reaches next.
        TyG::Tensor(..) => pool.raise_to(TENSOR_FORMAT_VERSION),
        TyG::Handle(ty) => {
            pool.raise_to(HANDLE_TYPE_FORMAT_VERSION);
            pool.intern(&ty.name);
            pool.intern(&ty.runtime);
        }
        _ => {}
    }
}

fn collect_type_strings<X: WireExt>(ty: &TyG<X>, pool: &mut StringPoolBuilder) {
    ty.visit_types(|ty| collect_type_identity_strings(ty, pool));
}

/// Whether `inst` carries a member of the v51 INST wire batch: an instruction
/// tag (60..=62) or a sub-op tag (BinOp 23..=25, UnOp 9..=12) the reader gates
/// on `INST_WIRE_BATCH_FORMAT_VERSION`. The collector raises the header on
/// exactly this predicate, so it must name every tag the batch added — the
/// `inst_wire_batch_tags_are_read_gated` test holds the two in step.
fn carries_inst_wire_batch_member<X: WireExt>(inst: &InstG<X>) -> bool {
    matches!(
        inst,
        InstG::MakeAggregate { .. }
            | InstG::MemCopy { .. }
            | InstG::MemSet { .. }
            | InstG::BinOp {
                op: BinOp::RotL | BinOp::RotR | BinOp::FCopySign,
                ..
            }
            | InstG::UnOp {
                op: UnOp::CtLz | UnOp::CtTz | UnOp::BSwap | UnOp::BitReverse,
                ..
            }
    )
}

fn collect_inst_strings<X: WireExt>(inst: &InstG<X>, pool: &mut StringPoolBuilder) {
    if matches!(inst, InstG::MakeClosure { .. }) {
        pool.raise_to(MAKE_CLOSURE_FORMAT_VERSION);
    }
    // v67: Inst tag 71 is read-gated, so a contraction raises the header even
    // before its (tensor) result type does below.
    if matches!(inst, InstG::TensorContract { .. }) {
        pool.raise_to(TENSOR_FORMAT_VERSION);
    }
    // v68: Inst tags 72..=74 are read-gated likewise.
    if matches!(
        inst,
        InstG::TensorMap { .. } | InstG::TensorReduce { .. } | InstG::TensorView { .. }
    ) {
        pool.raise_to(TENSOR_MAP_REDUCE_VIEW_FORMAT_VERSION);
    }
    // v69: Inst tags 75 and 76 are read-gated likewise.
    if matches!(
        inst,
        InstG::TensorGather { .. } | InstG::TensorScatter { .. }
    ) {
        pool.raise_to(TENSOR_GATHER_SCATTER_FORMAT_VERSION);
    }
    if matches!(
        inst,
        InstG::CallCannotUnwind { .. } | InstG::CallIndirectCannotUnwind { .. }
    ) {
        pool.raise_to(CALL_UNWIND_BOUNDARY_FORMAT_VERSION);
    }
    // Crystal lane (wave-DS): a module containing a drop is v47; one that does not is untouched.
    if matches!(inst, InstG::Drop { .. }) {
        pool.raise_to(DROP_INST_FORMAT_VERSION);
    }
    // v51: every INST wire batch tag is read-gated, so a module carrying one
    // raises the header; a module with none keeps its bytes.
    if carries_inst_wire_batch_member(inst) {
        pool.raise_to(INST_WIRE_BATCH_FORMAT_VERSION);
    }
    // Crystal lane (D3): a module containing a WEAK compare-exchange is v48; a module whose
    // compare-exchanges are all strong is untouched.
    if matches!(inst, InstG::CmpXchg { weak: true, .. }) {
        pool.raise_to(WEAK_CMPXCHG_FORMAT_VERSION);
    }
    // v52 (plan item P): a module carrying a KINDED assert (Inst tag 63) is
    // v52; one whose every assert is `Unspecified` keeps tag 29 and its bytes.
    if matches!(inst, InstG::Assert { kind, .. } if !kind.is_unspecified()) {
        pool.raise_to(ASSERT_KIND_FORMAT_VERSION);
    }
    // v54 (amendment P): a module carrying a panic site (Inst tag 66 or 67) is
    // v54; one without keeps its version and its bytes.
    if inst.panic_site().is_some() {
        pool.raise_to(PANIC_SITE_FORMAT_VERSION);
    }
    // v55 (amendment D): a module carrying a `DropInvoke` (Inst tag 68) is
    // v55; a plain `Drop` keeps tag 57 and v47.
    if matches!(inst, InstG::DropInvoke { .. }) {
        pool.raise_to(DROP_GLUE_FORMAT_VERSION);
    }
    // v56 (amendment D, Part 2): a module carrying an `InvokeIndirect` (Inst
    // tag 69) is v56; one without keeps its version and its bytes.
    if matches!(inst, InstG::InvokeIndirect { .. }) {
        pool.raise_to(UNWIND_TWINS_FORMAT_VERSION);
    }
    inst.visit_type_occurrences(|occurrence| match occurrence {
        crate::type_walk::TypeOccurrence::Spelled(ty) => collect_type_identity_strings(ty, pool),
        crate::type_walk::TypeOccurrence::Ground(ty) => collect_type_identity_strings(ty, pool),
    });
    // v45 (WS3.12): an indirect call site carries its own convention, so it
    // raises the writer exactly as a function's does.
    if let InstG::CallIndirect { calling_conv, .. }
    | InstG::CallIndirectCannotUnwind { calling_conv, .. }
    | InstG::InvokeIndirect { calling_conv, .. } = inst
        && calling_conv.is_abi_surface()
    {
        raise_to_abi_surface(pool);
    }
    match inst {
        InstG::OpenFrame { def } => {
            pool.intern(&def.name);
            for slot in &def.slots {
                pool.intern(&slot.name);
            }
        }
        InstG::DialectOp(op) => {
            pool.intern(&op.dialect);
            pool.intern(&op.op);
            for entry in &op.attrs {
                pool.intern(&entry.name);
                if let crate::dialect::AttrValue::Str(s) = &entry.value {
                    pool.intern(s);
                }
            }
        }
        InstG::Const { value, .. } => {
            collect_constant_strings(value, pool);
        }
        // v50: Inst tag 59 is read-gated, so it raises the header.
        InstG::ArraySplat { .. } => {
            pool.raise_to(ARRAY_SPLAT_FORMAT_VERSION);
        }
        InstG::Switch { cases, .. } => {
            for case in cases {
                collect_constant_strings(&case.value, pool);
            }
        }
        _ => {}
    }
}

fn collect_evidence_strings(ev: &ProofEvidence, pool: &mut StringPoolBuilder) {
    match ev {
        ProofEvidence::LeanProof(s) | ProofEvidence::KaniHarness(s) | ProofEvidence::Trusted(s) => {
            pool.intern(s);
        }
        ProofEvidence::TranslationValidation { rule_name, .. } => {
            pool.intern(rule_name);
        }
        ProofEvidence::CleanCic {
            kernel_recheck: Some(recheck),
            ..
        } => {
            pool.intern(&recheck.module);
            for thm in &recheck.theorems {
                pool.intern(thm);
            }
            pool.intern(&recheck.anchor);
            for ax in &recheck.allowed_axioms {
                pool.intern(ax);
            }
            // v61: a certificate binding selects the version that carries it,
            // for THIS module only.
            if let Some(binding) = recheck.binding.as_deref() {
                pool.raise_to(CERTIFICATE_BINDING_FORMAT_VERSION);
                if let Some(source) = &binding.source {
                    pool.intern(&source.decl);
                }
                for callee in &binding.callees {
                    pool.intern(callee);
                }
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
    // Decoding only needs id -> string lookup. Keeping the writer's ordered
    // index here used to rebuild an otherwise-unused BTreeMap and duplicate
    // every decoded string.
    pool: Option<Vec<String>>,
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

    /// Read a fixed-width field into stack storage.
    ///
    /// Tags, varints, ids, fixed integers, and digests dominate the binary
    /// grammar. Routing them through `read_exact` allocated a fresh `Vec` for
    /// every encoded scalar (and for every byte of a multi-byte varint). Keep
    /// the same pre-read bounds check while removing that per-field heap work.
    fn read_array<const N: usize>(&mut self) -> Result<[u8; N], BinaryError> {
        self.reserve_checked(N)?;
        let mut bytes = [0u8; N];
        self.cursor
            .read_exact(&mut bytes)
            .map_err(|_| BinaryError::UnexpectedEof)?;
        Ok(bytes)
    }

    fn read_u8(&mut self) -> Result<u8, BinaryError> {
        Ok(self.read_array::<1>()?[0])
    }

    fn read_bool(&mut self) -> Result<bool, BinaryError> {
        match self.read_u8()? {
            0 => Ok(false),
            1 => Ok(true),
            t => Err(BinaryError::InvalidTag(t)),
        }
    }

    fn read_u32(&mut self) -> Result<u32, BinaryError> {
        self.read_array().map(u32::from_le_bytes)
    }

    fn read_u64(&mut self) -> Result<u64, BinaryError> {
        self.read_array().map(u64::from_le_bytes)
    }

    fn read_v64(&mut self) -> Result<u64, BinaryError> {
        let mut result = 0u64;
        let mut shift = 0;
        loop {
            let b = self.read_u8()?;
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
        self.read_array().map(i128::from_le_bytes)
    }

    fn read_u128(&mut self) -> Result<u128, BinaryError> {
        self.read_array().map(u128::from_le_bytes)
    }

    fn read_f64(&mut self) -> Result<f64, BinaryError> {
        self.read_array().map(f64::from_le_bytes)
    }

    fn read_raw_str(&mut self) -> Result<String, BinaryError> {
        let len = self.read_checked_len()?;
        let b = self.read_exact(len)?;
        String::from_utf8(b).map_err(|_| BinaryError::Utf8Error)
    }

    fn read_str(&mut self) -> Result<String, BinaryError> {
        if self.pool.is_some() {
            let id = self.read_v32()?;
            self.pool
                .as_ref()
                .expect("checked above")
                .get(id as usize)
                .cloned()
                .ok_or(BinaryError::BadStringId(id))
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
    /// Pinned as bytes: `refuse/blob_pool_count_exceeds_input` (a hostile
    /// count) and `refuse/blob_truncated` (a cut input): both are `TooLarge`,
    /// because this check runs before every read — which is also why
    /// `BinaryError::UnexpectedEof` cannot fire.
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

fn read_opt_v32(r: &mut Reader<'_>) -> Result<Option<u32>, BinaryError> {
    let tag = r.read_u8()?;
    match tag {
        0 => Ok(None),
        1 => Ok(Some(r.read_v32()?)),
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

fn write_ty<X: WireExt>(buf: &mut impl BinarySink, pool: &SealedStringPool, ty: &TyG<X>) {
    match ty {
        TyG::Storage(layout) => {
            if !layout.is_well_formed(64) {
                buf.refuse(WireRefusal::InvalidStorageGeometry(*layout));
                return;
            }
            write_u8(buf, 40);
            write_v64(buf, layout.size_bytes);
            write_v64(buf, layout.align_bytes);
        }
        TyG::I8 => write_u8(buf, 0),
        TyG::I16 => write_u8(buf, 1),
        TyG::I32 => write_u8(buf, 2),
        TyG::I64 => write_u8(buf, 3),
        TyG::I128 => write_u8(buf, 4),
        TyG::U8 => write_u8(buf, 5),
        TyG::U16 => write_u8(buf, 6),
        TyG::U32 => write_u8(buf, 7),
        TyG::U64 => write_u8(buf, 8),
        TyG::U128 => write_u8(buf, 9),
        // v25 B1 scalars (tags 33-35; Error is UNENCODABLE - see below).
        TyG::Isize => write_u8(buf, 33),
        TyG::Usize => write_u8(buf, 34),
        TyG::Char => write_u8(buf, 35),
        // Ty::Error is producer-internal (a fail-closed typing placeholder)
        // with no wire spelling at any version; JSON and MessagePack can spell
        // one, so a decoded module CAN reach this arm. Refused here, by the
        // writer's own arm — never an invented tag for a typing hole.
        TyG::Error => buf.refuse(WireRefusal::ProducerInternalType),
        TyG::F16 => write_u8(buf, 31),
        TyG::F32 => write_u8(buf, 10),
        TyG::F64 => write_u8(buf, 11),
        TyG::Bool => write_u8(buf, 12),
        TyG::Ptr => write_u8(buf, 13),
        TyG::Unit => write_u8(buf, 14),
        TyG::Never => write_u8(buf, 15),
        TyG::Struct(id) => {
            write_u8(buf, 16);
            write_struct_id(buf, *id);
        }
        TyG::Array(tid, len) => {
            write_u8(buf, 17);
            write_ty_id(buf, *tid);
            write_v64(buf, *len);
        }
        TyG::Tuple(elems) => {
            write_u8(buf, 18);
            write_count(buf, "Ty::Tuple elements", elems.len());
            for e in elems {
                write_ty(buf, pool, e);
            }
        }
        TyG::Enum(id) => {
            write_u8(buf, 19);
            write_enum_id(buf, *id);
        }
        TyG::Func(id) => {
            write_u8(buf, 20);
            write_func_ty_id(buf, *id);
        }
        TyG::Ref(inner) => {
            write_u8(buf, 21);
            write_ty(buf, pool, inner);
        }
        TyG::RefMut(inner) => {
            write_u8(buf, 22);
            write_ty(buf, pool, inner);
        }
        TyG::PtrConst(inner) => {
            write_u8(buf, 23);
            write_ty(buf, pool, inner);
        }
        TyG::PtrMut(inner) => {
            write_u8(buf, 24);
            write_ty(buf, pool, inner);
        }
        TyG::Rc(inner) => {
            write_u8(buf, 25);
            write_ty(buf, pool, inner);
        }
        TyG::Set(elem, repr) => {
            write_u8(buf, 26);
            write_ty_id(buf, *elem);
            write_set_repr(buf, repr);
        }
        TyG::Sequence(elem) => {
            write_u8(buf, 27);
            write_ty_id(buf, *elem);
        }
        TyG::Record(id) => {
            write_u8(buf, 28);
            write_record_id(buf, *id);
        }
        TyG::Closure(id) => {
            write_u8(buf, 29);
            write_closure_ty_id(buf, *id);
        }
        TyG::FatPtr(kind) => {
            write_u8(buf, 30);
            write_fat_ptr_kind(buf, pool, kind);
        }
        TyG::Vector(elem, lanes) => {
            write_u8(buf, 32);
            write_v32(buf, *lanes);
            write_ty(buf, pool, elem);
        }
        // v30: refinement carrier. Representation-preserving — the base `TyId`
        // is what any consumer lays out; the `PredId` is proof surface.
        TyG::Refine(base, pred) => {
            write_u8(buf, 36);
            write_ty_id(buf, *base);
            write_v32(buf, pred.index());
        }
        TyG::Dialect(ty) => {
            // Identity hashing may precede structural validation on untrusted
            // input. Encode the claim exactly; readers/validators reject its
            // malformed lexical identity rather than turning hashing into a
            // new panic boundary.
            write_u8(buf, 37);
            write_str(buf, pool, &ty.namespace);
            write_str(buf, pool, &ty.name);
            write_v32(buf, ty.version);
        }
        // v43. Encoded exactly as claimed (the reader/validator reject a
        // malformed pair) so identity hashing never becomes a panic boundary.
        TyG::Handle(ty) => {
            write_u8(buf, 38);
            write_str(buf, pool, &ty.name);
            write_str(buf, pool, &ty.runtime);
        }
        // v67 (tensor region): the rank, then the element, as `Vector` spells
        // its lanes and element. Encoded exactly as claimed: an element the
        // validator refuses (`InvalidTensorType`) still has one spelling, so
        // identity hashing never becomes a refusal boundary for it.
        TyG::Tensor(elem, rank) => {
            write_u8(buf, 41);
            write_v32(buf, *rank);
            write_ty(buf, pool, elem);
        }
        TyG::Ext(e) => {
            write_u8(buf, TY_EXT_TAG);
            X::write_ext(buf, e);
        }
    }
}

fn write_fat_ptr_kind(buf: &mut impl BinarySink, _pool: &SealedStringPool, kind: &FatPtrKind) {
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
        // v38. Read-gated below: an unknown tag already fails closed with
        // `InvalidTag`, so the gate is not what makes this safe — it is what
        // keeps a v37-LABELLED blob carrying tag 3 from being accepted as
        // well-formed by a reader that would otherwise take it.
        FatPtrKind::ContainerLen => write_u8(buf, 3),
        // v40. Read-gated below on the same terms as tag 3: the gate keeps a
        // v39-or-older-LABELLED blob carrying tag 4 from being taken as
        // well-formed. The writer raises the header to 40 for it in
        // `collect_type_identity_strings`.
        FatPtrKind::ContainerVtable => write_u8(buf, 4),
    }
}

fn read_fat_ptr_kind(r: &mut Reader<'_>) -> Result<FatPtrKind, BinaryError> {
    match r.read_u8()? {
        0 => Ok(FatPtrKind::Slice(r.read_ty_id()?)),
        1 => Ok(FatPtrKind::Str),
        2 => Ok(FatPtrKind::TraitObject {
            trait_id: r.read_v32()?,
        }),
        3 if r.version >= 38 => Ok(FatPtrKind::ContainerLen),
        4 if r.version >= CONTAINER_VTABLE_FORMAT_VERSION => Ok(FatPtrKind::ContainerVtable),
        t => Err(BinaryError::InvalidTag(t)),
    }
}

fn write_set_repr(buf: &mut impl BinarySink, repr: &SetRepr) {
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

fn write_universe(buf: &mut impl BinarySink, pool: &SealedStringPool, u: &crate::pred::Universe) {
    match u {
        crate::pred::Universe::IntRange { lo, hi } => {
            write_u8(buf, 0);
            write_i128(buf, *lo);
            write_i128(buf, *hi);
        }
        crate::pred::Universe::Members(items) => {
            write_u8(buf, 1);
            write_count(buf, "Universe::Members items", items.len());
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

fn write_space(buf: &mut impl BinarySink, space: crate::pred::Space) {
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

fn write_pred(buf: &mut impl BinarySink, pool: &SealedStringPool, p: &crate::pred::Pred) {
    use crate::pred::Pred;
    match p {
        Pred::Interval { lo, hi } => {
            write_u8(buf, 0);
            write_i128(buf, *lo);
            write_i128(buf, *hi);
        }
        Pred::FiniteSet(items) => {
            write_u8(buf, 1);
            write_count(buf, "Pred::FiniteSet items", items.len());
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
            write_count(buf, "Pred::Conj children", children.len());
            for c in children {
                write_v32(buf, c.index());
            }
        }
        Pred::Disj(children) => {
            write_u8(buf, 6);
            write_count(buf, "Pred::Disj children", children.len());
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

fn read_ty<X: WireExt>(r: &mut Reader<'_>) -> Result<TyG<X>, BinaryError> {
    r.enter_nesting()?;
    let result = read_ty_inner(r);
    r.leave_nesting();
    result
}

fn read_ty_inner<X: WireExt>(r: &mut Reader<'_>) -> Result<TyG<X>, BinaryError> {
    let tag = r.read_u8()?;
    match tag {
        0 => Ok(TyG::I8),
        1 => Ok(TyG::I16),
        2 => Ok(TyG::I32),
        3 => Ok(TyG::I64),
        4 => Ok(TyG::I128),
        5 => Ok(TyG::U8),
        6 => Ok(TyG::U16),
        7 => Ok(TyG::U32),
        8 => Ok(TyG::U64),
        9 => Ok(TyG::U128),
        // v25 B1 scalars.
        33 => Ok(TyG::Isize),
        34 => Ok(TyG::Usize),
        35 => Ok(TyG::Char),
        10 => Ok(TyG::F32),
        11 => Ok(TyG::F64),
        12 => Ok(TyG::Bool),
        13 => Ok(TyG::Ptr),
        14 => Ok(TyG::Unit),
        15 => Ok(TyG::Never),
        16 => Ok(TyG::Struct(r.read_struct_id()?)),
        17 => {
            let tid = r.read_ty_id()?;
            let len = r.read_v64()?;
            Ok(TyG::Array(tid, len))
        }
        18 => {
            let n = r.read_checked_len()?;
            let mut elems = Vec::with_capacity(n);
            for _ in 0..n {
                elems.push(read_ty(r)?);
            }
            Ok(TyG::Tuple(elems))
        }
        19 => Ok(TyG::Enum(r.read_enum_id()?)),
        20 => Ok(TyG::Func(r.read_func_ty_id()?)),
        21 => Ok(TyG::Ref(Box::new(read_ty(r)?))),
        22 => Ok(TyG::RefMut(Box::new(read_ty(r)?))),
        23 => Ok(TyG::PtrConst(Box::new(read_ty(r)?))),
        24 => Ok(TyG::PtrMut(Box::new(read_ty(r)?))),
        25 => Ok(TyG::Rc(Box::new(read_ty(r)?))),
        26 => {
            let elem = r.read_ty_id()?;
            let repr = read_set_repr(r)?;
            Ok(TyG::Set(elem, repr))
        }
        27 => Ok(TyG::Sequence(r.read_ty_id()?)),
        28 => Ok(TyG::Record(r.read_record_id()?)),
        29 => Ok(TyG::Closure(r.read_closure_ty_id()?)),
        30 => Ok(TyG::FatPtr(read_fat_ptr_kind(r)?)),
        31 => Ok(TyG::F16),
        32 => {
            let lanes = r.read_v32()?;
            let elem = read_ty(r)?;
            Ok(TyG::Vector(Box::new(elem), lanes))
        }
        // v30 refinement carrier. No version gate: tag 36 never appears in a
        // pre-v30 blob, so reaching it already implies a v30+ writer.
        36 => {
            let base = r.read_ty_id()?;
            let pred = crate::value::PredId::new(r.read_v32()?);
            Ok(TyG::Refine(base, pred))
        }
        37 if r.version >= 39 => {
            let ty = crate::DialectTy::new(r.read_str()?, r.read_str()?, r.read_v32()?);
            ty.validate()
                .map_err(|error| BinaryError::InvalidData(error.to_string()))?;
            Ok(TyG::Dialect(Box::new(ty)))
        }
        // v43. Read-gated: a v42-or-older header carrying tag 38 is refused
        // with `InvalidTag(38)` rather than taken as well-formed.
        38 if r.version >= HANDLE_TYPE_FORMAT_VERSION => {
            let ty = crate::HandleTy::new(r.read_str()?, r.read_str()?);
            ty.validate()
                .map_err(|error| BinaryError::InvalidData(error.to_string()))?;
            Ok(TyG::Handle(Box::new(ty)))
        }
        40 if r.version >= STORAGE_LAYOUT_FORMAT_VERSION => {
            let layout = crate::StorageLayout::new(r.read_v64()?, r.read_v64()?);
            if !layout.is_well_formed(64) {
                return Err(BinaryError::InvalidData(
                    "invalid storage-only layout geometry".into(),
                ));
            }
            Ok(TyG::Storage(layout))
        }
        // v67 (tensor region). Read-gated: a v66-or-older header carrying tag
        // 41 is refused with `InvalidTag(41)`
        // (`refuse/blob_tensor_below_its_version`). The element is read
        // through `read_ty`, so its nesting is bounded; whether it is an
        // integer is the validator's decision, never the codec's.
        41 if r.version >= TENSOR_FORMAT_VERSION => {
            let rank = r.read_v32()?;
            let elem = read_ty(r)?;
            Ok(TyG::Tensor(Box::new(elem), rank))
        }
        // Amendment S: the extension tag. A level-R reader (`NoExt`) refuses
        // it at EVERY version, forged module magic included
        // (`refuse/ty_ext_tag_under_module_magic`); a template reader reads
        // the reference. Template blobs are never below their version floor.
        TY_EXT_TAG if X::reads_ext() => Ok(TyG::Ext(X::read_ext(r)?)),
        _ => Err(BinaryError::InvalidTag(tag)),
    }
}

// ---------------------------------------------------------------------------
// Constant
// ---------------------------------------------------------------------------

fn write_constant<X: WireExt>(
    buf: &mut impl BinarySink,
    pool: &SealedStringPool,
    c: &ConstantG<X>,
) {
    match c {
        ConstantG::Int(v) => {
            write_u8(buf, 0);
            write_i128(buf, *v);
        }
        // v24: the 128-bit-faithful unsigned carrier (canonical iff the value
        // exceeds i128::MAX - the decoder REJECTS a non-canonical payload).
        ConstantG::U128(v) => {
            write_u8(buf, 13);
            write_u128(buf, *v);
        }
        // v25: raw byte-array constant (utf8 flag + length-prefixed payload).
        ConstantG::Bytes { data, utf8 } => {
            write_u8(buf, 14);
            write_bool(buf, *utf8);
            write_count(buf, "Constant::Bytes data", data.len());
            buf.extend_from_slice(data);
        }
        ConstantG::Float(v) => {
            write_u8(buf, 1);
            write_f64(buf, *v);
        }
        ConstantG::Bool(v) => {
            write_u8(buf, 2);
            write_bool(buf, *v);
        }
        ConstantG::Aggregate(elems) => {
            write_u8(buf, 3);
            write_count(buf, "Constant::Aggregate elements", elems.len());
            for e in elems {
                write_constant(buf, pool, e);
            }
        }
        ConstantG::Array(elems) => {
            write_u8(buf, 8);
            write_count(buf, "Constant::Array elements", elems.len());
            for e in elems {
                write_constant(buf, pool, e);
            }
        }
        ConstantG::Vector(elems) => {
            write_u8(buf, 11);
            write_count(buf, "Constant::Vector elements", elems.len());
            for e in elems {
                write_constant(buf, pool, e);
            }
        }
        ConstantG::Sequence(elems) => {
            write_u8(buf, 4);
            write_count(buf, "Constant::Sequence elements", elems.len());
            for e in elems {
                write_constant(buf, pool, e);
            }
        }
        ConstantG::Set(elems) => {
            write_u8(buf, 5);
            write_count(buf, "Constant::Set elements", elems.len());
            for e in elems {
                write_constant(buf, pool, e);
            }
        }
        ConstantG::Record(fields) => {
            write_u8(buf, 6);
            write_count(buf, "Constant::Record fields", fields.len());
            for (name, val) in fields {
                write_str(buf, pool, name);
                write_constant(buf, pool, val);
            }
        }
        ConstantG::Closure { func, captures } => {
            write_u8(buf, 7);
            write_func_id(buf, *func);
            write_count(buf, "Constant::Closure captures", captures.len());
            for c in captures {
                write_constant(buf, pool, c);
            }
        }
        ConstantG::FnDef(func) => {
            write_u8(buf, 9);
            write_func_id(buf, *func);
        }
        ConstantG::SymbolAddr { symbol, addend } => {
            write_u8(buf, 12);
            write_str(buf, pool, symbol);
            write_u64(buf, *addend as u64);
        }
        ConstantG::PhantomData => write_u8(buf, 10),
        // Crystal lane (E3b): an unwritten struct/tuple lane. Tag only; the lane's type is its
        // position in the enclosing aggregate. Read-gated on v49.
        ConstantG::Uninit => write_u8(buf, 15),
        // v50: one element and one fixed-width length, whatever the length.
        ConstantG::Splat { elem, len } => {
            write_u8(buf, 16);
            write_constant(buf, pool, elem);
            write_u64(buf, *len);
        }
        // v70: the 32 digest bytes, then the counted extents as fixed-width
        // `u64`s; the bytes are the module's blob table section.
        ConstantG::TensorBlob { digest, dims } => {
            write_u8(buf, CONSTANT_TENSOR_BLOB_TAG);
            buf.extend_from_slice(&digest.0);
            write_count(buf, "Constant::TensorBlob dims", dims.len());
            for dim in dims {
                write_u64(buf, *dim);
            }
        }
        ConstantG::Ext(e) => {
            write_u8(buf, CONSTANT_EXT_TAG);
            X::write_ext(buf, e);
        }
    }
}

fn read_constant<X: WireExt>(r: &mut Reader<'_>) -> Result<ConstantG<X>, BinaryError> {
    r.enter_nesting()?;
    let result = read_constant_inner(r);
    r.leave_nesting();
    result
}

fn read_constant_inner<X: WireExt>(r: &mut Reader<'_>) -> Result<ConstantG<X>, BinaryError> {
    let tag = r.read_u8()?;
    match tag {
        0 => Ok(ConstantG::Int(r.read_i128()?)),
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
            Ok(ConstantG::U128(v))
        }
        // v25 Bytes: the utf8 flag is a CHECKED claim — reject invalid UTF-8
        // under the flag at decode (mirrors the validator; a str constant
        // with broken bytes must never materialize).
        14 => {
            let utf8 = r.read_bool()?;
            let len = r.read_checked_len()?;
            let data = r.read_exact(len)?;
            if utf8 && std::str::from_utf8(&data).is_err() {
                return Err(BinaryError::InvalidData(
                    "Constant::Bytes marked utf8 carries invalid UTF-8".to_string(),
                ));
            }
            Ok(ConstantG::Bytes { data, utf8 })
        }
        1 => Ok(ConstantG::Float(r.read_f64()?)),
        2 => Ok(ConstantG::Bool(r.read_bool()?)),
        3 => {
            let n = r.read_checked_len()?;
            let mut elems = Vec::with_capacity(n);
            for _ in 0..n {
                elems.push(read_constant(r)?);
            }
            Ok(ConstantG::Aggregate(elems))
        }
        8 => {
            let n = r.read_checked_len()?;
            let mut elems = Vec::with_capacity(n);
            for _ in 0..n {
                elems.push(read_constant(r)?);
            }
            Ok(ConstantG::Array(elems))
        }
        11 => {
            let n = r.read_checked_len()?;
            let mut elems = Vec::with_capacity(n);
            for _ in 0..n {
                elems.push(read_constant(r)?);
            }
            Ok(ConstantG::Vector(elems))
        }
        4 => {
            let n = r.read_checked_len()?;
            let mut elems = Vec::with_capacity(n);
            for _ in 0..n {
                elems.push(read_constant(r)?);
            }
            Ok(ConstantG::Sequence(elems))
        }
        5 => {
            let n = r.read_checked_len()?;
            let mut elems = Vec::with_capacity(n);
            for _ in 0..n {
                elems.push(read_constant(r)?);
            }
            Ok(ConstantG::Set(elems))
        }
        6 => {
            let n = r.read_checked_len()?;
            let mut fields = Vec::with_capacity(n);
            for _ in 0..n {
                let name = r.read_str()?;
                let val = read_constant(r)?;
                fields.push((name, val));
            }
            Ok(ConstantG::Record(fields))
        }
        7 => {
            let func = r.read_func_id()?;
            let n = r.read_checked_len()?;
            let mut captures = Vec::with_capacity(n);
            for _ in 0..n {
                captures.push(read_constant(r)?);
            }
            Ok(ConstantG::Closure { func, captures })
        }
        9 => Ok(ConstantG::FnDef(r.read_func_id()?)),
        12 => {
            let symbol = r.read_str()?;
            let addend = r.read_u64()? as i64;
            Ok(ConstantG::SymbolAddr { symbol, addend })
        }
        10 => Ok(ConstantG::PhantomData),
        // Crystal lane (E3b): tag 15 is read-gated. A blob that claims a version below v49 and carries
        // it is malformed, never silently read.
        15 if r.version >= UNINIT_LANE_FORMAT_VERSION => Ok(ConstantG::Uninit),
        // v50 Splat: read-gated (an older header carrying tag 16 is refused
        // with `InvalidTag(16)`), and its canonicality is CHECKED here like
        // `U128`'s — zero or one copy is spelled `Constant::Array`.
        16 if r.version >= ARRAY_SPLAT_FORMAT_VERSION => {
            let elem = read_constant(r)?;
            let len = r.read_u64()?;
            if len < 2 {
                return Err(BinaryError::InvalidData(format!(
                    "non-canonical Constant::Splat of {len} element(s): zero or one copy is \
                     spelled Constant::Array (one-spelling rule, SPEC_RATIFICATIONS §3.1)"
                )));
            }
            Ok(ConstantG::Splat {
                elem: Box::new(elem),
                len,
            })
        }
        // v70 TensorBlob: read-gated (an older header carrying tag 18 is
        // `InvalidTag(18)`, `refuse/blob_tensor_blob_below_its_version`). The
        // codec checks no rank, row or length rule: those are the validator's
        // (`InvalidTensorBlob`, `MissingBlob`).
        CONSTANT_TENSOR_BLOB_TAG if r.version >= TENSOR_BLOB_FORMAT_VERSION => {
            let mut digest = [0u8; 32];
            digest.copy_from_slice(&r.read_exact(32)?);
            let n = r.read_checked_len()?;
            let mut dims = Vec::with_capacity(n);
            for _ in 0..n {
                dims.push(r.read_u64()?);
            }
            Ok(ConstantG::TensorBlob {
                digest: crate::blob::BlobDigest(digest),
                dims,
            })
        }
        // Amendment S: the extension tag, refused by the level-R reader at
        // every version (`refuse/constant_ext_tag_under_module_magic`).
        CONSTANT_EXT_TAG if X::reads_ext() => Ok(ConstantG::Ext(X::read_ext(r)?)),
        _ => Err(BinaryError::InvalidTag(tag)),
    }
}

// ---------------------------------------------------------------------------
// Small enums (tag-only)
// ---------------------------------------------------------------------------

// The optional `; unencodable A, B` clause names variants that exist in the
// Rust enum but have NO wire tag yet (a reserved-then-landed number is the
// only way to get one — docs/wire-allocation.md). The writer FAILS CLOSED on
// them exactly as it does on `Ty::Error`: its arm refuses the variant by name
// (`BinarySink::refuse`), never an invented tag byte. The reader is unchanged,
// so an older blob can never carry one. Each such variant is also listed in
// `wire_census::UNENCODABLE` with its reason, so the census still requires a
// sample of every variant that IS encodable.
//
// The optional `; read_gated SINCE: A => t, ..` clause names tags appended at
// wire version `SINCE` (a `*_FORMAT_VERSION` constant): the writer spells
// them like any other tag, and the reader accepts them only under a header of
// at least `SINCE`, so an older blob carrying one is refused with
// `InvalidTag` rather than silently decoded. The writer never emits one under
// an older header because the string collector raises the header for every
// instruction that carries one (`carries_inst_wire_batch_member`).
macro_rules! tag_enum {
    ($write:ident, $read:ident, $ty:ty, $( $variant:ident => $tag:expr ),+ $(,)?) => {
        tag_enum!(@impl $write, $read, $ty, [ $( $variant => $tag ),+ ], [], VERSION, []);
    };
    ($write:ident, $read:ident, $ty:ty, $( $variant:ident => $tag:expr ),+ ;
     unencodable $( $unencodable:ident ),+ $(,)?) => {
        tag_enum!(
            @impl $write, $read, $ty, [ $( $variant => $tag ),+ ], [ $( $unencodable ),+ ],
            VERSION, []
        );
    };
    ($write:ident, $read:ident, $ty:ty, $( $variant:ident => $tag:expr ),+ ;
     read_gated $since:ident: $( $gated:ident => $gtag:expr ),+ $(,)?) => {
        tag_enum!(
            @impl $write, $read, $ty, [ $( $variant => $tag ),+ ], [],
            $since, [ $( $gated => $gtag ),+ ]
        );
    };
    (@impl $write:ident, $read:ident, $ty:ty,
     [ $( $variant:ident => $tag:expr ),+ ], [ $( $unencodable:ident ),* ],
     $since:ident, [ $( $gated:ident => $gtag:expr ),* ]) => {
        fn $write(buf: &mut impl BinarySink, v: &$ty) {
            let tag: u8 = match v {
                $( <$ty>::$variant => $tag, )+
                $( <$ty>::$gated => $gtag, )*
                $( <$ty>::$unencodable => {
                    buf.refuse(WireRefusal::NoWireTag {
                        construct: concat!(stringify!($ty), "::", stringify!($unencodable)),
                        site: None,
                    });
                    return;
                } )*
            };
            write_u8(buf, tag);
        }

        fn $read(r: &mut Reader<'_>) -> Result<$ty, BinaryError> {
            let tag = r.read_u8()?;
            match tag {
                $( $tag => Ok(<$ty>::$variant), )+
                $( $gtag if r.version >= $since => Ok(<$ty>::$gated), )*
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
    BAnd => 20, BOr => 21, BXor => 22;
    // WS3.20 (F-057): the rotates and copySign, appended by the INST wire
    // batch (v51) and read-gated on it.
    read_gated INST_WIRE_BATCH_FORMAT_VERSION: RotL => 23, RotR => 24, FCopySign => 25,
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

#[cfg(test)]
mod inst_wire_batch_sub_op_tags {
    //! WS3.20 (F-057): the bit intrinsics `CtLz`/`CtTz`/`BSwap`/`BitReverse`
    //! and `RotL`/`RotR`/`FCopySign` carry the tags the INST wire batch (v51)
    //! appended, and those tags are READ-GATED: a blob whose header predates
    //! the batch cannot carry one (no older writer emitted it; the writer
    //! panicked instead), so a reader at an older version refuses the byte
    //! rather than decoding it. The whole-module half (the collector raises
    //! the header; the projections refuse) is
    //! `tests::inst_wire_batch_tags_are_read_gated`.

    use super::*;

    const BINOPS: [(BinOp, u8); 3] = [(BinOp::RotL, 23), (BinOp::RotR, 24), (BinOp::FCopySign, 25)];
    const UNOPS: [(UnOp, u8); 4] = [
        (UnOp::CtLz, 9),
        (UnOp::CtTz, 10),
        (UnOp::BSwap, 11),
        (UnOp::BitReverse, 12),
    ];

    fn reader_at(bytes: &[u8], version: u32) -> Reader<'_> {
        let mut reader = Reader::new(bytes);
        reader.version = version;
        reader
    }

    #[test]
    fn sub_op_tags_round_trip_at_the_batch_version_and_are_refused_below_it() {
        for (op, tag) in BINOPS {
            let mut buf = Vec::new();
            write_binop(&mut buf, &op);
            assert_eq!(buf, vec![tag], "{op:?} is BinOp tag {tag}");
            let mut reader = reader_at(&buf, INST_WIRE_BATCH_FORMAT_VERSION);
            assert_eq!(read_binop(&mut reader), Ok(op), "{op:?} must round-trip");
            let mut reader = reader_at(&buf, INST_WIRE_BATCH_FORMAT_VERSION - 1);
            assert_eq!(
                read_binop(&mut reader),
                Err(BinaryError::InvalidTag(tag)),
                "{op:?}'s tag under a pre-batch header must be refused"
            );
        }
        for (op, tag) in UNOPS {
            let mut buf = Vec::new();
            write_unop(&mut buf, &op);
            assert_eq!(buf, vec![tag], "{op:?} is UnOp tag {tag}");
            let mut reader = reader_at(&buf, INST_WIRE_BATCH_FORMAT_VERSION);
            assert_eq!(read_unop(&mut reader), Ok(op), "{op:?} must round-trip");
            let mut reader = reader_at(&buf, INST_WIRE_BATCH_FORMAT_VERSION - 1);
            assert_eq!(
                read_unop(&mut reader),
                Err(BinaryError::InvalidTag(tag)),
                "{op:?}'s tag under a pre-batch header must be refused"
            );
        }
        // The tags before the batch did not move.
        let mut buf = Vec::new();
        write_binop(&mut buf, &BinOp::BXor);
        write_unop(&mut buf, &UnOp::FTrunc);
        assert_eq!(buf, vec![22, 8]);
    }

    #[test]
    fn reader_refuses_the_next_free_unop_and_binop_tags() {
        // Next free tag of each space, derived from the writer so this test
        // never spells a number that a later landing would have to edit.
        let mut buf = Vec::new();
        write_unop(&mut buf, &UnOp::BitReverse);
        let next_unop = buf[0] + 1;
        let mut buf = Vec::new();
        write_binop(&mut buf, &BinOp::FCopySign);
        let next_binop = buf[0] + 1;

        let mut reader = reader_at(std::slice::from_ref(&next_unop), VERSION);
        assert_eq!(
            read_unop(&mut reader),
            Err(BinaryError::InvalidTag(next_unop)),
            "an unallocated UnOp tag must be refused, not decoded"
        );
        let mut reader = reader_at(std::slice::from_ref(&next_binop), VERSION);
        assert_eq!(
            read_binop(&mut reader),
            Err(BinaryError::InvalidTag(next_binop)),
            "an unallocated BinOp tag must be refused, not decoded"
        );
    }
}

tag_enum!(write_unop, read_unop, UnOp,
    Neg => 0, FNeg => 1, Not => 2, CtPop => 3, FAbs => 4, FSqrt => 5,
    FFloor => 6, FCeil => 7, FTrunc => 8;
    // WS3.20 (F-057): the bit intrinsics, appended by the INST wire batch
    // (v51) and read-gated on it.
    read_gated INST_WIRE_BATCH_FORMAT_VERSION: CtLz => 9, CtTz => 10, BSwap => 11,
        BitReverse => 12,
);

tag_enum!(write_overflow_op, read_overflow_op, OverflowOp,
    AddOverflow => 0, SubOverflow => 1, MulOverflow => 2,
);

// v52 (plan item P): the operation an `AssertKind::Overflow` guards. Only
// ever written inside a tag-63 assert, which is itself read-gated on v52.
tag_enum!(write_assert_overflow_op, read_assert_overflow_op, AssertOverflowOp,
    Add => 0, Sub => 1, Mul => 2, Div => 3, Rem => 4, Shl => 5, Shr => 6, Neg => 7,
);

/// v52 (plan item P): the kind of a tag-63 assert. `Unspecified` has NO byte
/// here: it is spelled by Inst tag 29, so the writer never reaches that arm
/// and the reader refuses every byte not listed below.
fn write_assert_kind(
    buf: &mut impl BinarySink,
    canonical: Option<&FunctionCanonicalPlan>,
    kind: &AssertKind,
) {
    match kind {
        AssertKind::Unspecified => panic!(
            "AssertKind::Unspecified has no AssertKind wire tag: a kindless assert is Inst tag 29"
        ),
        AssertKind::Overflow(op) => {
            write_u8(buf, 0);
            write_assert_overflow_op(buf, op);
        }
        AssertKind::DivByZero => write_u8(buf, 1),
        AssertKind::RemByZero => write_u8(buf, 2),
        AssertKind::BoundsCheck { index, len } => {
            write_u8(buf, 3);
            write_projected_value_id(buf, canonical, *index);
            write_projected_value_id(buf, canonical, *len);
        }
        AssertKind::MisalignedPtr { required, found } => {
            write_u8(buf, 4);
            write_projected_value_id(buf, canonical, *required);
            write_projected_value_id(buf, canonical, *found);
        }
        AssertKind::NullPtr => write_u8(buf, 5),
    }
}

/// v54 (amendment P): a panic site's location. 0 `Global` (a v32 global
/// id), 1 `Value` (a value id, projected so canonical renumbering covers it).
fn write_panic_location(
    buf: &mut impl BinarySink,
    canonical: Option<&FunctionCanonicalPlan>,
    location: &PanicLocation,
) {
    match location {
        PanicLocation::Global(global) => {
            write_u8(buf, 0);
            write_v32(buf, global.index());
        }
        PanicLocation::Value(value) => {
            write_u8(buf, 1);
            write_projected_value_id(buf, canonical, *value);
        }
    }
}

/// Any byte but 0 and 1 is `InvalidTag`: a consumer MUST refuse it rather
/// than read it as either location (`refuse/blob_panic_location_tag_unknown`).
fn read_panic_location(r: &mut Reader<'_>) -> Result<PanicLocation, BinaryError> {
    let tag = r.read_u8()?;
    match tag {
        0 => Ok(PanicLocation::Global(GlobalId::new(r.read_v32()?))),
        1 => Ok(PanicLocation::Value(r.read_value_id()?)),
        _ => Err(BinaryError::InvalidTag(tag)),
    }
}

/// v54 (amendment P): the payload of Inst tags 66 (a sited `Assert`) and 67
/// (`AssertInvoke`, which appends its successors): the condition, a
/// kind-presence byte (0 `Unspecified`, 1 an AssertKind follows — the
/// AssertKind tag space keeps having no byte for `Unspecified`), the kind,
/// the entry (written as a `Call` callee is), then the location.
fn write_sited_assert_payload(
    buf: &mut impl BinarySink,
    canonical: Option<&FunctionCanonicalPlan>,
    cond: ValueId,
    kind: &AssertKind,
    site: &PanicSite,
) {
    write_projected_value_id(buf, canonical, cond);
    if kind.is_unspecified() {
        write_u8(buf, 0);
    } else {
        write_u8(buf, 1);
        write_assert_kind(buf, canonical, kind);
    }
    write_func_id(buf, site.entry);
    write_panic_location(buf, canonical, &site.location);
}

fn read_sited_assert_payload(
    r: &mut Reader<'_>,
) -> Result<(ValueId, AssertKind, PanicSite), BinaryError> {
    let cond = r.read_value_id()?;
    let kind = match r.read_u8()? {
        0 => AssertKind::Unspecified,
        1 => read_assert_kind(r)?,
        presence => return Err(BinaryError::InvalidTag(presence)),
    };
    let entry = r.read_func_id()?;
    let location = read_panic_location(r)?;
    Ok((cond, kind, PanicSite { entry, location }))
}

fn read_assert_kind(r: &mut Reader<'_>) -> Result<AssertKind, BinaryError> {
    let tag = r.read_u8()?;
    match tag {
        0 => Ok(AssertKind::Overflow(read_assert_overflow_op(r)?)),
        1 => Ok(AssertKind::DivByZero),
        2 => Ok(AssertKind::RemByZero),
        3 => Ok(AssertKind::BoundsCheck {
            index: r.read_value_id()?,
            len: r.read_value_id()?,
        }),
        4 => Ok(AssertKind::MisalignedPtr {
            required: r.read_value_id()?,
            found: r.read_value_id()?,
        }),
        5 => Ok(AssertKind::NullPtr),
        _ => Err(BinaryError::InvalidTag(tag)),
    }
}

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

// HAND-ROLLED, not `tag_enum!`: v41's `Custom { namespace, name }` carries a
// payload the macro cannot match. Tags 0..=12 are byte-for-byte the macro's;
// 13..=15 are v41 and read-gated.
fn write_obligation_kind(
    buf: &mut impl BinarySink,
    pool: &SealedStringPool,
    kind: &ObligationKind,
) {
    match kind {
        ObligationKind::Precondition => write_u8(buf, 0),
        ObligationKind::Postcondition => write_u8(buf, 1),
        ObligationKind::LoopInvariant => write_u8(buf, 2),
        ObligationKind::TypeInvariant => write_u8(buf, 3),
        ObligationKind::RefinementType => write_u8(buf, 4),
        ObligationKind::TranslationValidation => write_u8(buf, 5),
        ObligationKind::MemorySafety => write_u8(buf, 6),
        ObligationKind::PanicFreedom => write_u8(buf, 7),
        ObligationKind::TemporalSafety => write_u8(buf, 8),
        ObligationKind::Liveness => write_u8(buf, 9),
        // Trust (trust-ir-spine item T1): panic-class routing-grade kinds.
        ObligationKind::ArithmeticSafety => write_u8(buf, 10),
        ObligationKind::BoundsCheck => write_u8(buf, 11),
        // Aeneas-style give-back refinement view (trust-ir-giveback).
        ObligationKind::GiveBackRefinement => write_u8(buf, 12),
        ObligationKind::Termination => write_u8(buf, 13),
        ObligationKind::Ownership => write_u8(buf, 14),
        ObligationKind::Custom { namespace, name } => {
            write_u8(buf, 15);
            write_str(buf, pool, namespace);
            write_str(buf, pool, name);
        }
    }
}

fn read_obligation_kind(r: &mut Reader<'_>) -> Result<ObligationKind, BinaryError> {
    Ok(match r.read_u8()? {
        0 => ObligationKind::Precondition,
        1 => ObligationKind::Postcondition,
        2 => ObligationKind::LoopInvariant,
        3 => ObligationKind::TypeInvariant,
        4 => ObligationKind::RefinementType,
        5 => ObligationKind::TranslationValidation,
        6 => ObligationKind::MemorySafety,
        7 => ObligationKind::PanicFreedom,
        8 => ObligationKind::TemporalSafety,
        9 => ObligationKind::Liveness,
        10 => ObligationKind::ArithmeticSafety,
        11 => ObligationKind::BoundsCheck,
        12 => ObligationKind::GiveBackRefinement,
        13 if r.version >= CONTRACT_SURFACE_FORMAT_VERSION => ObligationKind::Termination,
        14 if r.version >= CONTRACT_SURFACE_FORMAT_VERSION => ObligationKind::Ownership,
        15 if r.version >= CONTRACT_SURFACE_FORMAT_VERSION => ObligationKind::Custom {
            namespace: r.read_str()?,
            name: r.read_str()?,
        },
        tag => return Err(BinaryError::InvalidTag(tag)),
    })
}

tag_enum!(write_proof_status, read_proof_status, ProofStatus,
    Pending => 0, Discharged => 1, Failed => 2, Trusted => 3, Certified => 4,
);

// HAND-ROLLED, not `tag_enum!`: tags 5..=11 are v45 (WS3.12) and must be
// READ-GATED, which the macro's reader cannot express. Tags 0..=4 are the
// macro's bytes.
fn write_calling_conv(buf: &mut impl BinarySink, v: &CallingConv) {
    write_u8(
        buf,
        match v {
            CallingConv::C => 0,
            CallingConv::Fast => 1,
            CallingConv::Cold => 2,
            CallingConv::Rust => 3,
            CallingConv::Swift => 4,
            CallingConv::CUnwind => 5,
            CallingConv::SysV64 => 6,
            CallingConv::Win64 => 7,
            CallingConv::Aapcs => 8,
            CallingConv::EfiApi => 9,
            CallingConv::VectorCall => 10,
            CallingConv::RustCold => 11,
        },
    );
}

fn read_calling_conv(r: &mut Reader<'_>) -> Result<CallingConv, BinaryError> {
    Ok(match r.read_u8()? {
        0 => CallingConv::C,
        1 => CallingConv::Fast,
        2 => CallingConv::Cold,
        3 => CallingConv::Rust,
        4 => CallingConv::Swift,
        5 if r.version >= ABI_SURFACE_FORMAT_VERSION => CallingConv::CUnwind,
        6 if r.version >= ABI_SURFACE_FORMAT_VERSION => CallingConv::SysV64,
        7 if r.version >= ABI_SURFACE_FORMAT_VERSION => CallingConv::Win64,
        8 if r.version >= ABI_SURFACE_FORMAT_VERSION => CallingConv::Aapcs,
        9 if r.version >= ABI_SURFACE_FORMAT_VERSION => CallingConv::EfiApi,
        10 if r.version >= ABI_SURFACE_FORMAT_VERSION => CallingConv::VectorCall,
        11 if r.version >= ABI_SURFACE_FORMAT_VERSION => CallingConv::RustCold,
        tag => return Err(BinaryError::InvalidTag(tag)),
    })
}

tag_enum!(write_visibility, read_visibility, Visibility,
    Default => 0, Hidden => 1, Protected => 2,
);

// HAND-ROLLED, not `tag_enum!`: tags 5..=8 are v41 and must be READ-GATED,
// which the macro's reader cannot express. Tags 0..=4 are the macro's bytes.
fn write_linkage(buf: &mut impl BinarySink, v: &Linkage) {
    write_u8(
        buf,
        match v {
            Linkage::External => 0,
            Linkage::Internal => 1,
            Linkage::Private => 2,
            Linkage::Weak => 3,
            Linkage::LinkOnce => 4,
            Linkage::AvailableExternally => 5,
            Linkage::ExternalWeak => 6,
            Linkage::WeakOdr => 7,
            Linkage::LinkOnceOdr => 8,
        },
    );
}

fn read_linkage(r: &mut Reader<'_>) -> Result<Linkage, BinaryError> {
    Ok(match r.read_u8()? {
        0 => Linkage::External,
        1 => Linkage::Internal,
        2 => Linkage::Private,
        3 => Linkage::Weak,
        4 => Linkage::LinkOnce,
        5 if r.version >= CONTRACT_SURFACE_FORMAT_VERSION => Linkage::AvailableExternally,
        6 if r.version >= CONTRACT_SURFACE_FORMAT_VERSION => Linkage::ExternalWeak,
        7 if r.version >= CONTRACT_SURFACE_FORMAT_VERSION => Linkage::WeakOdr,
        8 if r.version >= CONTRACT_SURFACE_FORMAT_VERSION => Linkage::LinkOnceOdr,
        tag => return Err(BinaryError::InvalidTag(tag)),
    })
}

tag_enum!(write_tls_model, read_tls_model, TlsModel,
    LocalExec => 0, InitialExec => 1, GeneralDynamic => 2, LocalDynamic => 3,
);

tag_enum!(write_endianness, read_endianness, Endianness,
    Little => 0, Big => 1,
);

// ---------------------------------------------------------------------------
// Vec helpers
// ---------------------------------------------------------------------------

fn write_projected_value_id(
    buf: &mut impl BinarySink,
    canonical: Option<&FunctionCanonicalPlan>,
    id: ValueId,
) {
    write_value_id(
        buf,
        canonical.map_or(id, |projection| projection.map_value(id)),
    );
}

fn write_vec_value_id(
    buf: &mut impl BinarySink,
    canonical: Option<&FunctionCanonicalPlan>,
    ids: &[ValueId],
) {
    write_count(buf, "value-id list", ids.len());
    for id in ids {
        write_projected_value_id(buf, canonical, *id);
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

/// A tensor contraction's axis-pair list (v67): the count, then a `v32` left
/// axis and a `v32` right axis per pair, in list order. `what` names the
/// counted field in a count refusal.
fn write_axis_pairs(buf: &mut impl BinarySink, what: &'static str, pairs: &[(u32, u32)]) {
    write_count(buf, what, pairs.len());
    for &(lhs, rhs) in pairs {
        write_v32(buf, lhs);
        write_v32(buf, rhs);
    }
}

fn read_axis_pairs(r: &mut Reader<'_>) -> Result<Vec<(u32, u32)>, BinaryError> {
    let n = r.read_checked_len()?;
    let mut pairs = Vec::with_capacity(n);
    for _ in 0..n {
        let lhs = r.read_v32()?;
        let rhs = r.read_v32()?;
        pairs.push((lhs, rhs));
    }
    Ok(pairs)
}

/// A v32 list (v68: a tensor reduction's axes, a tensor view's shape and
/// index node lists): the count, then each item. `what` names the counted
/// field in a count refusal.
fn write_v32_list(buf: &mut impl BinarySink, what: &'static str, items: &[u32]) {
    write_count(buf, what, items.len());
    for &item in items {
        write_v32(buf, item);
    }
}

fn read_v32_list(r: &mut Reader<'_>) -> Result<Vec<u32>, BinaryError> {
    let n = r.read_checked_len()?;
    let mut items = Vec::with_capacity(n);
    for _ in 0..n {
        items.push(r.read_v32()?);
    }
    Ok(items)
}

/// One tensor map node (v68): its `TensorMapNode` tag byte, then the scalar
/// instruction's fields in that instruction's order, the operator by its
/// scalar wire tag and each lane a v32.
fn write_tensor_map_node<X: WireExt>(
    buf: &mut impl BinarySink,
    pool: &SealedStringPool,
    node: &crate::TensorMapNode<X>,
) {
    match node {
        crate::TensorMapNode::BinOp { op, ty, lhs, rhs } => {
            write_u8(buf, 0);
            write_binop(buf, op);
            write_ty(buf, pool, ty);
            write_v32(buf, *lhs);
            write_v32(buf, *rhs);
        }
        crate::TensorMapNode::UnOp { op, ty, operand } => {
            write_u8(buf, 1);
            write_unop(buf, op);
            write_ty(buf, pool, ty);
            write_v32(buf, *operand);
        }
        crate::TensorMapNode::ICmp { op, ty, lhs, rhs } => {
            write_u8(buf, 2);
            write_icmp_op(buf, op);
            write_ty(buf, pool, ty);
            write_v32(buf, *lhs);
            write_v32(buf, *rhs);
        }
        crate::TensorMapNode::Select {
            ty,
            cond,
            then_lane,
            else_lane,
        } => {
            write_u8(buf, 3);
            write_ty(buf, pool, ty);
            write_v32(buf, *cond);
            write_v32(buf, *then_lane);
            write_v32(buf, *else_lane);
        }
        crate::TensorMapNode::Cast {
            op,
            src_ty,
            dst_ty,
            operand,
        } => {
            write_u8(buf, 4);
            write_cast_op(buf, op);
            write_ty(buf, pool, src_ty);
            write_ty(buf, pool, dst_ty);
            write_v32(buf, *operand);
        }
    }
}

fn read_tensor_map_node<X: WireExt>(
    r: &mut Reader<'_>,
) -> Result<crate::TensorMapNode<X>, BinaryError> {
    let tag = r.read_u8()?;
    Ok(match tag {
        0 => crate::TensorMapNode::BinOp {
            op: read_binop(r)?,
            ty: read_ty(r)?,
            lhs: r.read_v32()?,
            rhs: r.read_v32()?,
        },
        1 => crate::TensorMapNode::UnOp {
            op: read_unop(r)?,
            ty: read_ty(r)?,
            operand: r.read_v32()?,
        },
        2 => crate::TensorMapNode::ICmp {
            op: read_icmp_op(r)?,
            ty: read_ty(r)?,
            lhs: r.read_v32()?,
            rhs: r.read_v32()?,
        },
        3 => crate::TensorMapNode::Select {
            ty: read_ty(r)?,
            cond: r.read_v32()?,
            then_lane: r.read_v32()?,
            else_lane: r.read_v32()?,
        },
        4 => crate::TensorMapNode::Cast {
            op: read_cast_op(r)?,
            src_ty: read_ty(r)?,
            dst_ty: read_ty(r)?,
            operand: r.read_v32()?,
        },
        t => return Err(BinaryError::InvalidTag(t)),
    })
}

/// A `TensorReduceOp` (v68) by its tag, in declaration order.
fn tensor_reduce_op_tag(op: crate::TensorReduceOp) -> u8 {
    match op {
        crate::TensorReduceOp::Add => 0,
        crate::TensorReduceOp::Mul => 1,
        crate::TensorReduceOp::And => 2,
        crate::TensorReduceOp::Or => 3,
        crate::TensorReduceOp::Xor => 4,
        crate::TensorReduceOp::SMin => 5,
        crate::TensorReduceOp::SMax => 6,
        crate::TensorReduceOp::UMin => 7,
        crate::TensorReduceOp::UMax => 8,
    }
}

fn read_tensor_reduce_op(r: &mut Reader<'_>) -> Result<crate::TensorReduceOp, BinaryError> {
    Ok(match r.read_u8()? {
        0 => crate::TensorReduceOp::Add,
        1 => crate::TensorReduceOp::Mul,
        2 => crate::TensorReduceOp::And,
        3 => crate::TensorReduceOp::Or,
        4 => crate::TensorReduceOp::Xor,
        5 => crate::TensorReduceOp::SMin,
        6 => crate::TensorReduceOp::SMax,
        7 => crate::TensorReduceOp::UMin,
        8 => crate::TensorReduceOp::UMax,
        t => return Err(BinaryError::InvalidTag(t)),
    })
}

fn read_tensor_reduce_order(r: &mut Reader<'_>) -> Result<crate::TensorReduceOrder, BinaryError> {
    match r.read_u8()? {
        0 => Ok(crate::TensorReduceOrder::RowMajor),
        t => Err(BinaryError::InvalidTag(t)),
    }
}

/// One tensor view node (v68): its `TensorIndexExpr` tag byte, then a v64
/// literal, a v32 index, or two v32 node ids.
fn write_tensor_index_expr(buf: &mut impl BinarySink, expr: &crate::TensorIndexExpr) {
    write_u8(buf, tensor_index_expr_tag(expr));
    match *expr {
        crate::TensorIndexExpr::Lit(n) => write_v64(buf, n),
        crate::TensorIndexExpr::Param(k)
        | crate::TensorIndexExpr::SrcExtent(k)
        | crate::TensorIndexExpr::Coord(k) => write_v32(buf, k),
        crate::TensorIndexExpr::Add(a, b)
        | crate::TensorIndexExpr::Sub(a, b)
        | crate::TensorIndexExpr::Mul(a, b)
        | crate::TensorIndexExpr::Div(a, b)
        | crate::TensorIndexExpr::Rem(a, b)
        | crate::TensorIndexExpr::Min(a, b)
        | crate::TensorIndexExpr::Max(a, b) => {
            write_v32(buf, a);
            write_v32(buf, b);
        }
    }
}

/// A `TensorIndexExpr`'s tag (v68), in declaration order.
fn tensor_index_expr_tag(expr: &crate::TensorIndexExpr) -> u8 {
    match expr {
        crate::TensorIndexExpr::Lit(_) => 0,
        crate::TensorIndexExpr::Param(_) => 1,
        crate::TensorIndexExpr::SrcExtent(_) => 2,
        crate::TensorIndexExpr::Coord(_) => 3,
        crate::TensorIndexExpr::Add(..) => 4,
        crate::TensorIndexExpr::Sub(..) => 5,
        crate::TensorIndexExpr::Mul(..) => 6,
        crate::TensorIndexExpr::Div(..) => 7,
        crate::TensorIndexExpr::Rem(..) => 8,
        crate::TensorIndexExpr::Min(..) => 9,
        crate::TensorIndexExpr::Max(..) => 10,
    }
}

fn read_tensor_index_expr(r: &mut Reader<'_>) -> Result<crate::TensorIndexExpr, BinaryError> {
    let tag = r.read_u8()?;
    Ok(match tag {
        0 => crate::TensorIndexExpr::Lit(r.read_v64()?),
        1 => crate::TensorIndexExpr::Param(r.read_v32()?),
        2 => crate::TensorIndexExpr::SrcExtent(r.read_v32()?),
        3 => crate::TensorIndexExpr::Coord(r.read_v32()?),
        4..=10 => {
            let a = r.read_v32()?;
            let b = r.read_v32()?;
            match tag {
                4 => crate::TensorIndexExpr::Add(a, b),
                5 => crate::TensorIndexExpr::Sub(a, b),
                6 => crate::TensorIndexExpr::Mul(a, b),
                7 => crate::TensorIndexExpr::Div(a, b),
                8 => crate::TensorIndexExpr::Rem(a, b),
                9 => crate::TensorIndexExpr::Min(a, b),
                _ => crate::TensorIndexExpr::Max(a, b),
            }
        }
        t => return Err(BinaryError::InvalidTag(t)),
    })
}

// ---------------------------------------------------------------------------
// Inst
// ---------------------------------------------------------------------------

fn write_inst<X: WireExt>(
    buf: &mut impl BinarySink,
    pool: &SealedStringPool,
    canonical: Option<&FunctionCanonicalPlan>,
    inst: &InstG<X>,
) {
    match inst {
        InstG::BinOp { op, ty, lhs, rhs } => {
            write_u8(buf, 0);
            write_binop(buf, op);
            write_ty(buf, pool, ty);
            write_projected_value_id(buf, canonical, *lhs);
            write_projected_value_id(buf, canonical, *rhs);
        }
        InstG::UnOp { op, ty, operand } => {
            write_u8(buf, 1);
            write_unop(buf, op);
            write_ty(buf, pool, ty);
            write_projected_value_id(buf, canonical, *operand);
        }
        InstG::Overflow { op, ty, lhs, rhs } => {
            write_u8(buf, 2);
            write_overflow_op(buf, op);
            write_ty(buf, pool, ty);
            write_projected_value_id(buf, canonical, *lhs);
            write_projected_value_id(buf, canonical, *rhs);
        }
        InstG::ICmp { op, ty, lhs, rhs } => {
            write_u8(buf, 3);
            write_icmp_op(buf, op);
            write_ty(buf, pool, ty);
            write_projected_value_id(buf, canonical, *lhs);
            write_projected_value_id(buf, canonical, *rhs);
        }
        InstG::FCmp { op, ty, lhs, rhs } => {
            write_u8(buf, 4);
            write_fcmp_op(buf, op);
            write_ty(buf, pool, ty);
            write_projected_value_id(buf, canonical, *lhs);
            write_projected_value_id(buf, canonical, *rhs);
        }
        InstG::Cast {
            op,
            src_ty,
            dst_ty,
            operand,
        } => {
            write_u8(buf, 5);
            write_cast_op(buf, op);
            write_ty(buf, pool, src_ty);
            write_ty(buf, pool, dst_ty);
            write_projected_value_id(buf, canonical, *operand);
        }
        InstG::Load {
            ty,
            ptr,
            volatile,
            align,
        } => {
            write_u8(buf, 6);
            write_ty(buf, pool, ty);
            write_projected_value_id(buf, canonical, *ptr);
            write_bool(buf, *volatile);
            write_opt_u64(buf, *align);
        }
        InstG::Store {
            ty,
            ptr,
            value,
            volatile,
            align,
        } => {
            write_u8(buf, 7);
            write_ty(buf, pool, ty);
            write_projected_value_id(buf, canonical, *ptr);
            write_projected_value_id(buf, canonical, *value);
            write_bool(buf, *volatile);
            write_opt_u64(buf, *align);
        }
        InstG::Drop { ty, ptr } => {
            // Crystal lane (wave-DS): tag 57, the first free instruction byte. Read-gated on
            // v47 (`DROP_INST_FORMAT_VERSION`), so a blob CLAIMING an older version that
            // carries it is malformed and refused rather than silently promoted -- the
            // discipline the v37 `Untagged` tag records.
            write_u8(buf, 57);
            write_ty(buf, pool, ty);
            write_projected_value_id(buf, canonical, *ptr);
        }
        // v55 (amendment D): `Drop`'s payload, then `Invoke`'s successor
        // fields in `Invoke`'s order.
        InstG::DropInvoke {
            ty,
            ptr,
            normal_dest,
            normal_args,
            unwind_dest,
        } => {
            write_u8(buf, 68);
            write_ty(buf, pool, ty);
            write_projected_value_id(buf, canonical, *ptr);
            write_block_id(buf, *normal_dest);
            write_vec_value_id(buf, canonical, normal_args);
            write_block_id(buf, *unwind_dest);
        }
        InstG::Alloca { ty, count, align } => {
            write_u8(buf, 8);
            write_ty(buf, pool, ty);
            match count {
                None => write_u8(buf, 0),
                Some(v) => {
                    write_u8(buf, 1);
                    write_projected_value_id(buf, canonical, *v);
                }
            }
            write_opt_u64(buf, *align);
        }
        InstG::HeapAlloc {
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
                    write_projected_value_id(buf, canonical, *v);
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
        InstG::GEP {
            pointee_ty,
            base,
            indices,
            inbounds,
        } => {
            write_u8(buf, 9);
            write_ty(buf, pool, pointee_ty);
            write_projected_value_id(buf, canonical, *base);
            write_vec_value_id(buf, canonical, indices);
            write_bool(buf, *inbounds);
        }
        InstG::AtomicLoad { ty, ptr, ordering } => {
            write_u8(buf, 10);
            write_ty(buf, pool, ty);
            write_projected_value_id(buf, canonical, *ptr);
            write_ordering(buf, ordering);
        }
        InstG::AtomicStore {
            ty,
            ptr,
            value,
            ordering,
        } => {
            write_u8(buf, 11);
            write_ty(buf, pool, ty);
            write_projected_value_id(buf, canonical, *ptr);
            write_projected_value_id(buf, canonical, *value);
            write_ordering(buf, ordering);
        }
        InstG::AtomicRMW {
            op,
            ty,
            ptr,
            value,
            ordering,
        } => {
            write_u8(buf, 12);
            write_atomic_rmw_op(buf, op);
            write_ty(buf, pool, ty);
            write_projected_value_id(buf, canonical, *ptr);
            write_projected_value_id(buf, canonical, *value);
            write_ordering(buf, ordering);
        }
        InstG::CmpXchg {
            ty,
            ptr,
            expected,
            desired,
            success,
            failure,
            weak,
        } => {
            // Crystal lane (D3): the strength is the TAG, not a trailing byte, so a strong
            // compare-exchange keeps tag 13 and its exact historical bytes. A weak one takes
            // tag 58, read-gated on v48: a blob CLAIMING an older version that carries it is
            // malformed and refused rather than silently read as strong -- which would delete
            // the spurious-failure executions the flag exists to keep.
            write_u8(buf, if *weak { 58 } else { 13 });
            write_ty(buf, pool, ty);
            write_projected_value_id(buf, canonical, *ptr);
            write_projected_value_id(buf, canonical, *expected);
            write_projected_value_id(buf, canonical, *desired);
            write_ordering(buf, success);
            write_ordering(buf, failure);
        }
        InstG::Fence { ordering } => {
            write_u8(buf, 14);
            write_ordering(buf, ordering);
        }
        InstG::Br { target, args } => {
            write_u8(buf, 15);
            write_block_id(buf, *target);
            write_vec_value_id(buf, canonical, args);
        }
        InstG::CondBr {
            cond,
            then_target,
            then_args,
            else_target,
            else_args,
        } => {
            write_u8(buf, 16);
            write_projected_value_id(buf, canonical, *cond);
            write_block_id(buf, *then_target);
            write_vec_value_id(buf, canonical, then_args);
            write_block_id(buf, *else_target);
            write_vec_value_id(buf, canonical, else_args);
        }
        InstG::Switch {
            value,
            default,
            default_args,
            cases,
            exhaustive_enum_unreachable,
        } => {
            write_u8(buf, 17);
            write_projected_value_id(buf, canonical, *value);
            write_block_id(buf, *default);
            write_vec_value_id(buf, canonical, default_args);
            write_count(buf, "Switch cases", cases.len());
            for sc in cases {
                write_constant(buf, pool, &sc.value);
                write_v32(buf, sc.target.0);
                write_vec_value_id(buf, canonical, &sc.args);
            }
            // v15+: exhaustive-enum-unreachable flag; legacy modules default false.
            write_bool(buf, *exhaustive_enum_unreachable);
        }
        InstG::Call { callee, args } => {
            write_u8(buf, 18);
            write_func_id(buf, *callee);
            write_vec_value_id(buf, canonical, args);
        }
        InstG::CallCannotUnwind { callee, args } => {
            write_u8(buf, 64);
            write_func_id(buf, *callee);
            write_vec_value_id(buf, canonical, args);
        }
        InstG::CallIndirectCannotUnwind {
            callee,
            sig,
            args,
            calling_conv,
        } => {
            write_u8(buf, 65);
            write_projected_value_id(buf, canonical, *callee);
            write_func_ty_id(buf, *sig);
            write_vec_value_id(buf, canonical, args);
            write_calling_conv(buf, calling_conv);
        }
        InstG::CallIndirect {
            callee,
            sig,
            args,
            calling_conv,
        } => {
            write_u8(buf, 19);
            write_projected_value_id(buf, canonical, *callee);
            write_func_ty_id(buf, *sig);
            write_vec_value_id(buf, canonical, args);
            // VERSION >= 12: indirect-call ABI. Read side defaults C on older.
            write_calling_conv(buf, calling_conv);
        }
        InstG::Return { values } => {
            write_u8(buf, 20);
            write_vec_value_id(buf, canonical, values);
        }
        InstG::ExtractField {
            ty,
            aggregate,
            field,
        } => {
            write_u8(buf, 21);
            write_ty(buf, pool, ty);
            write_projected_value_id(buf, canonical, *aggregate);
            write_v32(buf, *field);
        }
        InstG::InsertField {
            ty,
            aggregate,
            field,
            value,
        } => {
            write_u8(buf, 22);
            write_ty(buf, pool, ty);
            write_projected_value_id(buf, canonical, *aggregate);
            write_v32(buf, *field);
            write_projected_value_id(buf, canonical, *value);
        }
        InstG::ExtractElement { ty, array, index } => {
            write_u8(buf, 23);
            write_ty(buf, pool, ty);
            write_projected_value_id(buf, canonical, *array);
            write_projected_value_id(buf, canonical, *index);
        }
        InstG::InsertElement {
            ty,
            array,
            index,
            value,
        } => {
            write_u8(buf, 24);
            write_ty(buf, pool, ty);
            write_projected_value_id(buf, canonical, *array);
            write_projected_value_id(buf, canonical, *index);
            write_projected_value_id(buf, canonical, *value);
        }
        InstG::Const { ty, value } => {
            write_u8(buf, 25);
            write_ty(buf, pool, ty);
            write_constant(buf, pool, value);
        }
        InstG::NullPtr => write_u8(buf, 26),
        InstG::GlobalAddr { global } => {
            write_u8(buf, 48);
            write_v32(buf, global.index());
        }
        InstG::Undef { ty } => {
            write_u8(buf, 27);
            write_ty(buf, pool, ty);
        }
        InstG::Assume { cond } => {
            write_u8(buf, 28);
            write_projected_value_id(buf, canonical, *cond);
        }
        // v52 (plan item P): a kindless assert keeps tag 29 and its exact
        // historical bytes; a kinded one is tag 63, the condition, then the
        // kind (`write_assert_kind`). One spelling per value: tag 63 never
        // carries `Unspecified` (the kind tag space has no byte for it).
        //
        // v54 (amendment P): a SITED assert of any kind is tag 66 — the
        // condition, a kind-presence byte (0 Unspecified, 1 a kind follows),
        // the kind, then the panic site (`write_panic_site`). Tags 29 and 63
        // spell only siteless asserts, so each assert has one encoding.
        InstG::Assert {
            cond,
            kind,
            site: None,
        } if kind.is_unspecified() => {
            write_u8(buf, 29);
            write_projected_value_id(buf, canonical, *cond);
        }
        InstG::Assert {
            cond,
            kind,
            site: None,
        } => {
            write_u8(buf, 63);
            write_projected_value_id(buf, canonical, *cond);
            write_assert_kind(buf, canonical, kind);
        }
        InstG::Assert {
            cond,
            kind,
            site: Some(site),
        } => {
            write_u8(buf, 66);
            write_sited_assert_payload(buf, canonical, *cond, kind, site);
        }
        // v54 (amendment P): tag 66's payload, then `Invoke`'s successor
        // fields in `Invoke`'s order.
        InstG::AssertInvoke {
            cond,
            kind,
            site,
            normal_dest,
            normal_args,
            unwind_dest,
        } => {
            write_u8(buf, 67);
            write_sited_assert_payload(buf, canonical, *cond, kind, site);
            write_block_id(buf, *normal_dest);
            write_vec_value_id(buf, canonical, normal_args);
            write_block_id(buf, *unwind_dest);
        }
        InstG::Unreachable => write_u8(buf, 30),
        InstG::Copy { ty, operand } => {
            write_u8(buf, 31);
            write_ty(buf, pool, ty);
            write_projected_value_id(buf, canonical, *operand);
        }
        InstG::Select {
            ty,
            cond,
            then_val,
            else_val,
        } => {
            write_u8(buf, 32);
            write_ty(buf, pool, ty);
            write_projected_value_id(buf, canonical, *cond);
            write_projected_value_id(buf, canonical, *then_val);
            write_projected_value_id(buf, canonical, *else_val);
        }
        InstG::Borrow { ptr } => {
            write_u8(buf, 33);
            write_projected_value_id(buf, canonical, *ptr);
        }
        InstG::BorrowMut { ptr } => {
            write_u8(buf, 34);
            write_projected_value_id(buf, canonical, *ptr);
        }
        InstG::EndBorrow { borrow_ptr } => {
            write_u8(buf, 35);
            write_projected_value_id(buf, canonical, *borrow_ptr);
        }
        InstG::Retain { ptr } => {
            write_u8(buf, 36);
            write_projected_value_id(buf, canonical, *ptr);
        }
        InstG::Release { ptr } => {
            write_u8(buf, 37);
            write_projected_value_id(buf, canonical, *ptr);
        }
        InstG::IsUnique { ptr } => {
            write_u8(buf, 38);
            write_projected_value_id(buf, canonical, *ptr);
        }
        InstG::Dealloc { ptr } => {
            write_u8(buf, 39);
            write_projected_value_id(buf, canonical, *ptr);
        }
        // Binding frames (tags 40..=43)
        InstG::OpenFrame { def } => {
            write_u8(buf, 40);
            write_v32(buf, def.id.index());
            write_str(buf, pool, &def.name);
            write_count(buf, "BindingFrameDef.slots", def.slots.len());
            for slot in &def.slots {
                write_str(buf, pool, &slot.name);
                write_ty(buf, pool, &slot.ty);
            }
        }
        // Every `frame` below is an SSA handle, not the `BindingFrameId`
        // definition embedded by `OpenFrame`, so canonical projections remap it.
        InstG::BindSlot { frame, slot, value } => {
            write_u8(buf, 41);
            write_projected_value_id(buf, canonical, *frame);
            write_v32(buf, *slot);
            write_projected_value_id(buf, canonical, *value);
        }
        InstG::LoadSlot { frame, slot, ty } => {
            write_u8(buf, 42);
            write_projected_value_id(buf, canonical, *frame);
            write_v32(buf, *slot);
            write_ty(buf, pool, ty);
        }
        InstG::CloseFrame { frame } => {
            write_u8(buf, 43);
            write_projected_value_id(buf, canonical, *frame);
        }
        // Coroutine suspend (tag 50, v16+). New wire tags are never present in
        // pre-v16 blobs, so no read-side version gate is needed.
        InstG::CoroSuspend {
            frame,
            state_slot,
            next_state,
            value,
        } => {
            write_u8(buf, 50);
            write_projected_value_id(buf, canonical, *frame);
            write_v32(buf, *state_slot);
            write_i128(buf, i128::from(*next_state));
            write_projected_value_id(buf, canonical, *value);
        }
        // Exception handling (tags 51..=53, v17+). New wire tags are never
        // present in pre-v17 blobs, so no read-side version gate is needed.
        InstG::Invoke {
            callee,
            args,
            normal_dest,
            normal_args,
            unwind_dest,
        } => {
            write_u8(buf, 51);
            write_func_id(buf, *callee);
            write_vec_value_id(buf, canonical, args);
            write_block_id(buf, *normal_dest);
            write_vec_value_id(buf, canonical, normal_args);
            write_block_id(buf, *unwind_dest);
        }
        // v56 (amendment D, Part 2): `CallIndirect`'s tag-19 payload, then
        // `Invoke`'s successor fields in `Invoke`'s order.
        InstG::InvokeIndirect {
            callee,
            sig,
            args,
            calling_conv,
            normal_dest,
            normal_args,
            unwind_dest,
        } => {
            write_u8(buf, 69);
            write_projected_value_id(buf, canonical, *callee);
            write_func_ty_id(buf, *sig);
            write_vec_value_id(buf, canonical, args);
            write_calling_conv(buf, calling_conv);
            write_block_id(buf, *normal_dest);
            write_vec_value_id(buf, canonical, normal_args);
            write_block_id(buf, *unwind_dest);
        }
        InstG::LandingPad {
            is_cleanup,
            catch_type_indices,
        } => {
            write_u8(buf, 52);
            write_bool(buf, *is_cleanup);
            write_count(
                buf,
                "LandingPad catch_type_indices",
                catch_type_indices.len(),
            );
            for idx in catch_type_indices {
                write_v32(buf, *idx);
            }
        }
        InstG::Resume { exn } => {
            write_u8(buf, 53);
            write_projected_value_id(buf, canonical, *exn);
        }
        InstG::SeqMapAddK { ty, seq, k } => {
            write_u8(buf, 54);
            write_ty(buf, pool, ty);
            write_projected_value_id(buf, canonical, *seq);
            write_u64(buf, *k);
        }
        InstG::SeqMapNot { ty, seq } => {
            write_u8(buf, 55);
            write_ty(buf, pool, ty);
            write_projected_value_id(buf, canonical, *seq);
        }
        InstG::SeqMap { ty, seq, fwd } => {
            // VERSION >= 21: general element-op loop (ty + seq + element FuncId).
            write_u8(buf, 56);
            write_ty(buf, pool, ty);
            write_projected_value_id(buf, canonical, *seq);
            write_func_id(buf, *fwd);
        }
        // v50: `n` copies of one operand — the type carries `n`.
        InstG::ArraySplat { ty, value } => {
            write_u8(buf, 59);
            write_ty(buf, pool, ty);
            write_projected_value_id(buf, canonical, *value);
        }
        // v51 (INST wire batch, WS3.5): the aggregate type, the enum variant
        // as a presence byte plus a v32, then one operand per lane.
        InstG::MakeAggregate {
            ty,
            variant,
            fields,
        } => {
            write_u8(buf, 60);
            write_ty(buf, pool, ty);
            write_opt_v32(buf, *variant);
            write_vec_value_id(buf, canonical, fields);
        }
        InstG::MakeClosure { ty, func, captures } => {
            write_u8(buf, 70);
            write_closure_ty_id(buf, *ty);
            write_func_id(buf, *func);
            write_vec_value_id(buf, canonical, captures);
        }
        // v67 (tensor region): the result type, the operands in field order,
        // then the batch and the contracted axis-pair lists.
        InstG::TensorContract {
            ty,
            lhs,
            rhs,
            batch,
            contract,
        } => {
            write_u8(buf, 71);
            write_ty(buf, pool, ty);
            write_projected_value_id(buf, canonical, *lhs);
            write_projected_value_id(buf, canonical, *rhs);
            write_axis_pairs(buf, "TensorContract batch pairs", batch);
            write_axis_pairs(buf, "TensorContract contract pairs", contract);
        }
        // v68 (tensor map, reduce and view): every field in declaration order.
        InstG::TensorMap { ty, args, body } => {
            write_u8(buf, 72);
            write_ty(buf, pool, ty);
            write_vec_value_id(buf, canonical, args);
            write_count(buf, "TensorMap body", body.len());
            for node in body {
                write_tensor_map_node(buf, pool, node);
            }
        }
        InstG::TensorReduce {
            ty,
            src,
            op,
            axes,
            order,
        } => {
            write_u8(buf, 73);
            write_ty(buf, pool, ty);
            write_projected_value_id(buf, canonical, *src);
            write_u8(buf, tensor_reduce_op_tag(*op));
            write_v32_list(buf, "TensorReduce axes", axes);
            match order {
                crate::TensorReduceOrder::RowMajor => write_u8(buf, 0),
            }
        }
        InstG::TensorView {
            ty,
            src,
            params,
            exprs,
            shape,
            index,
            fill,
        } => {
            write_u8(buf, 74);
            write_ty(buf, pool, ty);
            write_projected_value_id(buf, canonical, *src);
            write_vec_value_id(buf, canonical, params);
            write_count(buf, "TensorView exprs", exprs.len());
            for expr in exprs {
                write_tensor_index_expr(buf, expr);
            }
            write_v32_list(buf, "TensorView shape", shape);
            write_v32_list(buf, "TensorView index", index);
            match fill {
                None => write_u8(buf, 0),
                Some(fill) => {
                    write_u8(buf, 1);
                    write_projected_value_id(buf, canonical, *fill);
                }
            }
        }
        // v69 (tensor gather and scatter): every field in declaration order,
        // `coords` a counted value-id list.
        InstG::TensorGather { ty, data, coords } => {
            write_u8(buf, 75);
            write_ty(buf, pool, ty);
            write_projected_value_id(buf, canonical, *data);
            write_vec_value_id(buf, canonical, coords);
        }
        InstG::TensorScatter {
            ty,
            init,
            src,
            coords,
        } => {
            write_u8(buf, 76);
            write_ty(buf, pool, ty);
            write_projected_value_id(buf, canonical, *init);
            write_projected_value_id(buf, canonical, *src);
            write_vec_value_id(buf, canonical, coords);
        }
        InstG::DialectOp(op) => {
            write_u8(buf, 44);
            write_dialect_inst(buf, pool, canonical, op);
        }
        InstG::PtrData { ptr_ty, ptr } => {
            write_u8(buf, 45);
            write_ty(buf, pool, ptr_ty);
            write_projected_value_id(buf, canonical, *ptr);
        }
        InstG::PtrMetadata {
            ptr_ty,
            metadata_ty,
            ptr,
        } => {
            write_u8(buf, 46);
            write_ty(buf, pool, ptr_ty);
            write_ty(buf, pool, metadata_ty);
            write_projected_value_id(buf, canonical, *ptr);
        }
        InstG::PtrFromParts {
            ptr_ty,
            metadata_ty,
            data,
            metadata,
        } => {
            write_u8(buf, 47);
            write_ty(buf, pool, ptr_ty);
            write_ty(buf, pool, metadata_ty);
            write_projected_value_id(buf, canonical, *data);
            write_projected_value_id(buf, canonical, *metadata);
        }
        // v51 (INST wire batch, WS3.20): the three operands in field order,
        // then the memmove flag.
        InstG::MemCopy {
            dst,
            src,
            bytes,
            overlap,
        } => {
            write_u8(buf, 61);
            write_projected_value_id(buf, canonical, *dst);
            write_projected_value_id(buf, canonical, *src);
            write_projected_value_id(buf, canonical, *bytes);
            write_bool(buf, *overlap);
        }
        // v51 (INST wire batch, WS3.20): the three operands in field order.
        InstG::MemSet { dst, byte, bytes } => {
            write_u8(buf, 62);
            write_projected_value_id(buf, canonical, *dst);
            write_projected_value_id(buf, canonical, *byte);
            write_projected_value_id(buf, canonical, *bytes);
        }
    }
}

fn write_dialect_inst(
    buf: &mut impl BinarySink,
    pool: &SealedStringPool,
    canonical: Option<&FunctionCanonicalPlan>,
    op: &crate::dialect::DialectInst,
) {
    write_str(buf, pool, &op.dialect);
    write_str(buf, pool, &op.op);
    write_vec_value_id(buf, canonical, &op.operands);
    write_count(buf, "DialectInst.result_tys", op.result_tys.len());
    for t in &op.result_tys {
        write_ty(buf, pool, t);
    }
    write_count(buf, "DialectInst.attrs", op.attrs.len());
    for entry in &op.attrs {
        write_str(buf, pool, &entry.name);
        write_attr_value(buf, pool, &entry.value);
    }
    write_v32(buf, op.version);
}

fn write_attr_value(
    buf: &mut impl BinarySink,
    pool: &SealedStringPool,
    v: &crate::dialect::AttrValue,
) {
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
        0 => AttrValue::I64(i64::from_le_bytes(r.read_array()?)),
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

fn read_inst<X: WireExt>(r: &mut Reader<'_>) -> Result<InstG<X>, BinaryError> {
    let tag = r.read_u8()?;
    match tag {
        0 => Ok(InstG::BinOp {
            op: read_binop(r)?,
            ty: read_ty(r)?,
            lhs: r.read_value_id()?,
            rhs: r.read_value_id()?,
        }),
        1 => Ok(InstG::UnOp {
            op: read_unop(r)?,
            ty: read_ty(r)?,
            operand: r.read_value_id()?,
        }),
        2 => Ok(InstG::Overflow {
            op: read_overflow_op(r)?,
            ty: read_ty(r)?,
            lhs: r.read_value_id()?,
            rhs: r.read_value_id()?,
        }),
        3 => Ok(InstG::ICmp {
            op: read_icmp_op(r)?,
            ty: read_ty(r)?,
            lhs: r.read_value_id()?,
            rhs: r.read_value_id()?,
        }),
        4 => Ok(InstG::FCmp {
            op: read_fcmp_op(r)?,
            ty: read_ty(r)?,
            lhs: r.read_value_id()?,
            rhs: r.read_value_id()?,
        }),
        5 => Ok(InstG::Cast {
            op: read_cast_op(r)?,
            src_ty: read_ty(r)?,
            dst_ty: read_ty(r)?,
            operand: r.read_value_id()?,
        }),
        6 => Ok(InstG::Load {
            ty: read_ty(r)?,
            ptr: r.read_value_id()?,
            volatile: r.read_bool()?,
            align: read_opt_u64(r)?,
        }),
        7 => Ok(InstG::Store {
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
            Ok(InstG::Alloca { ty, count, align })
        }
        57 if r.version >= DROP_INST_FORMAT_VERSION => {
            let ty = read_ty(r)?;
            let ptr = r.read_value_id()?;
            Ok(InstG::Drop { ty, ptr })
        }
        // v55 (amendment D): read-gated, so an older header carrying tag 68
        // is `InvalidTag` (the tag-57 discipline).
        68 if r.version >= DROP_GLUE_FORMAT_VERSION => Ok(InstG::DropInvoke {
            ty: read_ty(r)?,
            ptr: r.read_value_id()?,
            normal_dest: r.read_block_id()?,
            normal_args: read_vec_value_id(r)?,
            unwind_dest: r.read_block_id()?,
        }),
        // v56 (amendment D, Part 2): `InvokeIndirect`, read-gated; below its
        // version the tag falls through to `InvalidTag(69)`.
        69 if r.version >= UNWIND_TWINS_FORMAT_VERSION => Ok(InstG::InvokeIndirect {
            callee: r.read_value_id()?,
            sig: r.read_func_ty_id()?,
            args: read_vec_value_id(r)?,
            calling_conv: read_calling_conv(r)?,
            normal_dest: r.read_block_id()?,
            normal_args: read_vec_value_id(r)?,
            unwind_dest: r.read_block_id()?,
        }),
        // Crystal lane (D3): a WEAK compare-exchange -- tag 13's payload, read-gated on v48.
        58 if r.version >= WEAK_CMPXCHG_FORMAT_VERSION => Ok(InstG::CmpXchg {
            ty: read_ty(r)?,
            ptr: r.read_value_id()?,
            expected: r.read_value_id()?,
            desired: r.read_value_id()?,
            success: read_ordering(r)?,
            failure: read_ordering(r)?,
            weak: true,
        }),
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
            Ok(InstG::HeapAlloc {
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
            Ok(InstG::GEP {
                pointee_ty,
                base,
                indices,
                inbounds,
            })
        }
        10 => Ok(InstG::AtomicLoad {
            ty: read_ty(r)?,
            ptr: r.read_value_id()?,
            ordering: read_ordering(r)?,
        }),
        11 => Ok(InstG::AtomicStore {
            ty: read_ty(r)?,
            ptr: r.read_value_id()?,
            value: r.read_value_id()?,
            ordering: read_ordering(r)?,
        }),
        12 => Ok(InstG::AtomicRMW {
            op: read_atomic_rmw_op(r)?,
            ty: read_ty(r)?,
            ptr: r.read_value_id()?,
            value: r.read_value_id()?,
            ordering: read_ordering(r)?,
        }),
        13 => Ok(InstG::CmpXchg {
            ty: read_ty(r)?,
            ptr: r.read_value_id()?,
            expected: r.read_value_id()?,
            desired: r.read_value_id()?,
            success: read_ordering(r)?,
            failure: read_ordering(r)?,
            weak: false,
        }),
        14 => Ok(InstG::Fence {
            ordering: read_ordering(r)?,
        }),
        15 => Ok(InstG::Br {
            target: r.read_block_id()?,
            args: read_vec_value_id(r)?,
        }),
        16 => Ok(InstG::CondBr {
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
            Ok(InstG::Switch {
                value,
                default,
                default_args,
                cases,
                exhaustive_enum_unreachable,
            })
        }
        18 => Ok(InstG::Call {
            callee: r.read_func_id()?,
            args: read_vec_value_id(r)?,
        }),
        64 if r.version >= CALL_UNWIND_BOUNDARY_FORMAT_VERSION => Ok(InstG::CallCannotUnwind {
            callee: r.read_func_id()?,
            args: read_vec_value_id(r)?,
        }),
        65 if r.version >= CALL_UNWIND_BOUNDARY_FORMAT_VERSION => {
            Ok(InstG::CallIndirectCannotUnwind {
                callee: r.read_value_id()?,
                sig: r.read_func_ty_id()?,
                args: read_vec_value_id(r)?,
                calling_conv: read_calling_conv(r)?,
            })
        }
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
            Ok(InstG::CallIndirect {
                callee,
                sig,
                args,
                calling_conv,
            })
        }
        20 => Ok(InstG::Return {
            values: read_vec_value_id(r)?,
        }),
        21 => Ok(InstG::ExtractField {
            ty: read_ty(r)?,
            aggregate: r.read_value_id()?,
            field: r.read_v32()?,
        }),
        22 => Ok(InstG::InsertField {
            ty: read_ty(r)?,
            aggregate: r.read_value_id()?,
            field: r.read_v32()?,
            value: r.read_value_id()?,
        }),
        23 => Ok(InstG::ExtractElement {
            ty: read_ty(r)?,
            array: r.read_value_id()?,
            index: r.read_value_id()?,
        }),
        24 => Ok(InstG::InsertElement {
            ty: read_ty(r)?,
            array: r.read_value_id()?,
            index: r.read_value_id()?,
            value: r.read_value_id()?,
        }),
        25 => Ok(InstG::Const {
            ty: read_ty(r)?,
            value: read_constant(r)?,
        }),
        26 => Ok(InstG::NullPtr),
        48 => Ok(InstG::GlobalAddr {
            global: GlobalId::new(r.read_v32()?),
        }),
        27 => Ok(InstG::Undef { ty: read_ty(r)? }),
        28 => Ok(InstG::Assume {
            cond: r.read_value_id()?,
        }),
        // Every version: tag 29 is the kindless assert, read as `Unspecified`.
        29 => Ok(InstG::Assert {
            cond: r.read_value_id()?,
            kind: AssertKind::Unspecified,
            site: None,
        }),
        // v52 (plan item P): a kinded assert, read-gated, so an older header
        // carrying tag 63 is `InvalidTag(63)` rather than silently promoted.
        63 if r.version >= ASSERT_KIND_FORMAT_VERSION => Ok(InstG::Assert {
            cond: r.read_value_id()?,
            kind: read_assert_kind(r)?,
            site: None,
        }),
        // v54 (amendment P): a sited assert and `AssertInvoke`, read-gated, so
        // an older header carrying tag 66 / 67 is `InvalidTag` rather than
        // read with its site dropped.
        66 if r.version >= PANIC_SITE_FORMAT_VERSION => {
            let (cond, kind, site) = read_sited_assert_payload(r)?;
            Ok(InstG::Assert {
                cond,
                kind,
                site: Some(site),
            })
        }
        67 if r.version >= PANIC_SITE_FORMAT_VERSION => {
            let (cond, kind, site) = read_sited_assert_payload(r)?;
            Ok(InstG::AssertInvoke {
                cond,
                kind,
                site,
                normal_dest: r.read_block_id()?,
                normal_args: read_vec_value_id(r)?,
                unwind_dest: r.read_block_id()?,
            })
        }
        30 => Ok(InstG::Unreachable),
        31 => Ok(InstG::Copy {
            ty: read_ty(r)?,
            operand: r.read_value_id()?,
        }),
        32 => Ok(InstG::Select {
            ty: read_ty(r)?,
            cond: r.read_value_id()?,
            then_val: r.read_value_id()?,
            else_val: r.read_value_id()?,
        }),
        33 => Ok(InstG::Borrow {
            ptr: r.read_value_id()?,
        }),
        34 => Ok(InstG::BorrowMut {
            ptr: r.read_value_id()?,
        }),
        35 => Ok(InstG::EndBorrow {
            borrow_ptr: r.read_value_id()?,
        }),
        36 => Ok(InstG::Retain {
            ptr: r.read_value_id()?,
        }),
        37 => Ok(InstG::Release {
            ptr: r.read_value_id()?,
        }),
        38 => Ok(InstG::IsUnique {
            ptr: r.read_value_id()?,
        }),
        39 => Ok(InstG::Dealloc {
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
            Ok(InstG::OpenFrame {
                def: crate::inst::BindingFrameDef::new(id, name, slots),
            })
        }
        41 => Ok(InstG::BindSlot {
            frame: r.read_value_id()?,
            slot: r.read_v32()?,
            value: r.read_value_id()?,
        }),
        42 => Ok(InstG::LoadSlot {
            frame: r.read_value_id()?,
            slot: r.read_v32()?,
            ty: read_ty(r)?,
        }),
        43 => Ok(InstG::CloseFrame {
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
            Ok(InstG::CoroSuspend {
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
            Ok(InstG::Invoke {
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
            Ok(InstG::LandingPad {
                is_cleanup,
                catch_type_indices,
            })
        }
        53 => Ok(InstG::Resume {
            exn: r.read_value_id()?,
        }),
        54 => Ok(InstG::SeqMapAddK {
            ty: read_ty(r)?,
            seq: r.read_value_id()?,
            k: r.read_u64()?,
        }),
        55 => Ok(InstG::SeqMapNot {
            ty: read_ty(r)?,
            seq: r.read_value_id()?,
        }),
        56 => Ok(InstG::SeqMap {
            ty: read_ty(r)?,
            seq: r.read_value_id()?,
            fwd: r.read_func_id()?,
        }),
        // v50: read-gated, so an older header carrying tag 59 is `InvalidTag`.
        59 if r.version >= ARRAY_SPLAT_FORMAT_VERSION => Ok(InstG::ArraySplat {
            ty: read_ty(r)?,
            value: r.read_value_id()?,
        }),
        // v51, the INST wire batch: all three tags are read-gated, so an older
        // header carrying one is `InvalidTag` — no older writer emitted them.
        60 if r.version >= INST_WIRE_BATCH_FORMAT_VERSION => Ok(InstG::MakeAggregate {
            ty: read_ty(r)?,
            variant: read_opt_v32(r)?,
            fields: read_vec_value_id(r)?,
        }),
        61 if r.version >= INST_WIRE_BATCH_FORMAT_VERSION => Ok(InstG::MemCopy {
            dst: r.read_value_id()?,
            src: r.read_value_id()?,
            bytes: r.read_value_id()?,
            overlap: r.read_bool()?,
        }),
        62 if r.version >= INST_WIRE_BATCH_FORMAT_VERSION => Ok(InstG::MemSet {
            dst: r.read_value_id()?,
            byte: r.read_value_id()?,
            bytes: r.read_value_id()?,
        }),
        70 if r.version >= MAKE_CLOSURE_FORMAT_VERSION => Ok(InstG::MakeClosure {
            ty: r.read_closure_ty_id()?,
            func: r.read_func_id()?,
            captures: read_vec_value_id(r)?,
        }),
        // v67 (tensor region): read-gated, so an older header carrying tag 71
        // is `InvalidTag(71)` (`refuse/blob_tensor_below_its_version`).
        71 if r.version >= TENSOR_FORMAT_VERSION => Ok(InstG::TensorContract {
            ty: read_ty(r)?,
            lhs: r.read_value_id()?,
            rhs: r.read_value_id()?,
            batch: read_axis_pairs(r)?,
            contract: read_axis_pairs(r)?,
        }),
        // v68 (tensor map, reduce and view): read-gated, so an older header
        // carrying tag 72, 73 or 74 is `InvalidTag`
        // (`refuse/blob_tensor_map_reduce_view_below_its_version`).
        72 if r.version >= TENSOR_MAP_REDUCE_VIEW_FORMAT_VERSION => {
            let ty = read_ty(r)?;
            let args = read_vec_value_id(r)?;
            let n = r.read_checked_len()?;
            let mut body = Vec::with_capacity(n);
            for _ in 0..n {
                body.push(read_tensor_map_node(r)?);
            }
            Ok(InstG::TensorMap { ty, args, body })
        }
        73 if r.version >= TENSOR_MAP_REDUCE_VIEW_FORMAT_VERSION => Ok(InstG::TensorReduce {
            ty: read_ty(r)?,
            src: r.read_value_id()?,
            op: read_tensor_reduce_op(r)?,
            axes: read_v32_list(r)?,
            order: read_tensor_reduce_order(r)?,
        }),
        74 if r.version >= TENSOR_MAP_REDUCE_VIEW_FORMAT_VERSION => {
            let ty = read_ty(r)?;
            let src = r.read_value_id()?;
            let params = read_vec_value_id(r)?;
            let n = r.read_checked_len()?;
            let mut exprs = Vec::with_capacity(n);
            for _ in 0..n {
                exprs.push(read_tensor_index_expr(r)?);
            }
            let shape = read_v32_list(r)?;
            let index = read_v32_list(r)?;
            let fill = match r.read_u8()? {
                0 => None,
                1 => Some(r.read_value_id()?),
                t => return Err(BinaryError::InvalidTag(t)),
            };
            Ok(InstG::TensorView {
                ty,
                src,
                params,
                exprs,
                shape,
                index,
                fill,
            })
        }
        // v69 (tensor gather and scatter): read-gated, so an older header
        // carrying tag 75 or 76 is `InvalidTag`
        // (`refuse/blob_tensor_gather_scatter_below_its_version`).
        75 if r.version >= TENSOR_GATHER_SCATTER_FORMAT_VERSION => Ok(InstG::TensorGather {
            ty: read_ty(r)?,
            data: r.read_value_id()?,
            coords: read_vec_value_id(r)?,
        }),
        76 if r.version >= TENSOR_GATHER_SCATTER_FORMAT_VERSION => Ok(InstG::TensorScatter {
            ty: read_ty(r)?,
            init: r.read_value_id()?,
            src: r.read_value_id()?,
            coords: read_vec_value_id(r)?,
        }),
        44 => Ok(InstG::DialectOp(Box::new(read_dialect_inst(r)?))),
        45 => Ok(InstG::PtrData {
            ptr_ty: read_ty(r)?,
            ptr: r.read_value_id()?,
        }),
        46 => Ok(InstG::PtrMetadata {
            ptr_ty: read_ty(r)?,
            metadata_ty: read_ty(r)?,
            ptr: r.read_value_id()?,
        }),
        47 => Ok(InstG::PtrFromParts {
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
    buf: &mut impl BinarySink,
    pool: &SealedStringPool,
    proofs: &[ProofAnnotation],
) {
    let retained = proofs
        .iter()
        .filter(|proof| {
            #[cfg(feature = "clean-expr")]
            {
                !matches!(proof, ProofAnnotation::Goal(_))
            }
            #[cfg(not(feature = "clean-expr"))]
            {
                let _ = proof;
                true
            }
        })
        .count();
    write_count(buf, "proof annotation list", retained);
    for proof in proofs {
        #[cfg(feature = "clean-expr")]
        if matches!(proof, ProofAnnotation::Goal(_)) {
            continue;
        }
        write_proof_annotation(buf, pool, proof);
    }
}

fn write_proof_annotation(
    buf: &mut impl BinarySink,
    _pool: &SealedStringPool,
    ann: &ProofAnnotation,
) {
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
        ProofAnnotation::RegionHavocStore => write_u8(buf, 38),
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
            write_count(buf, "ProofAnnotation::BranchWeights weights", weights.len());
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

fn write_divergence(buf: &mut impl BinarySink, d: &Divergence) {
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
        38 => Ok(ProofAnnotation::RegionHavocStore),
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

fn write_proof_evidence(buf: &mut impl BinarySink, pool: &SealedStringPool, ev: &ProofEvidence) {
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
        // Module-local inheritance keeps tag 6 and its exact two-varint payload.
        ProofEvidence::InheritedFromCallee {
            callee,
            obligation,
            external: None,
        } => {
            write_u8(buf, 6);
            write_v32(buf, callee.index());
            write_v32(buf, obligation.index());
        }
        // v41 cross-crate inheritance takes a NEW tag, so an older reader
        // refuses it (`InvalidTag(8)`) instead of reading it as local.
        ProofEvidence::InheritedFromCallee {
            callee,
            obligation,
            external: Some(reference),
        } => {
            write_u8(buf, 8);
            write_v32(buf, callee.index());
            write_v32(buf, obligation.index());
            write_extern_ref(buf, pool, reference);
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
                    write_count(
                        buf,
                        "CleanCicKernelRecheck.theorems",
                        recheck.theorems.len(),
                    );
                    for thm in &recheck.theorems {
                        write_str(buf, pool, thm);
                    }
                    write_str(buf, pool, &recheck.anchor);
                    write_count(
                        buf,
                        "CleanCicKernelRecheck.allowed_axioms",
                        recheck.allowed_axioms.len(),
                    );
                    for ax in &recheck.allowed_axioms {
                        write_str(buf, pool, ax);
                    }
                    // v61+: the certificate binding (WS1.12a), a presence
                    // byte after the directive. A binding raises its module
                    // to v61 during collection, so below v61 there is none to
                    // write — never one narrowed to `None`.
                    if pool.minimum_version() >= CERTIFICATE_BINDING_FORMAT_VERSION {
                        match recheck.binding.as_deref() {
                            None => write_u8(buf, 0),
                            Some(binding) => {
                                write_u8(buf, 1);
                                write_certificate_binding(buf, pool, binding);
                            }
                        }
                    } else {
                        assert!(
                            recheck.binding.is_none(),
                            "a certificate binding reached a writer below \
                             CERTIFICATE_BINDING_FORMAT_VERSION; collection must raise it"
                        );
                    }
                }
            }
        }
    }
}

/// The v61 certificate binding record (WS1.12a): the environment and
/// statement digests, the presence-prefixed origin-module digest and source
/// reference, the callee link symbols, then the presence-prefixed island
/// (WS1.13: its declaration bytes, length-framed and OPAQUE — never decoded
/// here — then its recorded digest). Field order is the struct's; every field
/// is written, so the carrier never narrows a binding (the island included,
/// `docs/SPEC_RATIFICATIONS.md` §8 amendment).
fn write_certificate_binding(
    buf: &mut impl BinarySink,
    pool: &SealedStringPool,
    binding: &crate::proof::CertificateBinding,
) {
    // Exhaustive destructure: a field added to `CertificateBinding` without a
    // carrier is a compile error here, never a silently dropped field (the
    // WS1.13 island arrived after this carrier was first written).
    let crate::proof::CertificateBinding {
        environment_digest,
        statement_digest,
        origin_module,
        source,
        callees,
        environment,
    } = binding;
    write_proof_digest(buf, environment_digest);
    write_proof_digest(buf, statement_digest);
    match origin_module {
        None => write_u8(buf, 0),
        Some(digest) => {
            write_u8(buf, 1);
            write_proof_digest(buf, digest);
        }
    }
    match source {
        None => write_u8(buf, 0),
        Some(source) => {
            write_u8(buf, 1);
            write_str(buf, pool, &source.decl);
            write_proof_digest(buf, &source.closure_digest);
        }
    }
    write_count(buf, "CertificateBinding.callees", callees.len());
    for callee in callees {
        write_str(buf, pool, callee);
    }
    // WS1.13: the island rides the carrier as the SAME opaque bytes, with the
    // digest it RECORDS (the validator recomputes and compares it; a reader
    // that recomputed here would launder a forged digest into a true one).
    match environment {
        None => write_u8(buf, 0),
        Some(island) => {
            write_u8(buf, 1);
            write_bytes(buf, &island.declarations);
            write_proof_digest(buf, &island.digest);
        }
    }
}

/// The reader of [`write_certificate_binding`].
fn read_certificate_binding(
    r: &mut Reader<'_>,
) -> Result<crate::proof::CertificateBinding, BinaryError> {
    let environment_digest = read_proof_digest(r)?;
    let statement_digest = read_proof_digest(r)?;
    let origin_module = match r.read_u8()? {
        0 => None,
        1 => Some(read_proof_digest(r)?),
        tag => return Err(BinaryError::InvalidTag(tag)),
    };
    let source = match r.read_u8()? {
        0 => None,
        1 => Some(crate::proof::SourceDefinitionRef {
            decl: r.read_str()?,
            closure_digest: read_proof_digest(r)?,
        }),
        tag => return Err(BinaryError::InvalidTag(tag)),
    };
    let count = r.read_checked_len()?;
    let mut callees = Vec::with_capacity(count);
    for _ in 0..count {
        callees.push(r.read_str()?);
    }
    let environment = match r.read_u8()? {
        0 => None,
        1 => Some(crate::proof::IslandEnvironment {
            declarations: r.read_bytes()?,
            digest: read_proof_digest(r)?,
        }),
        tag => return Err(BinaryError::InvalidTag(tag)),
    };
    // Built field by field (no `..` from a constructor): a field added to the
    // struct without a carrier is a compile error here, not a silent `None`.
    Ok(crate::proof::CertificateBinding {
        environment_digest,
        statement_digest,
        origin_module,
        source,
        callees,
        environment,
    })
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
            let smt_hash = r.read_array()?;
            Ok(ProofEvidence::TranslationValidation {
                rule_name,
                smt_hash,
            })
        }
        5 => Ok(ProofEvidence::Trusted(r.read_str()?)),
        6 => {
            let callee = r.read_func_id()?;
            let obligation = r.read_proof_id()?;
            Ok(ProofEvidence::InheritedFromCallee {
                callee,
                obligation,
                external: None,
            })
        }
        8 if r.version >= CONTRACT_SURFACE_FORMAT_VERSION => {
            let callee = r.read_func_id()?;
            let obligation = r.read_proof_id()?;
            let external = read_extern_ref(r)?;
            Ok(ProofEvidence::InheritedFromCallee {
                callee,
                obligation,
                external: Some(external),
            })
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
                    // v61+: the certificate binding. An older blob has no
                    // carrier, so its directive decodes UNBOUND (the
                    // pre-binding meaning), never bound to anything.
                    let binding = if r.version >= CERTIFICATE_BINDING_FORMAT_VERSION {
                        match r.read_u8()? {
                            0 => None,
                            1 => Some(Box::new(read_certificate_binding(r)?)),
                            tag => return Err(BinaryError::InvalidTag(tag)),
                        }
                    } else {
                        None
                    };
                    Some(CleanCicKernelRecheck {
                        module,
                        theorems,
                        anchor,
                        allowed_axioms,
                        binding,
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

fn write_instr_node<X: WireExt>(
    buf: &mut impl BinarySink,
    pool: &SealedStringPool,
    canonical: Option<&FunctionCanonicalPlan>,
    node: &InstrNodeG<X>,
) {
    write_inst(buf, pool, canonical, &node.inst);
    write_vec_value_id(buf, canonical, &node.results);
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
            write_count(buf, "ProofContext.assumes", pc.assumes.len());
            for o in &pc.assumes {
                write_proof_id(buf, *o);
            }
            write_count(buf, "ProofContext.establishes", pc.establishes.len());
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

fn read_instr_node<X: WireExt>(
    r: &mut Reader<'_>,
    version: u32,
) -> Result<InstrNodeG<X>, BinaryError> {
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
    Ok(InstrNodeG {
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

/// `signature` is the row's index in `Module.func_types`, which a refusal
/// names.
fn write_func_ty<X: WireExt>(
    buf: &mut impl BinarySink,
    pool: &SealedStringPool,
    signature: usize,
    ft: &FuncTyG<X>,
) {
    write_count(buf, "FuncTy.params", ft.params.len());
    for p in &ft.params {
        write_ty(buf, pool, p);
    }
    write_count(buf, "FuncTy.returns", ft.returns.len());
    for r in &ft.returns {
        write_ty(buf, pool, r);
    }
    write_bool(buf, ft.is_vararg);
    if pool.minimum_version() >= SIGNATURE_ABI_FORMAT_VERSION {
        write_bool(buf, ft.abi.is_some());
        if let Some(abi) = &ft.abi {
            // A descriptor past the limits its reader enforces has no wire
            // image: refused by this arm (the reader's own predicate, so the
            // two cannot disagree), and nothing is written for it.
            match abi.validate_encoding_limits() {
                Ok(()) => write_raw_str(buf, &abi.to_canonical_text()),
                Err(detail) => buf.refuse(WireRefusal::SignatureAbi { signature, detail }),
            }
        }
    }
}

fn read_func_ty<X: WireExt>(r: &mut Reader<'_>) -> Result<FuncTyG<X>, BinaryError> {
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
    let abi = if r.version >= SIGNATURE_ABI_FORMAT_VERSION && r.read_bool()? {
        let len = r.read_checked_len()?;
        if len > crate::signature_abi::MAX_ABI_TEXT_BYTES {
            return Err(BinaryError::InvalidData(
                "signature ABI exceeds its wire byte limit".into(),
            ));
        }
        let bytes = r.read_exact(len)?;
        let text = std::str::from_utf8(&bytes).map_err(|_| BinaryError::Utf8Error)?;
        Some(
            crate::signature_abi::SignatureAbi::from_canonical_text(text)
                .map_err(|e| BinaryError::InvalidData(e.to_string()))?,
        )
    } else {
        None
    };
    Ok(FuncTyG {
        params,
        returns,
        abi,
        is_vararg,
    })
}

// Nominal carriers can now be mapped between levels, but their wire rows remain
// ground at both levels. Keep this boundary explicit in addition to S's T5.
fn write_ground_nominal_ty<X: WireExt>(
    buf: &mut impl BinarySink,
    pool: &SealedStringPool,
    ty: &TyG<X>,
) {
    // NoExt cannot contain an extension; keep R's ordinary writer free of an
    // additional type-tree walk. Only the S carrier needs this boundary check.
    if X::reads_ext() {
        let mut generic = false;
        ty.for_each_ext(&mut |_| generic = true);
        if generic {
            buf.refuse(WireRefusal::NoWireTag {
                construct: "extension in a ground nominal field",
                site: None,
            });
            return;
        }
    }
    write_ty(buf, pool, ty);
}

fn read_ground_nominal_ty<X: WireExt>(r: &mut Reader<'_>) -> Result<TyG<X>, BinaryError> {
    let ty = read_ty(r)?;
    // The R type reader already refuses extension tags by construction.
    if X::reads_ext() {
        let mut generic = false;
        ty.for_each_ext(&mut |_| generic = true);
        if generic {
            return Err(BinaryError::InvalidData(
                "extension in a ground nominal field".into(),
            ));
        }
    }
    Ok(ty)
}

fn write_field_def<X: WireExt>(
    buf: &mut impl BinarySink,
    pool: &SealedStringPool,
    fd: &FieldDefG<X>,
) {
    write_str(buf, pool, &fd.name);
    write_ground_nominal_ty(buf, pool, &fd.ty);
    match fd.offset {
        None => write_u8(buf, 0),
        Some(o) => {
            write_u8(buf, 1);
            write_u64(buf, o);
        }
    }
}

fn read_field_def<X: WireExt>(r: &mut Reader<'_>) -> Result<FieldDefG<X>, BinaryError> {
    let name = r.read_str()?;
    let ty = read_ground_nominal_ty(r)?;
    let offset = match r.read_u8()? {
        0 => None,
        1 => Some(r.read_u64()?),
        t => return Err(BinaryError::InvalidTag(t)),
    };
    Ok(FieldDefG { name, ty, offset })
}

/// v58 nominal identity key. One presence byte, then a variant tag.
///
/// Written only when the pool already selected v58 (`collect_strings_into`
/// raises `minimum_version` for every keyed def), so a module with no keys is
/// byte-identical to its pre-v58 encoding.
fn write_type_origin(
    buf: &mut impl BinarySink,
    pool: &SealedStringPool,
    origin: Option<&TypeOrigin>,
) {
    match origin {
        None => write_u8(buf, 0),
        Some(TypeOrigin::Rust {
            stable_crate_id,
            def_path_hash,
            args_digest,
        }) => {
            write_u8(buf, 1);
            write_u8(buf, 0);
            write_u64(buf, *stable_crate_id);
            buf.extend_from_slice(def_path_hash);
            write_proof_digest(buf, args_digest);
        }
        Some(TypeOrigin::Clean { decl, env_digest }) => {
            write_u8(buf, 1);
            write_u8(buf, 1);
            write_str(buf, pool, decl);
            write_proof_digest(buf, env_digest);
        }
    }
}

fn read_type_origin(r: &mut Reader<'_>) -> Result<Option<TypeOrigin>, BinaryError> {
    // Read-gated: a header below `NOMINAL_IDENTITY_FORMAT_VERSION` carries no
    // origin byte at all, and a blob CLAIMING one must not be promoted by
    // reading bytes that belong to the next record. Stated against the
    // constant, not a literal, so the sentence survives a renumber.
    if r.version < NOMINAL_IDENTITY_FORMAT_VERSION {
        return Ok(None);
    }
    match r.read_u8()? {
        0 => Ok(None),
        1 => match r.read_u8()? {
            0 => {
                let stable_crate_id = r.read_u64()?;
                let mut def_path_hash = [0u8; 16];
                for byte in &mut def_path_hash {
                    *byte = r.read_u8()?;
                }
                let args_digest = read_proof_digest(r)?;
                Ok(Some(TypeOrigin::Rust {
                    stable_crate_id,
                    def_path_hash,
                    args_digest,
                }))
            }
            1 => {
                let decl = r.read_str()?;
                let env_digest = read_proof_digest(r)?;
                Ok(Some(TypeOrigin::Clean { decl, env_digest }))
            }
            t => Err(BinaryError::InvalidTag(t)),
        },
        t => Err(BinaryError::InvalidTag(t)),
    }
}

fn write_struct_def<X: WireExt>(
    buf: &mut impl BinarySink,
    pool: &SealedStringPool,
    sd: &StructDefG<X>,
) {
    write_struct_id(buf, sd.id);
    write_str(buf, pool, &sd.name);
    write_count(buf, "StructDef.fields", sd.fields.len());
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
    // v58 nominal identity key (trailing, presence-tagged).
    if pool.minimum_version() >= NOMINAL_IDENTITY_FORMAT_VERSION {
        write_type_origin(buf, pool, sd.origin.as_ref());
    }
}

fn read_struct_def<X: WireExt>(r: &mut Reader<'_>) -> Result<StructDefG<X>, BinaryError> {
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
    let origin = read_type_origin(r)?;
    Ok(StructDefG {
        id,
        name,
        fields,
        size,
        align,
        repr,
        origin,
    })
}

fn write_record_def(buf: &mut impl BinarySink, pool: &SealedStringPool, rd: &RecordDef) {
    write_v32(buf, rd.id.0);
    write_str(buf, pool, &rd.name);
    write_count(buf, "RecordDef.fields", rd.fields.len());
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

fn write_closure_ty(buf: &mut impl BinarySink, pool: &SealedStringPool, ct: &ClosureTy) {
    write_func_ty_id(buf, ct.func);
    write_count(buf, "ClosureTy.captures", ct.captures.len());
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

fn write_enum_variant<X: WireExt>(
    buf: &mut impl BinarySink,
    pool: &SealedStringPool,
    ev: &EnumVariantG<X>,
) {
    write_str(buf, pool, &ev.name);
    write_count(buf, "EnumVariant.fields", ev.fields.len());
    for f in &ev.fields {
        write_ground_nominal_ty(buf, pool, f);
    }
    write_count(buf, "EnumVariant.field_names", ev.field_names.len());
    for name in &ev.field_names {
        write_str(buf, pool, name);
    }
}

fn read_enum_variant<X: WireExt>(r: &mut Reader<'_>) -> Result<EnumVariantG<X>, BinaryError> {
    let name = r.read_str()?;
    let field_count = r.read_checked_len()?;
    let mut fields = Vec::with_capacity(field_count);
    for _ in 0..field_count {
        fields.push(read_ground_nominal_ty(r)?);
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
    Ok(EnumVariantG {
        name,
        fields,
        field_names,
    })
}

fn write_enum_def<X: WireExt>(
    buf: &mut impl BinarySink,
    pool: &SealedStringPool,
    ed: &EnumDefG<X>,
) {
    write_enum_id(buf, ed.id);
    write_str(buf, pool, &ed.name);
    write_count(buf, "EnumDef.variants", ed.variants.len());
    for v in &ed.variants {
        write_enum_variant(buf, pool, v);
    }
    // Explicit discriminants + tag-repr hint (VERSION >= 19). Written
    // verbatim (the vector may be shorter than `variants`; entries are
    // Option-tagged 0=implicit 1=explicit i128).
    write_count(buf, "EnumDef.discriminants", ed.discriminants.len());
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
                EnumTagEncoding::SingleInhabited { variant } => {
                    write_u8(buf, 3);
                    write_v32(buf, *variant);
                }
            }
            write_v64(buf, layout.size);
            write_v64(buf, layout.align);
            write_count(
                buf,
                "EnumLayoutDescriptor.variant_field_offsets",
                layout.variant_field_offsets.len(),
            );
            for offsets in &layout.variant_field_offsets {
                write_count(
                    buf,
                    "EnumLayoutDescriptor.variant_field_offsets row",
                    offsets.len(),
                );
                for offset in offsets {
                    write_v64(buf, *offset);
                }
            }
        }
    }
    // v58 nominal identity key (trailing, presence-tagged).
    if pool.minimum_version() >= NOMINAL_IDENTITY_FORMAT_VERSION {
        write_type_origin(buf, pool, ed.origin.as_ref());
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
        // v45 (WS3.14(b)): read-gated, so a pre-v45 blob can never carry one.
        EnumTagRepr::U128 => 9,
        EnumTagRepr::I128 => 10,
    }
}

fn enum_tag_repr_from_byte(byte: u8, version: u32) -> Result<EnumTagRepr, BinaryError> {
    Ok(match byte {
        1 => EnumTagRepr::U8,
        2 => EnumTagRepr::U16,
        3 => EnumTagRepr::U32,
        4 => EnumTagRepr::U64,
        5 => EnumTagRepr::I8,
        6 => EnumTagRepr::I16,
        7 => EnumTagRepr::I32,
        8 => EnumTagRepr::I64,
        9 if version >= ABI_SURFACE_FORMAT_VERSION => EnumTagRepr::U128,
        10 if version >= ABI_SURFACE_FORMAT_VERSION => EnumTagRepr::I128,
        tag => return Err(BinaryError::InvalidTag(tag)),
    })
}

fn read_enum_def<X: WireExt>(r: &mut Reader<'_>) -> Result<EnumDefG<X>, BinaryError> {
    let id = r.read_enum_id()?;
    let name = r.read_str()?;
    let variant_count = r.read_checked_len()?;
    if variant_count == 0 && r.version < SINGLE_INHABITED_ENUM_FORMAT_VERSION {
        return Err(BinaryError::InvalidData(
            "empty nominal enum declarations require wire v65".into(),
        ));
    }
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
            byte => Some(enum_tag_repr_from_byte(byte, r.version)?),
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
                        niche_ty: enum_tag_repr_from_byte(r.read_u8()?, r.version)?,
                    },
                    // v37. Gated, not unconditional: byte 2 is not a value any
                    // v36-or-earlier writer could have produced, so a blob
                    // CLAIMING v36 that carries it is malformed and must be
                    // refused rather than silently promoted.
                    2 if r.version >= 37 => EnumTagEncoding::Untagged,
                    3 if r.version >= SINGLE_INHABITED_ENUM_FORMAT_VERSION => {
                        EnumTagEncoding::SingleInhabited {
                            variant: r.read_v32()?,
                        }
                    }
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
    let origin = read_type_origin(r)?;
    Ok(EnumDefG {
        id,
        name,
        variants,
        discriminants,
        repr,
        layout,
        origin,
    })
}

fn write_global<X: WireExt>(
    buf: &mut impl BinarySink,
    pool: &SealedStringPool,
    g: &GlobalG<X>,
    name: Option<&str>,
) {
    write_str(buf, pool, name.unwrap_or(&g.name));
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
    // v41: section, visibility, retention.
    if contract_surface(pool) {
        write_opt_str(buf, pool, g.section.as_deref());
        write_visibility(buf, &g.visibility);
        write_bool(buf, g.retained);
    }
}

fn read_global<X: WireExt>(r: &mut Reader<'_>, version: u32) -> Result<GlobalG<X>, BinaryError> {
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
    // v41: an older blob consumes none of these and means "no section, default
    // visibility, not retained" — the pre-v41 world.
    let (section, visibility, retained) = if version >= CONTRACT_SURFACE_FORMAT_VERSION {
        (read_opt_str(r)?, read_visibility(r)?, r.read_bool()?)
    } else {
        (None, Visibility::Default, false)
    };
    Ok(GlobalG {
        name,
        ty,
        mutable,
        initializer,
        linkage,
        tls,
        align,
        section,
        visibility,
        retained,
    })
}

fn write_block<X: WireExt>(
    buf: &mut impl BinarySink,
    pool: &SealedStringPool,
    canonical: Option<&FunctionCanonicalPlan>,
    function: FuncId,
    block: &BlockG<X>,
) {
    write_block_id(buf, block.id);
    write_count(buf, "Block.params", block.params.len());
    for (vid, ty) in &block.params {
        write_projected_value_id(buf, canonical, *vid);
        write_ty(buf, pool, ty);
    }
    write_count(buf, "Block.body", block.body.len());
    for (index, node) in block.body.iter().enumerate() {
        // An instruction ahead of its wire tag (the ONE list is
        // `Inst::binary_wire_gap`, empty since v51) is refused here, at its
        // node, and nothing is written for it.
        if let Some(construct) = node.inst.binary_wire_gap() {
            buf.refuse(WireRefusal::NoWireTag {
                construct,
                site: Some(WireNodeSite {
                    function: function.index(),
                    block: block.id.index(),
                    index,
                }),
            });
            continue;
        }
        write_instr_node(buf, pool, canonical, node);
    }
}

fn read_block<X: WireExt>(r: &mut Reader<'_>, version: u32) -> Result<BlockG<X>, BinaryError> {
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
    Ok(BlockG { id, params, body })
}

fn write_proof_obligation(
    buf: &mut impl BinarySink,
    pool: &SealedStringPool,
    po: &ProofObligation,
    canonical: Option<&FunctionCanonicalPlan>,
) {
    write_proof_id(buf, po.id);
    write_obligation_kind(buf, pool, &po.kind);
    write_proof_status(buf, &po.status);
    write_str(buf, pool, &po.description);
    match &po.formula {
        None => write_u8(buf, 0),
        Some(formula) => {
            write_u8(buf, 1);
            // ONE formula encoder. This used to be an inline duplicate of
            // `write_proof_formula`, kept in lockstep by comment; it silently
            // dropped v41 `bindings` the moment the shared encoder grew them.
            // `canonical` is the owning function's plan (WS4.4, NEW-1).
            write_proof_formula_in(buf, pool, formula, canonical);
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
    // v46+: the named temporal property this obligation discharges.
    if pool.minimum_version() >= SPEC_CARRIER_FORMAT_VERSION {
        match &po.spec {
            None => write_u8(buf, 0),
            Some(spec) => {
                write_u8(buf, 1);
                write_str(buf, pool, &spec.machine);
                write_str(buf, pool, &spec.temporal);
            }
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
        1 => Some(read_proof_formula(r)?),
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
    // v46+: the temporal-property backref; legacy files default to None
    // (unbindable, never a wildcard).
    let spec = if version >= SPEC_CARRIER_FORMAT_VERSION {
        match r.read_u8()? {
            0 => None,
            1 => Some(crate::proof::SpecObligationRef {
                machine: r.read_str()?,
                temporal: r.read_str()?,
            }),
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
        spec,
    })
}

fn trust_ir_site(function: u32, block: u32, inst_index: u32) -> crate::proof::ObligationSite {
    crate::proof::ObligationSite::new(
        FuncId::new(function),
        crate::value::BlockId::new(block),
        inst_index,
    )
}

fn write_proof_certificate(
    buf: &mut impl BinarySink,
    pool: &SealedStringPool,
    cert: &ProofCertificate,
) {
    write_proof_id(buf, cert.obligation);
    write_str(buf, pool, &cert.prover);
    write_proof_evidence(buf, pool, &cert.evidence);
    // v41: coverage assurance projected from the evidence bundle.
    if contract_surface(pool) {
        match &cert.assurance {
            None => write_u8(buf, 0),
            Some(assurance) => {
                write_u8(buf, 1);
                match assurance.bound {
                    CoverageBound::Unbounded => write_u8(buf, 0),
                    CoverageBound::UnwindBounded { depth } => {
                        write_u8(buf, 1);
                        write_u64(buf, depth);
                    }
                    CoverageBound::ModelBounded { size } => {
                        write_u8(buf, 2);
                        write_u64(buf, size);
                    }
                    CoverageBound::Unrecorded => write_u8(buf, 3),
                }
                write_proof_digest(buf, &assurance.request_digest);
            }
        }
    }
}

fn read_proof_certificate(r: &mut Reader<'_>) -> Result<ProofCertificate, BinaryError> {
    let obligation = r.read_proof_id()?;
    let prover = r.read_str()?;
    let evidence = read_proof_evidence(r)?;
    // v41. `None` is UNKNOWN coverage, never `Unbounded`.
    let assurance = if r.version >= CONTRACT_SURFACE_FORMAT_VERSION {
        match r.read_u8()? {
            0 => None,
            1 => {
                let bound = match r.read_u8()? {
                    0 => CoverageBound::Unbounded,
                    1 => CoverageBound::UnwindBounded {
                        depth: r.read_u64()?,
                    },
                    2 => CoverageBound::ModelBounded {
                        size: r.read_u64()?,
                    },
                    3 => CoverageBound::Unrecorded,
                    tag => return Err(BinaryError::InvalidTag(tag)),
                };
                Some(CoverageAssurance {
                    bound,
                    request_digest: read_proof_digest(r)?,
                })
            }
            tag => return Err(BinaryError::InvalidTag(tag)),
        }
    } else {
        None
    };
    Ok(ProofCertificate {
        obligation,
        prover,
        evidence,
        assurance,
    })
}

// ---------------------------------------------------------------------------
// ProofLineageManifest sidecar storage
// ---------------------------------------------------------------------------

fn write_proof_digest(buf: &mut impl BinarySink, digest: &ProofDigest) {
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
    let digest = r.read_array()?;
    Ok(ProofDigest {
        algorithm,
        bytes: digest,
    })
}

fn write_proof_transform_stage(buf: &mut impl BinarySink, stage: ProofTransformStage) {
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

fn write_proof_transform(
    buf: &mut impl BinarySink,
    pool: &SealedStringPool,
    transform: &ProofTransform,
) {
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
    buf: &mut impl BinarySink,
    pool: &SealedStringPool,
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
    buf: &mut impl BinarySink,
    pool: &SealedStringPool,
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

fn write_proof_lineage_node(
    buf: &mut impl BinarySink,
    pool: &SealedStringPool,
    node: &ProofLineageNode,
) {
    write_v32(buf, node.id.0);
    write_proof_transform(buf, pool, &node.transform);
    write_proof_digest(buf, &node.source_module);
    write_proof_digest(buf, &node.target_module);

    let mut obligations = node.obligations.clone();
    obligations.sort();
    write_count(buf, "ProofLineageNode.obligations", obligations.len());
    for obligation in obligations {
        write_v32(buf, obligation.0);
    }

    let mut certificates = node.certificates.clone();
    certificates.sort();
    write_count(buf, "ProofLineageNode.certificates", certificates.len());
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
    write_count(buf, "ProofLineageNode.depends_on", depends_on.len());
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

/// The v45 pass-mode record: one tag byte that encodes the whole `Option`
/// (`0` = UNRECORDED, which a consumer must not read as "Direct"), then the
/// variant's payload. Written only under [`abi_surface`].
fn write_pass_mode(buf: &mut impl BinarySink, pool: &SealedStringPool, pass: Option<&PassMode>) {
    match pass {
        None => write_u8(buf, 0),
        Some(PassMode::Ignore) => write_u8(buf, 1),
        Some(PassMode::Direct) => write_u8(buf, 2),
        Some(PassMode::Pair) => write_u8(buf, 3),
        Some(PassMode::Cast { pieces }) => {
            write_u8(buf, 4);
            write_count(buf, "PassMode::Cast pieces", pieces.len());
            for piece in pieces {
                write_ty(buf, pool, piece);
            }
        }
        Some(PassMode::Indirect { on_stack }) => {
            write_u8(buf, 5);
            write_bool(buf, *on_stack);
        }
    }
}

fn read_pass_mode(r: &mut Reader<'_>) -> Result<Option<PassMode>, BinaryError> {
    Ok(match r.read_u8()? {
        0 => None,
        1 => Some(PassMode::Ignore),
        2 => Some(PassMode::Direct),
        3 => Some(PassMode::Pair),
        4 => {
            let n = r.read_checked_len()?;
            let mut pieces = Vec::with_capacity(n);
            for _ in 0..n {
                pieces.push(read_ty(r)?);
            }
            Some(PassMode::Cast { pieces })
        }
        5 => Some(PassMode::Indirect {
            on_stack: r.read_bool()?,
        }),
        tag => return Err(BinaryError::InvalidTag(tag)),
    })
}

fn write_param_attrs(buf: &mut impl BinarySink, pool: &SealedStringPool, pa: &ParamAttrs) {
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
    // v45 (WS3.11): the integer extension rides flag bits 5 and 6. They are
    // MUTUALLY EXCLUSIVE — both set is not a third extension — and setting
    // either raised the writer to v45 in the collection walk, so no pre-v45
    // blob carries one. Bit 7 is unallocated and never written.
    match pa.ext {
        ArgExt::None => {}
        ArgExt::ZeroExt => flags |= 0b010_0000,
        ArgExt::SignExt => flags |= 0b100_0000,
    }
    write_u8(buf, flags);
    write_opt_u64(buf, pa.dereferenceable);
    write_opt_u64(buf, pa.align);
    // v45: the pass mode, a presence-tagged record after `align`.
    if abi_surface(pool) {
        write_pass_mode(buf, pool, pa.pass.as_ref());
    }
}

fn read_param_attrs(r: &mut Reader<'_>) -> Result<ParamAttrs, BinaryError> {
    let flags = r.read_u8()?;
    // WS3.11 (wire checklist item 7): unknown flag bits are REFUSED, not
    // dropped. Before this a v43 blob with bit 5 set decoded silently with
    // the bit gone, so a v45 extension smuggled into an older blob became
    // "no extension recorded" instead of an error. Pinned as bytes:
    // `refuse/blob_param_flag_bit_below_its_version`. The allocated set grows
    // with the version: bits 0..=2 always, 3..=4 from v20, 5..=6 from v45.
    let mut allocated: u8 = 0b0000_0111;
    if r.version >= 20 {
        allocated |= 0b0001_1000;
    }
    if r.version >= ABI_SURFACE_FORMAT_VERSION {
        allocated |= 0b0110_0000;
    }
    if flags & !allocated != 0 {
        return Err(BinaryError::InvalidData(format!(
            "parameter attribute flag bits {:#04x} are not allocated at wire version {}",
            flags & !allocated,
            r.version
        )));
    }
    let ext = match flags & 0b0110_0000 {
        0 => ArgExt::None,
        0b010_0000 => ArgExt::ZeroExt,
        0b100_0000 => ArgExt::SignExt,
        // Both extension bits set is not a third extension: refuse rather
        // than pick one.
        _ => {
            return Err(BinaryError::InvalidData(
                "parameter attribute flags set both `zeroext` and `signext`".to_string(),
            ));
        }
    };
    let dereferenceable = read_opt_u64(r)?;
    let align = read_opt_u64(r)?;
    let pass = if r.version >= ABI_SURFACE_FORMAT_VERSION {
        read_pass_mode(r)?
    } else {
        None
    };
    // byval/sret are VERSION >= 20 flag bits. Pre-v20 writers never set them,
    // and a pre-v20 blob that spells one is now refused above.
    Ok(ParamAttrs {
        dereferenceable,
        nonnull: flags & 0b0001 != 0,
        align,
        noalias: flags & 0b0010 != 0,
        readonly: flags & 0b0100 != 0,
        byval: flags & 0b0_1000 != 0,
        sret: flags & 0b1_0000 != 0,
        ext,
        pass,
    })
}

fn write_func_attrs(
    buf: &mut impl BinarySink,
    pool: &SealedStringPool,
    fa: &FuncAttrs,
    param_count: Option<usize>,
) {
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
    // v41: `naked` rides bit 4. Setting it raised the writer to v41 in the
    // collection walk, so no pre-v41 blob ever carries the bit.
    if fa.naked {
        flags |= 0b1_0000;
    }
    write_u8(buf, flags);
    let param_count = param_count.unwrap_or(fa.params.len());
    write_count(buf, "FuncAttrs.params", param_count);
    for pa in &fa.params[..param_count] {
        write_param_attrs(buf, pool, pa);
    }
    // v41: target features, a trailing block.
    if contract_surface(pool) {
        write_count(buf, "FuncAttrs.target_features", fa.target_features.len());
        for feature in &fa.target_features {
            write_str(buf, pool, feature);
        }
    }
    // v45 (WS3.11): the return slot, the same record as a parameter's.
    if abi_surface(pool) {
        write_param_attrs(buf, pool, &fa.ret);
    }
}

fn read_func_attrs(r: &mut Reader<'_>) -> Result<FuncAttrs, BinaryError> {
    let flags = r.read_u8()?;
    // Bit 4 (`naked`) is v41. No pre-v41 writer ever set it, and decoding it
    // under an older header would grant a v41-only meaning and silently raise
    // the module to v41 on re-serialization, so refuse rather than guess.
    if flags & 0b1_0000 != 0 && r.version < CONTRACT_SURFACE_FORMAT_VERSION {
        return Err(BinaryError::InvalidData(
            "function attribute flag bit 4 (`naked`) requires a v41 header".to_string(),
        ));
    }
    let n = r.read_checked_len()?;
    let mut params = Vec::with_capacity(n);
    for _ in 0..n {
        params.push(read_param_attrs(r)?);
    }
    let target_features = if r.version >= CONTRACT_SURFACE_FORMAT_VERSION {
        let n = r.read_checked_len()?;
        let mut out = Vec::with_capacity(n);
        for _ in 0..n {
            out.push(r.read_str()?);
        }
        out
    } else {
        Vec::new()
    };
    let ret = if r.version >= ABI_SURFACE_FORMAT_VERSION {
        read_param_attrs(r)?
    } else {
        ParamAttrs::default()
    };
    Ok(FuncAttrs {
        readonly: flags & 0b0001 != 0,
        readnone: flags & 0b0010 != 0,
        inlinehint: flags & 0b0100 != 0,
        cold: flags & 0b1000 != 0,
        params,
        naked: flags & 0b1_0000 != 0,
        target_features,
        ret,
    })
}

/// Serialize a [`ProofFormula`] (schema + payload + optional smtlib/sort). Mirrors
/// the inline encoding in [`write_proof_obligation`] so both stay in lockstep.
/// v41 clause sort. Tags mirror `trust_ir_contract::Sort`'s variant order so a
/// bridge translation is tag-preserving.
fn write_clause_sort(buf: &mut impl BinarySink, pool: &SealedStringPool, sort: &ClauseSort) {
    match sort {
        ClauseSort::Bool => write_u8(buf, 0),
        ClauseSort::Int => write_u8(buf, 1),
        ClauseSort::BitVec(width) => {
            write_u8(buf, 2);
            write_v32(buf, *width);
        }
        ClauseSort::Array(k, v) => {
            write_u8(buf, 3);
            write_clause_sort(buf, pool, k);
            write_clause_sort(buf, pool, v);
        }
        ClauseSort::Float { eb, sb } => {
            write_u8(buf, 4);
            write_v32(buf, *eb);
            write_v32(buf, *sb);
        }
        ClauseSort::RoundingMode => write_u8(buf, 5),
        ClauseSort::Datatype { name, constructors } => {
            write_u8(buf, 6);
            write_str(buf, pool, name);
            write_count(buf, "ClauseSort::Datatype constructors", constructors.len());
            for (ctor, fields) in constructors {
                write_str(buf, pool, ctor);
                write_count(buf, "ClauseSort::Datatype constructor fields", fields.len());
                for (field, field_sort) in fields {
                    write_str(buf, pool, field);
                    write_clause_sort(buf, pool, field_sort);
                }
            }
        }
    }
}

fn read_clause_sort(r: &mut Reader<'_>) -> Result<ClauseSort, BinaryError> {
    Ok(match r.read_u8()? {
        0 => ClauseSort::Bool,
        1 => ClauseSort::Int,
        2 => ClauseSort::BitVec(r.read_v32()?),
        3 => {
            let k = read_clause_sort(r)?;
            let v = read_clause_sort(r)?;
            ClauseSort::Array(Box::new(k), Box::new(v))
        }
        4 => ClauseSort::Float {
            eb: r.read_v32()?,
            sb: r.read_v32()?,
        },
        5 => ClauseSort::RoundingMode,
        6 => {
            let name = r.read_str()?;
            let n = r.read_checked_len()?;
            let mut constructors = Vec::with_capacity(n);
            for _ in 0..n {
                let ctor = r.read_str()?;
                let field_count = r.read_checked_len()?;
                let mut fields = Vec::with_capacity(field_count);
                for _ in 0..field_count {
                    let field = r.read_str()?;
                    fields.push((field, read_clause_sort(r)?));
                }
                constructors.push((ctor, fields));
            }
            ClauseSort::Datatype { name, constructors }
        }
        tag => return Err(BinaryError::InvalidTag(tag)),
    })
}

fn write_clause_place(buf: &mut impl BinarySink, place: &ClausePlace) {
    match place {
        ClausePlace::Param { index } => {
            write_u8(buf, 0);
            write_v32(buf, *index);
        }
        ClausePlace::ResultSlot { index } => {
            write_u8(buf, 1);
            write_v32(buf, *index);
        }
        ClausePlace::MutParamExit { index } => {
            write_u8(buf, 2);
            write_v32(buf, *index);
        }
        ClausePlace::World => write_u8(buf, 3),
        ClausePlace::Unwind => write_u8(buf, 4),
        ClausePlace::Value(v) => {
            write_u8(buf, 5);
            write_value_id(buf, *v);
        }
        // v46: the spec-variable index space. Selection is driven by the
        // string collector, which raises `pool.minimum_version` for every
        // carrier that can hold one.
        ClausePlace::SpecVar { index } => {
            write_u8(buf, 6);
            write_v32(buf, *index);
        }
        ClausePlace::SpecVarNext { index } => {
            write_u8(buf, 7);
            write_v32(buf, *index);
        }
        // v59: the world epochs, tag only. Selection is driven by the string
        // collector, which raises `pool.minimum_version` wherever one is bound.
        ClausePlace::WorldPre => write_u8(buf, 8),
        ClausePlace::WorldPost => write_u8(buf, 9),
        // v62: tag 10 (8 and 9 are the v59 world epochs). Selected, like them and the
        // spec-variable places, by the formula string collector.
        ClausePlace::ParamPointeeEntry { index } => {
            write_u8(buf, 10);
            write_v32(buf, *index);
        }
    }
}

fn read_clause_place(r: &mut Reader<'_>) -> Result<ClausePlace, BinaryError> {
    Ok(match r.read_u8()? {
        0 => ClausePlace::Param {
            index: r.read_v32()?,
        },
        1 => ClausePlace::ResultSlot {
            index: r.read_v32()?,
        },
        2 => ClausePlace::MutParamExit {
            index: r.read_v32()?,
        },
        3 => ClausePlace::World,
        4 => ClausePlace::Unwind,
        5 => ClausePlace::Value(r.read_value_id()?),
        6 if r.version >= SPEC_CARRIER_FORMAT_VERSION => ClausePlace::SpecVar {
            index: r.read_v32()?,
        },
        7 if r.version >= SPEC_CARRIER_FORMAT_VERSION => ClausePlace::SpecVarNext {
            index: r.read_v32()?,
        },
        8 if r.version >= EFFECT_SUMMARY_FORMAT_VERSION => ClausePlace::WorldPre,
        9 if r.version >= EFFECT_SUMMARY_FORMAT_VERSION => ClausePlace::WorldPost,
        10 if r.version >= PARAM_POINTEE_PLACE_FORMAT_VERSION => ClausePlace::ParamPointeeEntry {
            index: r.read_v32()?,
        },
        tag => return Err(BinaryError::InvalidTag(tag)),
    })
}

/// Serialize a [`ProofFormula`]: schema, payload, optional smtlib/sort, and at
/// v41 the typed clause bindings. The single formula encoder — obligations call
/// it too.
fn write_proof_formula(buf: &mut impl BinarySink, pool: &SealedStringPool, f: &ProofFormula) {
    write_proof_formula_in(buf, pool, f, None);
}

/// [`write_proof_formula`] with the canonical plan of the function the
/// formula's `ClausePlace::Value` bindings resolve against (roadmap WS4.4,
/// NEW-1). A canonical projection renumbers that function's SSA values, so a
/// `Value` binding is written through
/// [`FunctionCanonicalPlan::map_binding_value`] — exactly the rewrite
/// `format::into_canonical` performs — and the streamed canonical image stays
/// byte-identical to the image of the materialized canonical module. `None`
/// (raw mode, or an identity function) writes the binding as stored.
fn write_proof_formula_in(
    buf: &mut impl BinarySink,
    pool: &SealedStringPool,
    f: &ProofFormula,
    canonical: Option<&FunctionCanonicalPlan>,
) {
    write_str(buf, pool, &f.schema);
    write_str(buf, pool, &f.payload);
    write_opt_str(buf, pool, f.smtlib.as_deref());
    write_opt_str(buf, pool, f.sort.as_deref());
    if contract_surface(pool) {
        // An empty vector is the legacy shape and reads as UNBINDABLE.
        write_count(buf, "ProofFormula.bindings", f.bindings.len());
        for (name, binding) in &f.bindings {
            write_str(buf, pool, name);
            write_clause_sort(buf, pool, &binding.sort);
            match (&binding.place, canonical) {
                (ClausePlace::Value(value), Some(plan)) => {
                    write_clause_place(buf, &ClausePlace::Value(plan.map_binding_value(*value)));
                }
                (place, _) => write_clause_place(buf, place),
            }
        }
    }
}

fn read_proof_formula(r: &mut Reader<'_>) -> Result<ProofFormula, BinaryError> {
    let schema = r.read_str()?;
    let payload = r.read_str()?;
    let smtlib = read_opt_str(r)?;
    let sort = read_opt_str(r)?;
    let bindings = if r.version >= CONTRACT_SURFACE_FORMAT_VERSION {
        let n = r.read_checked_len()?;
        let mut out = Vec::with_capacity(n);
        for _ in 0..n {
            let name = r.read_str()?;
            let sort = read_clause_sort(r)?;
            let place = read_clause_place(r)?;
            out.push((name, ClauseBinding { sort, place }));
        }
        out
    } else {
        Vec::new()
    };
    Ok(ProofFormula {
        schema,
        payload,
        smtlib,
        sort,
        bindings,
    })
}

/// Serialize the separate-compilation [`FunctionSummary`] (v18+). `canonical`
/// is the owning function's canonical plan, if the projection renumbers it
/// (the clauses' `Value` bindings follow the body — WS4.4, NEW-1).
fn write_function_summary(
    buf: &mut impl BinarySink,
    pool: &SealedStringPool,
    s: &FunctionSummary,
    canonical: Option<&FunctionCanonicalPlan>,
) {
    write_count(buf, "FunctionSummary.requires", s.requires.len());
    for c in &s.requires {
        write_proof_formula_in(buf, pool, c, canonical);
    }
    write_count(buf, "FunctionSummary.ensures", s.ensures.len());
    for c in &s.ensures {
        write_proof_formula_in(buf, pool, c, canonical);
    }
    write_count(buf, "FunctionSummary.params", s.params.len());
    for p in &s.params {
        write_str(buf, pool, p);
    }
    write_u8(buf, u8::from(s.proved));
    // v41: termination measures, then the cross-crate backing of `proved`.
    if contract_surface(pool) {
        write_count(buf, "FunctionSummary.decreases", s.decreases.len());
        for c in &s.decreases {
            write_proof_formula_in(buf, pool, c, canonical);
        }
        match &s.backed_by {
            None => write_u8(buf, 0),
            Some(reference) => {
                write_u8(buf, 1);
                write_extern_ref(buf, pool, reference);
            }
        }
    }
    // v59: the effect summary, presence-tagged. Written on EVERY summary once
    // the module is at v59, so `None` (UNRECORDED) stays spellable.
    if pool.minimum_version() >= EFFECT_SUMMARY_FORMAT_VERSION {
        match &s.effects {
            None => write_u8(buf, 0),
            Some(effects) => {
                write_u8(buf, 1);
                write_effect_summary(buf, effects);
            }
        }
    }
}

/// v59: one [`crate::EffectSummary`] — `reads`, `writes`, then the four flags
/// as strict bool bytes.
fn write_effect_summary(buf: &mut impl BinarySink, effects: &crate::EffectSummary) {
    write_effect_set(buf, &effects.reads);
    write_effect_set(buf, &effects.writes);
    write_u8(buf, u8::from(effects.allocates));
    write_u8(buf, u8::from(effects.frees));
    write_u8(buf, u8::from(effects.may_unwind));
    write_u8(buf, u8::from(effects.io));
}

fn write_effect_set(buf: &mut impl BinarySink, set: &crate::EffectSet) {
    match set {
        crate::EffectSet::Nothing => write_u8(buf, 0),
        crate::EffectSet::Places(places) => {
            write_u8(buf, 1);
            write_count(buf, "EffectSet::Places places", places.len());
            for place in places {
                write_effect_place(buf, place);
            }
        }
        crate::EffectSet::Everything => write_u8(buf, 2),
    }
}

fn write_effect_place(buf: &mut impl BinarySink, place: &crate::EffectPlace) {
    match place {
        crate::EffectPlace::ParamPointee { index } => {
            write_u8(buf, 0);
            write_v32(buf, *index);
        }
        crate::EffectPlace::Global(global) => {
            write_u8(buf, 1);
            write_v32(buf, global.index());
        }
    }
}

fn read_effect_summary(r: &mut Reader<'_>) -> Result<crate::EffectSummary, BinaryError> {
    Ok(crate::EffectSummary {
        reads: read_effect_set(r)?,
        writes: read_effect_set(r)?,
        allocates: r.read_bool()?,
        frees: r.read_bool()?,
        may_unwind: r.read_bool()?,
        io: r.read_bool()?,
    })
}

fn read_effect_set(r: &mut Reader<'_>) -> Result<crate::EffectSet, BinaryError> {
    Ok(match r.read_u8()? {
        0 => crate::EffectSet::Nothing,
        1 => {
            let n = r.read_checked_len()?;
            let mut places = Vec::with_capacity(n);
            for _ in 0..n {
                places.push(read_effect_place(r)?);
            }
            let set = crate::EffectSet::Places(places);
            // One spelling per set (SPEC_RATIFICATIONS §3): the canonicality
            // is CHECKED here like `U128`'s and `Splat`'s, so a decoded
            // module never carries two spellings of one set — the empty set
            // is `Nothing`, and a `Places` list is strictly ascending.
            if !set.is_canonical() {
                return Err(BinaryError::InvalidData(format!(
                    "non-canonical EffectSet::Places({:?}): a place list must be non-empty and \
                     strictly ascending, and the empty set is spelled EffectSet::Nothing \
                     (one-spelling rule, SPEC_RATIFICATIONS §3)",
                    set.places()
                )));
            }
            set
        }
        2 => crate::EffectSet::Everything,
        tag => return Err(BinaryError::InvalidTag(tag)),
    })
}

fn read_effect_place(r: &mut Reader<'_>) -> Result<crate::EffectPlace, BinaryError> {
    Ok(match r.read_u8()? {
        0 => crate::EffectPlace::ParamPointee {
            index: r.read_v32()?,
        },
        1 => crate::EffectPlace::Global(GlobalId::new(r.read_v32()?)),
        tag => return Err(BinaryError::InvalidTag(tag)),
    })
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
    // v41. `decreases = []` means "no measure stated", never "terminates";
    // `backed_by = None` means NOT RECORDED, never "backed locally".
    let (decreases, backed_by) = if r.version >= CONTRACT_SURFACE_FORMAT_VERSION {
        let n = r.read_checked_len()?;
        let mut decreases = Vec::with_capacity(n);
        for _ in 0..n {
            decreases.push(read_proof_formula(r)?);
        }
        let backed_by = match r.read_u8()? {
            0 => None,
            1 => Some(read_extern_ref(r)?),
            tag => return Err(BinaryError::InvalidTag(tag)),
        };
        (decreases, backed_by)
    } else {
        (Vec::new(), None)
    };
    // v59. `effects = None` means UNRECORDED (a caller havocs), never "pure".
    let effects = if r.version >= EFFECT_SUMMARY_FORMAT_VERSION {
        match r.read_u8()? {
            0 => None,
            1 => Some(read_effect_summary(r)?),
            tag => return Err(BinaryError::InvalidTag(tag)),
        }
    } else {
        None
    };
    Ok(FunctionSummary {
        requires,
        ensures,
        params,
        proved,
        decreases,
        backed_by,
        effects,
    })
}

/// v23: producer provenance tag. Stable wire tags (frozen; new producers
/// append): TRust=0, Clean=1, TrustIr=2, TSwift=3, TC=4, Other=5 followed by
/// its string payload.
fn write_producer(buf: &mut impl BinarySink, pool: &SealedStringPool, producer: &Producer) {
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

/// v41 codegen license. The tag encodes the whole `Option`, so `None` has a
/// spelling on the wire: re-serializing a module with an unlicensed function
/// must not turn it into an affirmative `Ungated` refusal.
fn write_body_gate(
    buf: &mut impl BinarySink,
    pool: &SealedStringPool,
    gate: Option<&crate::BodyGate>,
) {
    match gate {
        None => write_u8(buf, 0),
        Some(crate::BodyGate::Ungated) => write_u8(buf, 1),
        Some(crate::BodyGate::Gated {
            authority,
            evidence: None,
        }) => {
            write_u8(buf, 2);
            write_str(buf, pool, authority);
        }
        // v61: the evidenced license. Tag 2 keeps its exact bytes; the
        // evidence is a separate tag, so no pre-v61 reader misreads it.
        Some(crate::BodyGate::Gated {
            authority,
            evidence: Some(evidence),
        }) => {
            write_u8(buf, 3);
            write_str(buf, pool, authority);
            write_v32(buf, evidence.obligation.index());
            write_proof_digest(buf, &evidence.body_digest);
        }
    }
}

fn read_body_gate(r: &mut Reader<'_>) -> Result<Option<crate::BodyGate>, BinaryError> {
    Ok(match r.read_u8()? {
        0 => None,
        1 => Some(crate::BodyGate::Ungated),
        2 => Some(crate::BodyGate::Gated {
            authority: r.read_str()?,
            evidence: None,
        }),
        3 if r.version >= CERTIFICATE_BINDING_FORMAT_VERSION => Some(crate::BodyGate::Gated {
            authority: r.read_str()?,
            evidence: Some(crate::GateEvidence {
                obligation: r.read_proof_id()?,
                body_digest: read_proof_digest(r)?,
            }),
        }),
        tag => return Err(BinaryError::InvalidTag(tag)),
    })
}

fn write_module_import(
    buf: &mut impl BinarySink,
    pool: &SealedStringPool,
    import: &crate::ModuleImport,
) {
    write_str(buf, pool, &import.name);
    write_proof_digest(buf, &import.digest);
    match &import.producer {
        None => write_u8(buf, 0),
        Some(producer) => {
            write_u8(buf, 1);
            write_producer(buf, pool, producer);
        }
    }
    // v44: the identity scheme the digest was recorded under. Written only
    // under a v44+ header, which the writer selects exactly when some row is
    // not V2 — so every row of such a table carries its tag.
    if pool.minimum_version() >= IMPORT_SCHEME_FORMAT_VERSION {
        write_identity_scheme(buf, import.scheme);
    }
}

/// v44 `ModuleImport.scheme` tag (tag space `IdentityScheme`).
fn write_identity_scheme(buf: &mut impl BinarySink, scheme: IdentityScheme) {
    write_u8(
        buf,
        match scheme {
            IdentityScheme::V2 => 0,
            IdentityScheme::V3 => 1,
        },
    );
}

fn read_identity_scheme(r: &mut Reader<'_>) -> Result<IdentityScheme, BinaryError> {
    Ok(match r.read_u8()? {
        0 => IdentityScheme::V2,
        1 => IdentityScheme::V3,
        tag => return Err(BinaryError::InvalidTag(tag)),
    })
}

fn read_module_import(r: &mut Reader<'_>) -> Result<crate::ModuleImport, BinaryError> {
    let name = r.read_str()?;
    let digest = read_proof_digest(r)?;
    let producer = match r.read_u8()? {
        0 => None,
        1 => Some(read_producer(r)?),
        tag => return Err(BinaryError::InvalidTag(tag)),
    };
    // v44 read gate. An older row carries no scheme and was recorded under
    // the legacy v2 domain, so it decodes as V2 — never as the current scheme.
    let scheme = if r.version >= IMPORT_SCHEME_FORMAT_VERSION {
        read_identity_scheme(r)?
    } else {
        IdentityScheme::V2
    };
    Ok(crate::ModuleImport {
        name,
        digest,
        producer,
        scheme,
    })
}

fn write_extern_ref(
    buf: &mut impl BinarySink,
    pool: &SealedStringPool,
    reference: &crate::ExternRef,
) {
    write_v32(buf, reference.module.index());
    write_str(buf, pool, &reference.symbol);
    match reference.obligation {
        None => write_u8(buf, 0),
        Some(obligation) => {
            write_u8(buf, 1);
            write_proof_id(buf, obligation);
        }
    }
}

fn read_extern_ref(r: &mut Reader<'_>) -> Result<crate::ExternRef, BinaryError> {
    let module = crate::ImportId::new(r.read_v32()?);
    let symbol = r.read_str()?;
    let obligation = match r.read_u8()? {
        0 => None,
        1 => Some(r.read_proof_id()?),
        tag => return Err(BinaryError::InvalidTag(tag)),
    };
    Ok(crate::ExternRef {
        module,
        symbol,
        obligation,
    })
}

fn write_function<X: WireExt>(
    buf: &mut impl BinarySink,
    pool: &SealedStringPool,
    func: &FunctionG<X>,
    name: Option<&str>,
    canonical: Option<&FunctionCanonicalPlan>,
    retain_source_provenance: bool,
    include_codegen_license: bool,
) {
    write_func_id(buf, func.id);
    write_str(buf, pool, name.unwrap_or(&func.name));
    write_func_ty_id(buf, func.ty);
    write_block_id(buf, func.entry);
    write_count(buf, "Function.blocks", func.blocks.len());
    if let Some(canonical) = canonical {
        for &block_index in &canonical.block_order {
            write_block(
                buf,
                pool,
                Some(canonical),
                func.id,
                &func.blocks[block_index],
            );
        }
    } else {
        for block in &func.blocks {
            write_block(buf, pool, None, func.id, block);
        }
    }
    write_proof_annotation_list(buf, pool, &func.proofs);
    write_calling_conv(buf, &func.calling_conv);
    write_linkage(buf, &func.linkage);
    write_func_attrs(
        buf,
        pool,
        &func.attrs,
        canonical.map(|projection| projection.param_attrs_len),
    );
    // v18+: separate-compilation contract. Presence byte then payload, so a
    // body-less declaration carrying a summary round-trips.
    match &func.summary {
        None => write_u8(buf, 0),
        Some(summary) => {
            write_u8(buf, 1);
            write_function_summary(buf, pool, summary, canonical);
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
            write_count(buf, "Function.value_names", names.len());
            for (v, n) in names {
                write_projected_value_id(buf, canonical, *v);
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
            write_count(buf, "Function.scopes", scopes.len());
            for (index, sc) in scopes.iter().enumerate() {
                // WS4.19: fail closed. The chain has no carrier at any
                // version yet, and dropping it would make the round trip a
                // silent lie. Refused by this arm, at its untruncated
                // position (`Module::wire_image_refusal` is this walk).
                if sc.inlined_at.is_some() {
                    buf.refuse(WireRefusal::InlinedScopeChain {
                        function: func.id.index(),
                        scope: index,
                    });
                }
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
    let source_provenance = projected_source_provenance(func, canonical, retain_source_provenance);
    match source_provenance {
        None => write_u8(buf, 0),
        Some(provenance) => {
            write_u8(buf, 1);
            write_v32(buf, provenance.schema);
            write_proof_digest(buf, &provenance.compiler_source_digest);
            write_proof_digest(buf, &provenance.semantic_body_digest);
            write_proof_digest(buf, &provenance.binding_digest);
            write_count(buf, "SourceProvenance.loops", provenance.loops.len());
            for source_loop in &provenance.loops {
                write_v32(buf, source_loop.source_loop_id);
                write_v32(buf, source_loop.hir_local_id);
                write_block_id(buf, source_loop.header);
                write_count(
                    buf,
                    "SourceLoopProvenance.bindings",
                    source_loop.bindings.len(),
                );
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
    // v41: codegen license, then the display path. A projection that omits
    // the license still has to spell it once some OTHER v41 feature holds the
    // image at v41: tag 0 ("no licensing claim") and an absent path, so the
    // image decodes as an unlicensed module and, matching the collector, no
    // authority or path string is looked up in the pool.
    if contract_surface(pool) {
        if include_codegen_license {
            write_body_gate(buf, pool, func.body_gate.as_ref());
            match &func.display_path {
                None => write_u8(buf, 0),
                Some(path) => {
                    write_u8(buf, 1);
                    write_str(buf, pool, path);
                }
            }
        } else {
            write_body_gate(buf, pool, None);
            write_u8(buf, 0);
        }
    }
    // v45 (WS3.10): section, visibility, retention — `Global`'s v41 triple.
    if abi_surface(pool) {
        write_opt_str(buf, pool, func.section.as_deref());
        write_visibility(buf, &func.visibility);
        write_bool(buf, func.retained);
    }
}

fn read_function<X: WireExt>(
    r: &mut Reader<'_>,
    version: u32,
) -> Result<FunctionG<X>, BinaryError> {
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
                    scopes.push(ScopeData {
                        parent,
                        span,
                        inlined_at: None,
                    });
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
    // v41: a pre-v41 blob consumes neither byte. For `body_gate` that decodes
    // to `None` — "no licensing claim" — never `Ungated`.
    let (body_gate, display_path) = if version >= CONTRACT_SURFACE_FORMAT_VERSION {
        let gate = read_body_gate(r)?;
        let path = match r.read_u8()? {
            0 => None,
            1 => Some(r.read_str()?),
            tag => return Err(BinaryError::InvalidTag(tag)),
        };
        (gate, path)
    } else {
        (None, None)
    };
    // v45: an older blob consumes none of these and means "no section,
    // default visibility, not retained" — the pre-v45 world.
    let (section, visibility, retained) = if version >= ABI_SURFACE_FORMAT_VERSION {
        (read_opt_str(r)?, read_visibility(r)?, r.read_bool()?)
    } else {
        (None, Visibility::Default, false)
    };
    Ok(FunctionG {
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
        body_gate,
        display_path,
        section,
        visibility,
        retained,
    })
}

// ---------------------------------------------------------------------------
// Public API
// ---------------------------------------------------------------------------

fn collect_lineage_strings(nodes: &[ProofLineageNode]) -> SealedStringPool {
    let mut pool = StringPoolBuilder::new();
    for node in nodes {
        pool.intern(&node.transform.name);
        pool.intern(&node.transform.producer);
        pool.intern(&node.transform.version);
        for cert in &node.certificates {
            pool.intern(&cert.prover);
        }
        if let Some(replay) = &node.replay {
            pool.intern(&replay.engine);
            pool.intern(&replay.invocation);
        }
    }
    pool.seal()
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

    let pool = collect_lineage_strings(&nodes);
    write_count(&mut buf, "string table", pool.strings().len());
    for s in pool.strings() {
        write_raw_str(&mut buf, s);
    }

    write_count(&mut buf, "ProofLineageManifest nodes", nodes.len());
    for node in &nodes {
        write_proof_lineage_node(&mut buf, &pool, node);
    }

    let mut roots = manifest.roots.clone();
    roots.sort();
    write_count(&mut buf, "ProofLineageManifest.roots", roots.len());
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
    let magic = r.read_array::<{ PROOF_LINEAGE_MAGIC.len() }>()?;
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
        for _ in 0..pool_size {
            strings.push(r.read_raw_str()?);
        }
        r.pool = Some(strings);
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
    buf: &mut impl BinarySink,
    producer: &crate::request::NativeBundleProducer,
) {
    use crate::request::NativeBundleProducer;
    let tag: u8 = match producer {
        NativeBundleProducer::TRust => 0,
        NativeBundleProducer::TSwift => 1,
        NativeBundleProducer::TC => 2,
        NativeBundleProducer::TrustIr => 3,
        NativeBundleProducer::Clean => 4,
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
        4 => Ok(NativeBundleProducer::Clean),
        t => Err(BinaryError::InvalidTag(t)),
    }
}

fn write_native_adapter_input(
    buf: &mut impl BinarySink,
    input: &crate::request::NativeAdapterInput,
) {
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
    // WS5.3b: the module segment is written by `serialize_module`, which
    // refuses a completeness claim (no binary version carries one yet). This
    // entry point keeps its own pinned message for it.
    if bundle.module.completeness_claim_unencodable() {
        return Err(BinaryError::Unencodable(
            "native bundle binary codec cannot encode a module completeness claim \
             (Module.completeness, WS5.3b: no binary carrier yet); use serde JSON/MessagePack",
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
    // Every other construct or count the writer has no image for is refused
    // by the writer's own arm (`serialize_module` runs it in check mode
    // first); the two pinned refusals above keep their messages.
    let module = serialize_module(&bundle.module).map_err(|_| {
        BinaryError::Unencodable(
            "native bundle binary codec cannot encode the module: the binary writer refuses \
             it (Module::wire_image_refusal names the construct)",
        )
    })?;
    buf.extend_from_slice(&module);
    Ok(buf)
}

pub fn deserialize_native_verification_bundle(
    bytes: &[u8],
) -> Result<crate::request::NativeVerificationBundle, BinaryError> {
    // New envelope: TMVB header carries the scalar metadata losslessly, then
    // the TMPL lineage and TRUST_IR module segments follow.
    if bytes.starts_with(NATIVE_BUNDLE_MAGIC) {
        let mut r = Reader::new(bytes);
        let _magic = r.read_array::<{ NATIVE_BUNDLE_MAGIC.len() }>()?;
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

/// Serialize a [`crate::spec::SpecModule`] (current v27 layout). Every string
/// is spelled by `write_str`, which only INDEXES the sealed table; each one is
/// interned up front by [`collect_spec_module_strings`], and one that walk
/// misses panics in the writer instead of reaching the wire.
fn write_spec_module(
    buf: &mut impl BinarySink,
    pool: &SealedStringPool,
    sm: &crate::spec::SpecModule,
) {
    use crate::spec::SpecOrigin;

    write_str(buf, pool, &sm.name);

    write_count(buf, "SpecModule.vars", sm.vars.len());
    for v in &sm.vars {
        write_str(buf, pool, &v.name);
        write_str(buf, pool, &v.ty);
        // v46: the declared wire sort, inside the per-variable record (the
        // same shape v26's per-anchor `function` took).
        if pool.minimum_version() >= SPEC_CARRIER_FORMAT_VERSION {
            match &v.sort {
                None => write_u8(buf, 0),
                Some(sort) => {
                    write_u8(buf, 1);
                    write_clause_sort(buf, pool, sort);
                }
            }
        }
    }

    write_count(buf, "SpecModule.actions", sm.actions.len());
    for a in &sm.actions {
        write_str(buf, pool, a);
    }

    write_count(buf, "SpecModule.invariants", sm.invariants.len());
    for inv in &sm.invariants {
        write_str(buf, pool, &inv.name);
        write_str(buf, pool, &inv.formula);
        // v46: the typed first-order carrier.
        if pool.minimum_version() >= SPEC_CARRIER_FORMAT_VERSION {
            match &inv.typed {
                None => write_u8(buf, 0),
                Some(typed) => {
                    write_u8(buf, 1);
                    write_proof_formula(buf, pool, typed);
                }
            }
        }
    }

    write_count(buf, "SpecModule.anchors", sm.anchors.len());
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

    write_count(buf, "SpecModule.waivers", sm.waivers.len());
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
    // Temporal properties (v46). Appended after the v27 enforcement byte so
    // every older prefix stays byte-identical; the reader only consumes this
    // block when `version >= 46`.
    if pool.minimum_version() >= SPEC_CARRIER_FORMAT_VERSION {
        write_temporal(buf, pool, &sm.temporal);
    }
}

/// Serialize the `temporal` block of a [`crate::spec::SpecModule`] (v46).
fn write_temporal(
    buf: &mut impl BinarySink,
    pool: &SealedStringPool,
    temporal: &[crate::spec::SpecTemporal],
) {
    use crate::spec::TemporalForm;
    write_count(buf, "SpecModule.temporal", temporal.len());
    for property in temporal {
        write_str(buf, pool, &property.name);
        match &property.form {
            TemporalForm::Always(p) => {
                write_u8(buf, 0);
                write_proof_formula(buf, pool, p);
            }
            TemporalForm::Eventually(p) => {
                write_u8(buf, 1);
                write_proof_formula(buf, pool, p);
            }
            TemporalForm::LeadsTo(p, q) => {
                write_u8(buf, 2);
                write_proof_formula(buf, pool, p);
                write_proof_formula(buf, pool, q);
            }
            TemporalForm::WeakFair { action, relation }
            | TemporalForm::StrongFair { action, relation } => {
                write_u8(
                    buf,
                    if matches!(property.form, TemporalForm::WeakFair { .. }) {
                        3
                    } else {
                        4
                    },
                );
                write_str(buf, pool, action);
                match relation {
                    None => write_u8(buf, 0),
                    Some(relation) => {
                        write_u8(buf, 1);
                        write_proof_formula(buf, pool, relation);
                    }
                }
            }
        }
    }
}

/// Serialize the `proofs` block of a [`crate::spec::SpecModule`] (v14+).
fn write_proofs(
    buf: &mut impl BinarySink,
    pool: &SealedStringPool,
    proofs: &[crate::spec::SpecProof],
) {
    use crate::spec::ProofKind;
    write_count(buf, "SpecModule.proofs", proofs.len());
    for p in proofs {
        write_str(buf, pool, &p.machine);
        write_str(buf, pool, &p.action);
        write_str(buf, pool, &p.proof_name);
        match &p.kind {
            ProofKind::Kani => write_u8(buf, 0),
            // v46. Selection is driven by the string collector, which raises
            // the collected minimum version when a `CleanTheorem` binding occurs.
            ProofKind::CleanTheorem { name } => {
                write_u8(buf, 1);
                write_str(buf, pool, name);
            }
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
        SpecProjectionTarget, SpecProof, SpecTemporal, SpecVar, SpecWaiver, TemporalForm,
    };

    let name = r.read_str()?;

    let var_count = r.read_checked_len()?;
    let mut vars = Vec::with_capacity(var_count);
    for _ in 0..var_count {
        let vname = r.read_str()?;
        let vty = r.read_str()?;
        let sort = if r.version >= SPEC_CARRIER_FORMAT_VERSION {
            match r.read_u8()? {
                0 => None,
                1 => Some(read_clause_sort(r)?),
                t => return Err(BinaryError::InvalidTag(t)),
            }
        } else {
            None
        };
        vars.push(SpecVar {
            name: vname,
            ty: vty,
            sort,
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
        let typed = if r.version >= SPEC_CARRIER_FORMAT_VERSION {
            match r.read_u8()? {
                0 => None,
                1 => Some(read_proof_formula(r)?),
                t => return Err(BinaryError::InvalidTag(t)),
            }
        } else {
            None
        };
        invariants.push(SpecInvariant {
            name: iname,
            formula,
            typed,
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
                1 if r.version >= SPEC_CARRIER_FORMAT_VERSION => ProofKind::CleanTheorem {
                    name: r.read_str()?,
                },
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
    // Temporal properties (v46). Pre-v46 blobs end after `enforcement`, so
    // they default to empty.
    let temporal = if r.version >= SPEC_CARRIER_FORMAT_VERSION {
        let count = r.read_checked_len()?;
        let mut temporal = Vec::with_capacity(count);
        for _ in 0..count {
            let name = r.read_str()?;
            let form = match r.read_u8()? {
                0 => TemporalForm::Always(read_proof_formula(r)?),
                1 => TemporalForm::Eventually(read_proof_formula(r)?),
                2 => {
                    let p = read_proof_formula(r)?;
                    let q = read_proof_formula(r)?;
                    TemporalForm::LeadsTo(p, q)
                }
                tag @ (3 | 4) => {
                    let action = r.read_str()?;
                    let relation = match r.read_u8()? {
                        0 => None,
                        1 => Some(read_proof_formula(r)?),
                        t => return Err(BinaryError::InvalidTag(t)),
                    };
                    if tag == 3 {
                        TemporalForm::WeakFair { action, relation }
                    } else {
                        TemporalForm::StrongFair { action, relation }
                    }
                }
                t => return Err(BinaryError::InvalidTag(t)),
            };
            temporal.push(SpecTemporal { name, form });
        }
        temporal
    } else {
        Vec::new()
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
        temporal,
    })
}

fn write_module_with_pool(
    module: &Module,
    view: Option<&ModuleWireView>,
    pool: &SealedStringPool,
    mut buf: &mut impl BinarySink,
) {
    // WS5.3b: fail closed. A completeness claim has no carrier at any version
    // yet, and dropping it would make a `Partial` module read back as "no
    // claim". Refused by this arm, whatever the view
    // (`Module::wire_image_refusal` is this walk).
    if module.completeness_claim_unencodable() {
        buf.refuse(WireRefusal::CompletenessClaim);
    }

    // Header
    buf.extend_from_slice(MAGIC);
    write_u32(&mut buf, pool.minimum_version());

    write_count(&mut buf, "string table", pool.strings().len());
    for s in pool.strings() {
        write_raw_str(&mut buf, s);
    }

    write_module_sections(module, view, pool, buf);
}

/// The module section sequence after the header and the string pool — at
/// either level: a module blob (`X = NoExt`) and a template blob (`X =
/// TemplateRef`, amendment S) share it, written by these same writers.
fn write_module_sections<X: WireExt>(
    module: &ModuleG<X>,
    view: Option<&ModuleWireView>,
    pool: &SealedStringPool,
    mut buf: &mut impl BinarySink,
) {
    let include_proof_sidecars = view.is_none_or(ModuleWireView::includes_proof_sidecars);
    // Module name
    write_str(
        &mut buf,
        pool,
        view.map_or(&module.name, |view| view.module_name(module)),
    );

    // Func types
    write_count(&mut buf, "Module.func_types", module.func_types.len());
    for (signature, ft) in module.func_types.iter().enumerate() {
        write_func_ty(&mut buf, pool, signature, ft);
    }

    // Structs
    write_count(&mut buf, "Module.structs", module.structs.len());
    for sd in &module.structs {
        write_struct_def(&mut buf, pool, sd);
    }

    // Enums
    write_count(&mut buf, "Module.enums", module.enums.len());
    for ed in &module.enums {
        write_enum_def(&mut buf, pool, ed);
    }

    // Records
    write_count(&mut buf, "Module.records", module.records.len());
    for rd in &module.records {
        write_record_def(&mut buf, pool, rd);
    }

    // Closure types
    write_count(&mut buf, "Module.closure_types", module.closure_types.len());
    for ct in &module.closure_types {
        write_closure_ty(&mut buf, pool, ct);
    }

    // Globals
    write_count(&mut buf, "Module.globals", module.globals.len());
    for (index, global) in module.globals.iter().enumerate() {
        let name = view.map(|view| view.global_name(global, index));
        write_global(&mut buf, pool, global, name);
    }

    // Types
    write_count(&mut buf, "Module.types", module.types.len());
    for ty in &module.types {
        write_ty(&mut buf, pool, ty);
    }

    // Functions
    write_count(&mut buf, "Module.functions", module.functions.len());
    if let Some(view) = view {
        for &index in &view.function_order {
            let function = &module.functions[index];
            write_function(
                &mut buf,
                pool,
                function,
                Some(view.function_name(function, index)),
                view.canonical_function(index),
                view.retain_source_provenance,
                view.includes_codegen_license(),
            );
        }
    } else {
        for function in &module.functions {
            write_function(&mut buf, pool, function, None, None, false, true);
        }
    }

    // Proof obligations
    let obligation_count = if include_proof_sidecars {
        view.map_or(module.proof_obligations.len(), |view| {
            view.obligation_rows.len()
        })
    } else {
        0
    };
    write_count(&mut buf, "Module.proof_obligations", obligation_count);
    if include_proof_sidecars {
        if let Some(view) = view {
            // WS4.4 (NEW-1): an obligation's `Value` bindings follow its
            // owning function's canonical renumbering, resolved exactly as
            // `format::into_canonical` resolves them.
            let positions = view
                .canonical_functions
                .is_some()
                .then(|| crate::canonicalize::unique_function_positions(module));
            for &index in &view.obligation_rows {
                let obligation = &module.proof_obligations[index];
                let plan = positions.as_ref().and_then(|positions| {
                    crate::canonicalize::obligation_owner(obligation)
                        .and_then(|owner| positions.get(&owner))
                        .and_then(|&position| view.canonical_function(position))
                });
                write_proof_obligation(&mut buf, pool, obligation, plan);
            }
        } else {
            for obligation in &module.proof_obligations {
                write_proof_obligation(&mut buf, pool, obligation, None);
            }
        }
    }

    // Proof certificates
    let certificate_count = if include_proof_sidecars {
        module.proof_certificates.len()
    } else {
        0
    };
    write_count(&mut buf, "Module.proof_certificates", certificate_count);
    if include_proof_sidecars {
        for cert in &module.proof_certificates {
            write_proof_certificate(&mut buf, pool, cert);
        }
    }

    // Target info
    match &module.target_info {
        None => write_u8(&mut buf, 0),
        Some(ti) => {
            write_u8(&mut buf, 1);
            write_str(&mut buf, pool, &ti.triple);
            write_v32(&mut buf, ti.pointer_size);
            write_endianness(&mut buf, &ti.endianness);
            // ABI pinning (VERSION >= 20): stable ABI id + struct-passing
            // policy. Digest-bearing: these bytes feed Module::stable_digest.
            write_opt_str(&mut buf, pool, ti.abi.as_deref());
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
    write_count(&mut buf, "Module.files", module.files.len());
    for path in &module.files {
        let spelled = pool.debug_file(path);
        write_str(&mut buf, pool, spelled);
    }

    // Obligation-diagnostics sidecar (VERSION >= 11). Additive trailing section.
    let diagnostic_count = if include_proof_sidecars {
        module.obligation_diagnostics.len()
    } else {
        0
    };
    write_count(&mut buf, "Module.obligation_diagnostics", diagnostic_count);
    if include_proof_sidecars {
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
            write_str(&mut buf, pool, &d.message);
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
                    write_str(&mut buf, pool, detail);
                }
            }
        }
    }

    // Spec modules (VERSION >= 13). Additive trailing section; the current
    // writer always emits it, older readers stop before reaching it.
    write_count(&mut buf, "Module.spec_modules", module.spec_modules.len());
    for sm in &module.spec_modules {
        write_spec_module(&mut buf, pool, sm);
    }

    // Typed value model (VERSION >= 30). Two additive trailing sections.
    // Universes FIRST: a predicate may cite a `UnivId`, so the referent table
    // precedes the referencing one.
    write_count(&mut buf, "Module.universes", module.universes.len());
    for u in &module.universes {
        write_universe(&mut buf, pool, u);
    }
    write_count(&mut buf, "Module.predicates", module.predicates.len());
    for p in &module.predicates {
        write_pred(&mut buf, pool, p);
    }
    // v41: module-level `global_asm!` blocks, then the cross-crate import table.
    if contract_surface(pool) {
        write_count(&mut buf, "Module.global_asm", module.global_asm.len());
        for asm in &module.global_asm {
            write_str(&mut buf, pool, asm);
        }
        write_count(&mut buf, "Module.imports", module.imports.len());
        for import in &module.imports {
            write_module_import(&mut buf, pool, import);
        }
    }
    if pool.minimum_version() >= TUPLE_LAYOUT_FORMAT_VERSION {
        write_count(&mut buf, "Module.tuple_layouts", module.tuple_layouts.len());
        for desc in &module.tuple_layouts {
            write_v32(&mut buf, desc.tuple_type.index());
            write_v64(&mut buf, desc.size);
            write_v64(&mut buf, desc.align);
            write_count(
                &mut buf,
                "TupleLayoutDescriptor.field_offsets",
                desc.field_offsets.len(),
            );
            for offset in &desc.field_offsets {
                write_v64(&mut buf, *offset);
            }
        }
    }
    // v55 (amendment D): the drop-glue table, rows in the canonical
    // (ascending-glue) order the module holds them in.
    if pool.minimum_version() >= DROP_GLUE_FORMAT_VERSION {
        write_count(&mut buf, "Module.drop_glue", module.drop_glue.len());
        for entry in &module.drop_glue {
            write_func_id(&mut buf, entry.glue);
            write_ty(&mut buf, pool, &entry.ty);
        }
    }

    // v58 declared closure layouts. Written AFTER the v55 drop-glue table (and
    // so after the v42 tuple table, whose record shape it shares), so a module
    // carrying all three keeps one section order.
    if pool.minimum_version() >= NOMINAL_IDENTITY_FORMAT_VERSION {
        write_count(
            &mut buf,
            "Module.closure_layouts",
            module.closure_layouts.len(),
        );
        for desc in &module.closure_layouts {
            write_v32(&mut buf, desc.closure.index());
            write_v64(&mut buf, desc.size);
            write_v64(&mut buf, desc.align);
            write_count(
                &mut buf,
                "ClosureLayoutDescriptor.capture_offsets",
                desc.capture_offsets.len(),
            );
            for offset in &desc.capture_offsets {
                write_v64(&mut buf, *offset);
            }
            if pool.minimum_version() >= CLOSURE_ORIGIN_FORMAT_VERSION {
                write_type_origin(&mut buf, pool, desc.origin.as_ref());
            }
        }
    }
    // v70: the blob table, after the v58 closure layouts, rows in the
    // canonical (strictly ascending digest) order the module holds them in.
    if pool.minimum_version() >= TENSOR_BLOB_FORMAT_VERSION {
        write_count(&mut buf, "Module.blobs", module.blobs.len());
        for blob in &module.blobs {
            buf.extend_from_slice(&blob.digest.0);
            write_count(&mut buf, "Blob.data", blob.data.len());
            buf.extend_from_slice(&blob.data);
        }
    }
}

#[cfg(test)]
fn write_module(module: &Module, buf: &mut impl BinarySink) {
    let pool = collect_strings(module);
    write_module_with_pool(module, None, &pool, buf);
}

fn update_sha256_with_module_encoding(
    module: &Module,
    view: Option<&ModuleWireView>,
    pool: &SealedStringPool,
    hasher: &mut Sha256,
) {
    let mut sink = Sha256UpdateSink(hasher);
    stream_module_with_pool(module, view, pool, &mut sink);
}

fn stream_module_with_pool(
    module: &Module,
    view: Option<&ModuleWireView>,
    pool: &SealedStringPool,
    sink: &mut impl BinarySink,
) {
    let mut buffered = BufferedBinarySink::<_, BINARY_STREAM_BUFFER_BYTES>::new(sink);
    write_module_with_pool(module, view, pool, &mut buffered);
    buffered.finish();
}

/// A prepared, allocation-bounded walk over a module's exact binary encoding.
///
/// Construction collects the deterministic string pool but does not walk the
/// wire body. Length is counted lazily only when requested (or when required
/// by a length-prefixed digest); prefix-only hashing remains a single wire
/// pass. No operation allocates a whole-module byte buffer unless
/// [`Self::to_vec`] is explicitly requested.
pub struct ModuleBinaryPlan<'m> {
    module: &'m Module,
    pool: SealedStringPool,
    encoded_len: Option<usize>,
}

impl<'m> ModuleBinaryPlan<'m> {
    /// Prepare the exact minimum-lossless-version binary encoding of `module`.
    pub fn new(module: &'m Module) -> Self {
        Self {
            module,
            pool: collect_strings(module),
            encoded_len: None,
        }
    }

    /// Prepare the IDENTITY image of `module` under `scheme`: the exact
    /// encoding for [`IdentityScheme::V2`], and for [`IdentityScheme::V3`]
    /// the same encoding with every `Module.files` string written as `""`
    /// (the table length kept). The V3 image is what the portable module
    /// identity hashes; it is never a serialization of the module — the
    /// projection is a constructor argument to the pool the collection walk
    /// is handed, and this is the only caller that passes it.
    pub(crate) fn identity(module: &'m Module, scheme: IdentityScheme) -> Self {
        Self {
            module,
            pool: collect_strings_into(
                module,
                None,
                StringPoolBuilder::with_blanked_debug_files(scheme.blanks_debug_file_paths()),
            ),
            encoded_len: None,
        }
    }

    /// Return the exact number of bytes emitted by this plan, counting lazily.
    pub fn encoded_len(&mut self) -> usize {
        if let Some(encoded_len) = self.encoded_len {
            return encoded_len;
        }
        let mut counter = CountingSink::default();
        write_module_with_pool(self.module, None, &self.pool, &mut counter);
        self.encoded_len = Some(counter.len);
        counter.len
    }

    /// Visit the exact encoding in order without materializing it contiguously.
    /// Scalar fields are coalesced through a fixed-size buffer; chunk boundaries
    /// are an implementation detail and are not stable API.
    pub fn for_each_chunk(&mut self, mut callback: impl FnMut(&[u8])) {
        let mut sink = CallbackSink(&mut callback);
        stream_module_with_pool(self.module, None, &self.pool, &mut sink);
    }

    /// The one pre-check over this plan's pool: the writer in check mode
    /// ([`CheckSink`]). The first refusal by precedence, or the exact length
    /// (memoized for [`Self::encoded_len`]).
    fn check(&mut self) -> Result<usize, BinaryProjectionError> {
        let mut sink = CheckSink::default();
        write_module_with_pool(self.module, None, &self.pool, &mut sink);
        let len = sink.into_result()?;
        self.encoded_len = Some(len);
        Ok(len)
    }

    /// Stream the exact encoding into an arbitrary [`std::io::Write`],
    /// coalescing scalar wire fields through a fixed-size buffer, in ONE wire
    /// pass (no length prepass).
    ///
    /// # Errors
    ///
    /// The writer's I/O error, or `InvalidData` carrying the
    /// [`BinaryProjectionError`] when the module has no wire image. The
    /// streaming sink records the refusal (never a panic) and the walk
    /// finishes, so the bytes already handed to `writer` are NOT an image:
    /// a caller discards them on `Err`, as on any I/O error.
    pub fn write_to<W: IoWrite + ?Sized>(&mut self, writer: &mut W) -> io::Result<()> {
        let mut sink = IoSink::new(writer);
        stream_module_with_pool(self.module, None, &self.pool, &mut sink);
        sink.finish()
    }

    /// Materialize the exact encoding for compatibility with byte consumers.
    ///
    /// # Errors
    ///
    /// [`BinaryProjectionError`] when the module has no wire image: a
    /// construct the writer's own arm refuses, or a count past the format's
    /// `u32`. Checked by one counting walk before anything is allocated, so
    /// a refused image is never materialized.
    // `&mut self` only to memoize `encoded_len`; the sealed pool is read
    // through `&`. The `to_vec` name is the public byte-consumer API
    // trust/trust-cg call.
    #[allow(clippy::wrong_self_convention)]
    pub fn to_vec(&mut self) -> Result<Vec<u8>, BinaryProjectionError> {
        let len = self.check()?;
        let mut sink = BlobSink::with_capacity(len);
        write_module_with_pool(self.module, None, &self.pool, &mut sink);
        let bytes = sink.finish()?;
        debug_assert_eq!(bytes.len(), len);
        Ok(bytes)
    }

    /// Hash `prefix || exact_encoding` in one wire walk and no encoded-size
    /// allocation. This is useful for established identities whose framing
    /// does not put the payload length before the payload.
    pub fn sha256_prefixed(&mut self, prefix: &[u8]) -> [u8; 32] {
        let mut hasher = Sha256::new();
        hasher.update(prefix);
        update_sha256_with_module_encoding(self.module, None, &self.pool, &mut hasher);
        hasher.finalize().into()
    }

    /// Hash the exact encoding with TrustIR's canonical domain framing.
    pub fn sha256_domain(&mut self, domain: &str) -> ProofDigest {
        let domain_len = u64::try_from(domain.len())
            .expect("digest domain length exceeds canonical u64 framing");
        let payload_len = u64::try_from(self.encoded_len())
            .expect("digest payload length exceeds canonical u64 framing");
        let mut hasher = Sha256::new();
        hasher.update(b"trust-ir.sha256-domain.v1\0");
        hasher.update(domain_len.to_be_bytes());
        hasher.update(domain.as_bytes());
        hasher.update(payload_len.to_be_bytes());
        update_sha256_with_module_encoding(self.module, None, &self.pool, &mut hasher);
        ProofDigest::sha256(hasher.finalize().into())
    }
}

/// Prepared borrowed projection of a module's exact binary identity image.
///
/// The plan owns ordering/remap metadata, synthesized symbol names, and its
/// encoding string pool; the module, functions, blocks, instructions,
/// constants, and proof rows are never cloned. All output modes use the same
/// binary writer as [`serialize_module`].
///
/// A projected image is not an authoritative transformed [`Module`]: this API
/// neither constructs proof lineage nor rewrites caller-owned manifests,
/// verification bundles, cache records, or other external references. Even an
/// image that can be deserialized as a module must therefore remain scoped to
/// the projection recipe that produced it. Use [`Self::sha256_prefixed`] with
/// a projection-specific, versioned prefix for identity; [`Module::stable_digest`]
/// remains the authority for a module's canonical domain-separated identity.
///
/// `sha256_domain` is intentionally unavailable on this type, preventing a
/// projected image from being minted under a module-identity domain
/// (`trust_ir.module.v2` / `trust_ir.module.v3`) by accident.
///
/// ```compile_fail
/// use trust_ir::binary::{ModuleBinaryOptions, ProjectedModuleBinaryPlan};
/// use trust_ir::Module;
///
/// let module = Module::new("source");
/// let mut projection = ProjectedModuleBinaryPlan::try_new(
///     &module,
///     ModuleBinaryOptions::default(),
/// ).unwrap();
/// let _ = projection.sha256_domain("trust_ir.module.v2");
/// ```
pub struct ProjectedModuleBinaryPlan<'m> {
    module: &'m Module,
    view: ModuleWireView,
    pool: SealedStringPool,
    encoded_len: Option<usize>,
}

impl<'m> ProjectedModuleBinaryPlan<'m> {
    /// Prepare a deterministic identity projection, rejecting module-local
    /// references to omitted obligation rows before any bytes can be observed.
    /// External sidecars and bundles are outside this validation boundary.
    pub fn try_new(
        module: &'m Module,
        options: ModuleBinaryOptions<'_>,
    ) -> Result<Self, BinaryProjectionError> {
        // The one pre-check: the writer over the SOURCE module in check mode,
        // before any projection can drop what it would refuse.
        if let Some(refusal) = module.wire_image_refusal() {
            return Err(refusal);
        }
        let view = ModuleWireView::try_new(module, options)?;
        let pool = collect_strings_with_view(module, Some(&view));
        if pool.minimum_version() > BASE_FORMAT_VERSION
            && matches!(
                options.body,
                ModuleBinaryBody::RawV38 | ModuleBinaryBody::CanonicalV38
            )
        {
            // Every version the writer can select above the projected v38 must
            // map to a refusal here; the highest requirement wins so the error
            // names the feature that actually forbids the projection.
            return Err(if pool.minimum_version() >= TENSOR_BLOB_FORMAT_VERSION {
                BinaryProjectionError::TensorBlobRequiresV70
            } else if pool.minimum_version() >= TENSOR_GATHER_SCATTER_FORMAT_VERSION {
                BinaryProjectionError::TensorGatherScatterRequiresV69
            } else if pool.minimum_version() >= TENSOR_MAP_REDUCE_VIEW_FORMAT_VERSION {
                BinaryProjectionError::TensorMapReduceViewRequiresV68
            } else if pool.minimum_version() >= TENSOR_FORMAT_VERSION {
                BinaryProjectionError::TensorRequiresV67
            } else if pool.minimum_version() >= CLOSURE_ORIGIN_FORMAT_VERSION {
                BinaryProjectionError::ClosureOriginRequiresV66
            } else if pool.minimum_version() >= STORAGE_LAYOUT_FORMAT_VERSION {
                BinaryProjectionError::StorageRequiresV64
            } else if pool.minimum_version() >= MAKE_CLOSURE_FORMAT_VERSION {
                BinaryProjectionError::MakeClosureRequiresV63
            } else if pool.minimum_version() >= PARAM_POINTEE_PLACE_FORMAT_VERSION {
                BinaryProjectionError::ParamPointeePlaceRequiresV62
            } else if pool.minimum_version() >= CERTIFICATE_BINDING_FORMAT_VERSION {
                BinaryProjectionError::CertificateBindingRequiresV61
            } else if pool.minimum_version() >= SIGNATURE_ABI_FORMAT_VERSION {
                BinaryProjectionError::SignatureAbiRequiresCurrentFormat
            } else if pool.minimum_version() >= EFFECT_SUMMARY_FORMAT_VERSION {
                BinaryProjectionError::EffectSummaryRequiresV59
            } else if pool.minimum_version() >= NOMINAL_IDENTITY_FORMAT_VERSION {
                BinaryProjectionError::NominalIdentityRequiresV58
            } else if pool.minimum_version() >= UNWIND_TWINS_FORMAT_VERSION {
                BinaryProjectionError::UnwindTwinsRequiresV56
            } else if pool.minimum_version() >= DROP_GLUE_FORMAT_VERSION {
                BinaryProjectionError::DropGlueRequiresV55
            } else if pool.minimum_version() >= PANIC_SITE_FORMAT_VERSION {
                BinaryProjectionError::PanicSiteRequiresV54
            } else if pool.minimum_version() >= CALL_UNWIND_BOUNDARY_FORMAT_VERSION {
                BinaryProjectionError::CallUnwindBoundaryRequiresV53
            } else if pool.minimum_version() >= ASSERT_KIND_FORMAT_VERSION {
                BinaryProjectionError::AssertKindRequiresV52
            } else if pool.minimum_version() >= INST_WIRE_BATCH_FORMAT_VERSION {
                BinaryProjectionError::InstWireBatchRequiresV51
            } else if pool.minimum_version() >= ARRAY_SPLAT_FORMAT_VERSION {
                BinaryProjectionError::ArraySplatRequiresV50
            } else if pool.minimum_version() >= UNINIT_LANE_FORMAT_VERSION {
                BinaryProjectionError::UninitLaneRequiresV49
            } else if pool.minimum_version() >= WEAK_CMPXCHG_FORMAT_VERSION {
                BinaryProjectionError::WeakCmpXchgRequiresV48
            } else if pool.minimum_version() >= DROP_INST_FORMAT_VERSION {
                BinaryProjectionError::DropInstRequiresV47
            } else if pool.minimum_version() >= SPEC_CARRIER_FORMAT_VERSION {
                BinaryProjectionError::SpecCarrierRequiresV46
            } else if pool.minimum_version() >= ABI_SURFACE_FORMAT_VERSION {
                BinaryProjectionError::AbiSurfaceRequiresV45
            } else if pool.minimum_version() >= IMPORT_SCHEME_FORMAT_VERSION {
                BinaryProjectionError::ImportSchemeRequiresV44
            } else if pool.minimum_version() >= HANDLE_TYPE_FORMAT_VERSION {
                BinaryProjectionError::HandleTypeRequiresV43
            } else if pool.minimum_version() >= TUPLE_LAYOUT_FORMAT_VERSION {
                BinaryProjectionError::TupleLayoutRequiresV42
            } else if pool.minimum_version() >= CONTRACT_SURFACE_FORMAT_VERSION {
                BinaryProjectionError::ContractSurfaceRequiresV41
            } else if pool.minimum_version() >= CONTAINER_VTABLE_FORMAT_VERSION {
                BinaryProjectionError::ContainerVtableRequiresV40
            } else {
                BinaryProjectionError::DialectTypeRequiresV39
            });
        }
        Ok(Self {
            module,
            view,
            pool,
            encoded_len: None,
        })
    }

    /// Return the exact projected byte length, counting it only on first use.
    pub fn encoded_len(&mut self) -> usize {
        if let Some(encoded_len) = self.encoded_len {
            return encoded_len;
        }
        let mut counter = CountingSink::default();
        write_module_with_pool(self.module, Some(&self.view), &self.pool, &mut counter);
        self.encoded_len = Some(counter.len);
        counter.len
    }

    /// Visit projected encoding chunks in order. Scalar fields are coalesced
    /// through a fixed-size buffer; chunk boundaries are not a stable part of the
    /// format contract.
    pub fn for_each_chunk(&mut self, mut callback: impl FnMut(&[u8])) {
        let mut sink = CallbackSink(&mut callback);
        stream_module_with_pool(self.module, Some(&self.view), &self.pool, &mut sink);
    }

    /// The projected walk in check mode ([`CheckSink`]): the first refusal
    /// by precedence, or the exact projected length (memoized).
    /// [`Self::try_new`] already refused the source module; this is the
    /// projected image's own statement of the same rule.
    fn check(&mut self) -> Result<usize, BinaryProjectionError> {
        let mut sink = CheckSink::default();
        write_module_with_pool(self.module, Some(&self.view), &self.pool, &mut sink);
        let len = sink.into_result()?;
        self.encoded_len = Some(len);
        Ok(len)
    }

    /// Stream the projected identity image into an arbitrary writer,
    /// coalescing scalar wire fields through a fixed-size buffer, in ONE wire
    /// pass.
    ///
    /// # Errors
    ///
    /// The writer's I/O error, or `InvalidData` carrying the
    /// [`BinaryProjectionError`] when the projected image has none (recorded by
    /// the streaming sink; the bytes already written are not an image and are
    /// discarded by the caller on `Err`).
    pub fn write_to<W: IoWrite + ?Sized>(&mut self, writer: &mut W) -> io::Result<()> {
        let mut sink = IoSink::new(writer);
        stream_module_with_pool(self.module, Some(&self.view), &self.pool, &mut sink);
        sink.finish()
    }

    /// Materialize the projected identity image for compatibility-only consumers.
    ///
    /// # Errors
    ///
    /// [`BinaryProjectionError`] when the projected image has no wire image
    /// (checked by one counting walk before anything is allocated).
    // `&mut self` only to memoize `encoded_len`; the sealed pool is read
    // through `&`. The `to_vec` name is the public byte-consumer API
    // trust/trust-cg call.
    #[allow(clippy::wrong_self_convention)]
    pub fn to_vec(&mut self) -> Result<Vec<u8>, BinaryProjectionError> {
        let len = self.check()?;
        let mut sink = BlobSink::with_capacity(len);
        write_module_with_pool(self.module, Some(&self.view), &self.pool, &mut sink);
        let bytes = sink.finish()?;
        debug_assert_eq!(bytes.len(), len);
        Ok(bytes)
    }

    /// Hash `prefix || projected_encoding` in one projected wire walk.
    ///
    /// The prefix must identify the projection recipe and its version; it must
    /// not reuse a canonical module-identity domain (`trust_ir.module.v2` /
    /// `trust_ir.module.v3`).
    pub fn sha256_prefixed(&mut self, prefix: &[u8]) -> [u8; 32] {
        let mut hasher = Sha256::new();
        hasher.update(prefix);
        update_sha256_with_module_encoding(self.module, Some(&self.view), &self.pool, &mut hasher);
        hasher.finalize().into()
    }
}

const EXECUTABLE_CONTENT_DIGEST_V1_DOMAIN: &str = "trust_ir.module.executable_content.v1";

fn executable_content_binary_plan_v1(module: &Module) -> ProjectedModuleBinaryPlan<'_> {
    let view = ModuleWireView::executable_content_v1(module);
    let pool = collect_strings_with_view(module, Some(&view));
    ProjectedModuleBinaryPlan {
        module,
        view,
        pool,
        encoded_len: None,
    }
}

/// Compute the v1 executable-content identity through the shared projected
/// binary writer and the standard exact-length SHA-256 domain stream. Unlike
/// `Module::stable_digest`, the projected preimage is intentionally not an
/// authoritative serialized module.
pub(crate) fn executable_content_digest_v1(module: &Module) -> ProofDigest {
    let mut plan = executable_content_binary_plan_v1(module);
    let payload_len = u64::try_from(plan.encoded_len())
        .expect("executable-content projection length exceeds canonical u64 framing");
    let mut digest =
        ProofDigest::sha256_domain_stream(EXECUTABLE_CONTENT_DIGEST_V1_DOMAIN, payload_len);
    plan.for_each_chunk(|chunk| {
        digest
            .update(chunk)
            .expect("counted executable-content projection length must match the shared writer");
    });
    digest
        .finish()
        .expect("shared writer must emit the counted executable-content projection length")
}

/// The one message every binary entry point uses to refuse a lexical-scope
/// inlining chain (WS4.19). Shared so the fallible projection error and the
/// infallible writers' panic say the same thing.
fn inlined_scope_chain_unencodable_message(function: u32, scope: usize) -> String {
    format!(
        "function #{function} lexical scope #{scope} carries an inlining chain link \
         (ScopeData.inlined_at); no binary format version carries it yet (roadmap WS4.19 wire \
         part: a member of the next open wire batch), so the binary writer refuses the module \
         rather than dropping the chain; the text, JSON and MessagePack formats carry it"
    )
}

/// The refusal text for the producer-internal `Ty::Error`: the fallible
/// entry points report it as [`BinaryProjectionError::ProducerInternalType`],
/// the infallible writers panic with it.
pub const PRODUCER_INTERNAL_TYPE_UNENCODABLE_MESSAGE: &str =
    "Ty::Error is producer-internal and not encodable; validate_module rejects it";

/// The refusal text for a construct with no wire tag yet.
fn no_wire_tag_message(construct: &str, site: Option<&WireNodeSite>) -> String {
    let at = site.map_or_else(String::new, |site| {
        format!(
            "function #{} bb{} #{}: ",
            site.function, site.block, site.index
        )
    });
    format!(
        "{at}{construct} has no binary wire tag: its wire version is not yet reserved/landed \
         (docs/wire-allocation.md); use the text or serde codec"
    )
}

/// The refusal text for a count past the format's `u32` limit. It keeps the
/// pre-D1a panic text as its prefix.
fn count_exceeds_format_message(what: &str, count: u64) -> String {
    format!(
        "binary value exceeds the format's u32 length limit: {what} holds {count}, and every \
         reader refuses a count past {}",
        u32::MAX
    )
}

/// The refusal text for a module carrying a completeness claim
/// (`Module.completeness`, WS5.3b): the fallible projection reports it as
/// [`BinaryProjectionError::CompletenessClaimUnencodable`], the infallible
/// writers panic with it.
pub const COMPLETENESS_CLAIM_UNENCODABLE_MESSAGE: &str = "the module carries a completeness claim (Module.completeness); no binary format version \
     carries it yet (roadmap WS5.3b wire part: a member of the next open wire batch), so the \
     binary writer refuses the module rather than dropping the claim; the text, JSON and \
     MessagePack formats carry it";

/// The first `(function, scope)` whose `ScopeData.inlined_at` is set, if any.
/// The binary writer has no carrier for it (see
/// [`BinaryProjectionError::InlinedScopeChainUnencodable`]).
///
/// A scope past `u32::MAX` has no index (the exact enumeration
/// `(0..=u32::MAX).zip(..)`), so it is not reported here; its table's count
/// is then past the format's limit, which [`Module::wire_image_refusal`]
/// reports.
pub fn first_inlined_scope_chain(module: &Module) -> Option<(u32, u32)> {
    module.functions.iter().find_map(|func| {
        func.scopes.as_ref().and_then(|scopes| {
            (0..=u32::MAX)
                .zip(scopes)
                .find_map(|(scope, data)| data.inlined_at.is_some().then_some(scope))
                .map(|scope| (func.id.index(), scope))
        })
    })
}

/// Decode ONE LEB128 varint at the start of `bytes` by the codec's own read
/// rule — the rule every length, count and id in a binary module is read
/// with: the shortest spelling only (`0x80 0x00` is refused), at most one
/// payload bit in byte ten, and a truncated varint is refused by the
/// reader's pre-read bound.
/// Returns the value and how many bytes it occupies. Exposed so a test or a
/// fixture that edits bytes reads them by THIS rule instead of re-deriving it.
///
/// # Errors
///
/// The [`BinaryError`] the module reader would report at that position.
pub fn decode_varint(bytes: &[u8]) -> Result<(u64, usize), BinaryError> {
    let mut reader = Reader::new(bytes);
    let value = reader.read_v64()?;
    let used = usize::try_from(reader.cursor.position())
        .map_err(|_| BinaryError::InvalidData("varint length does not fit usize".to_string()))?;
    Ok((value, used))
}

/// Encode `value` as the codec's canonical (shortest) LEB128 varint — the
/// exact bytes the module writer emits for it. The inverse of
/// [`decode_varint`].
pub fn encode_varint(value: u64) -> Vec<u8> {
    let mut bytes = Vec::new();
    write_v64(&mut bytes, value);
    bytes
}

/// Serialize `module` in the compact binary format, at the minimum lossless
/// wire version for its content.
///
/// # Errors
///
/// [`BinaryProjectionError`] when the module has no wire image: a construct
/// the writer's own arm refuses (the producer-internal `Ty::Error`, a carrier
/// ahead of its wire part, a construct ahead of its tag) or a count past the
/// format's `u32`. One counting walk ([`Module::wire_image_refusal`]'s
/// writer, in check mode) runs first, so a refused image is never
/// materialized ("A construct or count with no wire image is refused by the
/// writer's own arm, at every trust-ir entry point",
/// `docs/SPEC_RATIFICATIONS.md`).
pub fn serialize_module(module: &Module) -> Result<Vec<u8>, BinaryProjectionError> {
    ModuleBinaryPlan::new(module).to_vec()
}

/// Deserialize exactly one TrustIr module from the compact binary format.
/// Trailing bytes are rejected rather than silently dropping unknown semantics.
///
/// # What the reader refuses, pinned as bytes
///
/// The must-refuse corpus carries one poisoned blob per reader refusal, so a
/// consumer can show — on these inputs, test-rung evidence and never proof —
/// that it has not wrapped this reader in a lenient fallback:
/// `refuse/blob_ambiguous_lineage_header` (`UnsupportedVersion`, a v26..=v28
/// header), `refuse/blob_bad_magic` (`InvalidMagic`),
/// `refuse/blob_truncated` and `refuse/blob_pool_count_exceeds_input`
/// (`TooLarge`: every read is size-checked against the remaining input
/// first), `refuse/blob_trailing_bytes` (`InvalidData`),
/// `refuse/blob_varint_overflow` (`VintOverflow`),
/// `refuse/blob_string_id_out_of_pool` (`BadStringId`),
/// `refuse/blob_pool_string_not_utf8` (`Utf8Error`),
/// `refuse/blob_feature_tag_below_its_version` (`InvalidTag`: a tag the
/// header's version does not allocate), and
/// `refuse/blob_param_flag_bit_below_its_version` and
/// `refuse/blob_tuple_layout_incoherent` (`InvalidData`). A level-S template
/// is never a module (amendment S): `refuse/template_blob_is_not_a_module`
/// (`InvalidMagic`, the `TRUST_IS` blob), and its two extension tags under the
/// module magic, `refuse/ty_ext_tag_under_module_magic` (`InvalidTag(39)`) and
/// `refuse/constant_ext_tag_under_module_magic` (`InvalidTag(17)`), refused at
/// every version because `NoExt` has no value to read. Two variants have no
/// row, for measured reasons: `Unencodable` is writer-side, and
/// `UnexpectedEof` is UNREACHABLE by construction — `reserve_checked` runs
/// before every read and reports a short input as `TooLarge`, so the
/// `read_exact` that would report EOF never sees one.
///
/// # The wire version is DROPPED here
///
/// The returned [`Module`] carries no record of the header version it was
/// decoded from, deliberately: the wire version is decode PROVENANCE, not
/// module content, so it must not live on the module or enter
/// [`Module::stable_digest`] (see [`WireVersion`]). The consequence is that a
/// caller of this function cannot afterwards check any rule phrased over the
/// producing version — notably [`crate::BodyGate`]'s producer conformance
/// rule. Use [`deserialize_module_with_wire_version`] when that rule matters;
/// it is the same decoder, and this function delegates to it.
pub fn deserialize_module(bytes: &[u8]) -> Result<Module, BinaryError> {
    deserialize_module_with_wire_version(bytes).map(|(module, _wire_version)| module)
}

/// [`deserialize_module`], keeping the declared HEADER VERSION beside the
/// module as a [`WireVersion`].
///
/// The version is the one the blob itself declared, already validated against
/// the accepted set. It is the ONLY place a consumer can learn what version
/// produced the bytes, because the version is not part of [`Module`] (adding
/// a field would change the module's serde shape and put decode provenance
/// into content identity). The module is byte-for-byte the one
/// [`deserialize_module`] returns; only the version is added.
///
/// The one rule this exists for is [`crate::BodyGate`]'s: a v41-or-later
/// producer MUST emit `Ungated` or `Gated` for every function with a body,
/// and a bodied wire tag `0` (`None`) at v41+ is refused — the header is
/// the writer's declared version, and the writer keeps pre-v41 content at a
/// pre-v41 version. Pair this with
/// `trust_ir_build::validate_module_as_decoded` to enforce it; the plain
/// entry point cannot, and says so.
///
/// The example below is compiled and run only with the `binary` feature —
/// the one configuration in which the paths it names are public (without
/// the feature the module is compiled privately for `Module::stable_digest`
/// and a doctest naming `trust_ir::binary::` cannot resolve). The same
/// behaviour is pinned feature-free by the
/// `decode_keeps_the_declared_header_version_beside_the_module` unit test.
#[cfg_attr(
    feature = "binary",
    doc = r#"
```
use trust_ir::Module;
let module = Module::new("m");
let bytes = trust_ir::binary::serialize_module(&module).unwrap();
let (decoded, wire_version) =
    trust_ir::binary::deserialize_module_with_wire_version(&bytes).unwrap();
assert_eq!(decoded.name, "m");
// The plain entry point decodes the same module and drops the version.
assert_eq!(trust_ir::binary::deserialize_module(&bytes).unwrap(), decoded);
// A legacy-content module is written at the base version, below v41.
assert_eq!(wire_version.get(), trust_ir::binary::BASE_FORMAT_VERSION);
assert!(!wire_version.claims_contract_surface());
```
"#
)]
pub fn deserialize_module_with_wire_version(
    bytes: &[u8],
) -> Result<(Module, WireVersion), BinaryError> {
    let mut r = Reader::new(bytes);

    // Header
    let magic = r.read_array::<{ MAGIC.len() }>()?;
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
    if AMBIGUOUS_LINEAGE_VERSIONS.contains(&version) {
        return Err(BinaryError::UnsupportedVersion);
    }
    r.version = version;

    if version >= 4 {
        let pool_size = r.read_checked_len()?;
        let mut strings = Vec::with_capacity(pool_size);
        for _ in 0..pool_size {
            strings.push(r.read_raw_str()?);
        }
        r.pool = Some(strings);
    }

    let module: Module = read_module_sections(&mut r, version)?;

    // One layout table checks both declared-layout sections (v42 tuples, v58
    // closures), each row laid out once.
    let layouts = module.layout_table();
    layouts
        .validate_tuple_layouts()
        .map_err(|error| BinaryError::InvalidData(error.to_string()))?;
    layouts
        .validate_closure_layouts()
        .map_err(|error| BinaryError::InvalidData(error.to_string()))?;

    if let Err(errors) = module.validate_vector_select_contracts() {
        return Err(BinaryError::InvalidData(format!("{}", errors[0])));
    }

    // `version` is the header word checked above against the accepted set —
    // this is the only place a `WireVersion` is minted.
    Ok((module, WireVersion(version)))
}

// ---------------------------------------------------------------------------
// Templates (amendment S, `docs/SPEC_RATIFICATIONS.md` §22)
// ---------------------------------------------------------------------------

/// The strings and minimum version of a template blob: the header's, then the
/// module's, never below [`TEMPLATE_FORMAT_VERSION`].
fn collect_template_strings(template: &crate::template::Template) -> SealedStringPool {
    use crate::template::{HoleKind, TemplateArg, TemplateParam, TypeContract};
    let mut pool = StringPoolBuilder::new();
    pool.raise_to(TEMPLATE_FORMAT_VERSION);
    let header = &template.header;
    pool.intern(&header.identity);
    for param in &header.params {
        if let TemplateParam::Const { ty } = param {
            collect_type_strings(ty, &mut pool);
        }
    }
    for hole in &header.holes {
        pool.intern(&hole.key.namespace);
        match &hole.kind {
            HoleKind::Type { contract } => match contract {
                TypeContract::Opaque => {}
                TypeContract::Struct { fields } => {
                    for ty in fields {
                        collect_type_strings(ty, &mut pool);
                    }
                }
                TypeContract::Enum { variants, .. } => {
                    for ty in variants.iter().flatten() {
                        collect_type_strings(ty, &mut pool);
                    }
                }
            },
            HoleKind::Const { ty } => collect_type_strings(ty, &mut pool),
            HoleKind::Callee { .. } | HoleKind::Global { .. } => {}
        }
        for arg in &hole.args {
            match arg {
                TemplateArg::Type(ty) => collect_type_strings(ty, &mut pool),
                TemplateArg::Const { value, ty } => {
                    collect_constant_strings(value, &mut pool);
                    collect_type_strings(ty, &mut pool);
                }
                TemplateArg::Host(_) => {}
            }
        }
    }
    collect_strings_into(&template.module, None, pool)
}

fn write_template_param(
    buf: &mut impl BinarySink,
    pool: &SealedStringPool,
    param: &crate::template::TemplateParam,
) {
    use crate::template::TemplateParam;
    match param {
        TemplateParam::Type => write_u8(buf, 0),
        TemplateParam::Const { ty } => {
            write_u8(buf, 1);
            write_ty(buf, pool, ty);
        }
        TemplateParam::Host => write_u8(buf, 2),
    }
}

fn write_type_contract(
    buf: &mut impl BinarySink,
    pool: &SealedStringPool,
    contract: &crate::template::TypeContract,
) {
    use crate::template::TypeContract;
    match contract {
        TypeContract::Opaque => write_u8(buf, 0),
        TypeContract::Struct { fields } => {
            write_u8(buf, 1);
            write_count(buf, "TypeContract::Struct fields", fields.len());
            for ty in fields {
                write_ty(buf, pool, ty);
            }
        }
        TypeContract::Enum {
            variants,
            discriminants,
            repr,
        } => {
            write_u8(buf, 2);
            write_count(buf, "TypeContract::Enum variants", variants.len());
            for fields in variants {
                write_count(buf, "TypeContract::Enum variant fields", fields.len());
                for ty in fields {
                    write_ty(buf, pool, ty);
                }
            }
            write_count(buf, "TypeContract::Enum discriminants", discriminants.len());
            for discriminant in discriminants {
                match discriminant {
                    None => write_u8(buf, 0),
                    Some(value) => {
                        write_u8(buf, 1);
                        write_i128(buf, *value);
                    }
                }
            }
            match repr {
                None => write_u8(buf, 0),
                Some(repr) => write_u8(buf, enum_tag_repr_byte(*repr)),
            }
        }
    }
}

fn write_hole_kind(
    buf: &mut impl BinarySink,
    pool: &SealedStringPool,
    kind: &crate::template::HoleKind,
) {
    use crate::template::HoleKind;
    match kind {
        HoleKind::Type { contract } => {
            write_u8(buf, 0);
            write_type_contract(buf, pool, contract);
        }
        HoleKind::Const { ty } => {
            write_u8(buf, 1);
            write_ty(buf, pool, ty);
        }
        HoleKind::Callee { decl } => {
            write_u8(buf, 2);
            write_func_id(buf, *decl);
        }
        HoleKind::Global { decl } => {
            write_u8(buf, 3);
            write_v32(buf, decl.index());
        }
    }
}

fn write_template_arg(
    buf: &mut impl BinarySink,
    pool: &SealedStringPool,
    arg: &crate::template::TemplateArg,
) {
    use crate::template::TemplateArg;
    match arg {
        TemplateArg::Type(ty) => {
            write_u8(buf, 0);
            write_ty(buf, pool, ty);
        }
        TemplateArg::Const { value, ty } => {
            write_u8(buf, 1);
            write_constant(buf, pool, value);
            write_ty(buf, pool, ty);
        }
        TemplateArg::Host(param) => {
            write_u8(buf, 2);
            write_v32(buf, param.index());
        }
    }
}

fn write_template_header(
    buf: &mut impl BinarySink,
    pool: &SealedStringPool,
    header: &crate::template::TemplateHeader,
) {
    write_str(buf, pool, &header.identity);
    write_count(buf, "TemplateHeader.params", header.params.len());
    for param in &header.params {
        write_template_param(buf, pool, param);
    }
    write_count(buf, "TemplateHeader.holes", header.holes.len());
    for hole in &header.holes {
        write_hole_kind(buf, pool, &hole.kind);
        write_str(buf, pool, &hole.key.namespace);
        write_bytes(buf, &hole.key.bytes);
        write_count(buf, "HoleDef.args", hole.args.len());
        for arg in &hole.args {
            write_template_arg(buf, pool, arg);
        }
    }
}

fn read_template_header(
    r: &mut Reader<'_>,
) -> Result<crate::template::TemplateHeader, BinaryError> {
    use crate::template::{HoleDef, HoleKind, HostKey, TemplateArg, TemplateParam, TypeContract};
    let identity = r.read_str()?;
    let param_count = r.read_checked_len()?;
    let mut params = Vec::with_capacity(param_count);
    for _ in 0..param_count {
        params.push(match r.read_u8()? {
            0 => TemplateParam::Type,
            1 => TemplateParam::Const { ty: read_ty(r)? },
            2 => TemplateParam::Host,
            t => return Err(BinaryError::InvalidTag(t)),
        });
    }
    let hole_count = r.read_checked_len()?;
    let mut holes = Vec::with_capacity(hole_count);
    for _ in 0..hole_count {
        let kind = match r.read_u8()? {
            0 => HoleKind::Type {
                contract: match r.read_u8()? {
                    0 => TypeContract::Opaque,
                    1 => {
                        let n = r.read_checked_len()?;
                        let mut fields = Vec::with_capacity(n);
                        for _ in 0..n {
                            fields.push(read_ty(r)?);
                        }
                        TypeContract::Struct { fields }
                    }
                    2 => {
                        let nv = r.read_checked_len()?;
                        let mut variants = Vec::with_capacity(nv);
                        for _ in 0..nv {
                            let nf = r.read_checked_len()?;
                            let mut fields = Vec::with_capacity(nf);
                            for _ in 0..nf {
                                fields.push(read_ty(r)?);
                            }
                            variants.push(fields);
                        }
                        let nd = r.read_checked_len()?;
                        let mut discriminants = Vec::with_capacity(nd);
                        for _ in 0..nd {
                            discriminants.push(match r.read_u8()? {
                                0 => None,
                                1 => Some(r.read_i128()?),
                                t => return Err(BinaryError::InvalidTag(t)),
                            });
                        }
                        let repr = match r.read_u8()? {
                            0 => None,
                            byte => Some(enum_tag_repr_from_byte(byte, r.version)?),
                        };
                        TypeContract::Enum {
                            variants,
                            discriminants,
                            repr,
                        }
                    }
                    t => return Err(BinaryError::InvalidTag(t)),
                },
            },
            1 => HoleKind::Const { ty: read_ty(r)? },
            2 => HoleKind::Callee {
                decl: r.read_func_id()?,
            },
            3 => HoleKind::Global {
                decl: GlobalId::new(r.read_v32()?),
            },
            t => return Err(BinaryError::InvalidTag(t)),
        };
        let namespace = r.read_str()?;
        let bytes = r.read_bytes()?;
        let arg_count = r.read_checked_len()?;
        let mut args = Vec::with_capacity(arg_count);
        for _ in 0..arg_count {
            args.push(match r.read_u8()? {
                0 => TemplateArg::Type(read_ty(r)?),
                1 => TemplateArg::Const {
                    value: read_constant(r)?,
                    ty: read_ty(r)?,
                },
                2 => TemplateArg::Host(crate::value::ParamId::new(r.read_v32()?)),
                t => return Err(BinaryError::InvalidTag(t)),
            });
        }
        holes.push(HoleDef {
            kind,
            key: HostKey { namespace, bytes },
            args,
        });
    }
    Ok(crate::template::TemplateHeader {
        identity,
        params,
        holes,
    })
}

/// Encode a level-S template as a `TRUST_IS` blob (amendment S, §2): the
/// magic, its version (`max(TEMPLATE_FORMAT_VERSION, the content's minimum
/// lossless version)`), the string pool, the header, then the module sections
/// written by the level-R writers at `X = TemplateRef`. Deterministic.
///
/// A template that fails a structural rule (T1–T5, T7–T9) has no wire
/// identity and is refused with that rule's error; T6 is
/// `trust_ir_build::template::validate_template`'s. A template the writer
/// itself refuses (a producer-internal `Ty::Error`, a lexical-scope inlining
/// chain link, a count past the format's `u32`: the writer's own arms, run
/// first over the check sink exactly as [`Module::wire_image_refusal`] runs
/// them over a module) is refused as `TemplateUnsupported`, never a panic.
pub fn serialize_template(
    template: &crate::template::Template,
) -> Result<Vec<u8>, crate::template::TemplateError> {
    template.check_structure()?;
    let pool = collect_template_strings(template);
    let mut check = CheckSink::default();
    write_template_with_pool(template, &pool, &mut check);
    if let Some(refusal) = check.first.into_iter().flatten().next() {
        return Err(crate::template::TemplateError::TemplateUnsupported {
            what: format!("a construct with no wire image ({refusal})"),
        });
    }
    let mut buf = Vec::new();
    write_template_with_pool(template, &pool, &mut buf);
    Ok(buf)
}

/// The template blob, after the structural rules: the one writer
/// [`serialize_template`] runs over the check sink and then over the blob.
fn write_template_with_pool(
    template: &crate::template::Template,
    pool: &SealedStringPool,
    mut buf: &mut impl BinarySink,
) {
    buf.extend_from_slice(TEMPLATE_MAGIC);
    write_u32(&mut buf, pool.minimum_version());
    write_count(&mut buf, "string table", pool.strings().len());
    for s in pool.strings() {
        write_raw_str(&mut buf, s);
    }
    write_template_header(&mut buf, pool, &template.header);
    write_module_sections(&template.module, None, pool, buf);
}

/// Decode a `TRUST_IS` template blob. A module blob is `NotATemplate`; a
/// header below [`TEMPLATE_FORMAT_VERSION`] or above [`VERSION`] is refused;
/// trailing bytes are refused; a decoded template failing a structural rule is
/// refused with that rule's error.
pub fn deserialize_template(
    bytes: &[u8],
) -> Result<crate::template::Template, crate::template::TemplateError> {
    use crate::template::TemplateError;
    let binary = |error: BinaryError| TemplateError::Binary(format!("{error:?}"));
    let mut r = Reader::new(bytes);
    let magic = r.read_array::<{ TEMPLATE_MAGIC.len() }>().map_err(binary)?;
    if magic != TEMPLATE_MAGIC[..] {
        return Err(TemplateError::NotATemplate);
    }
    let version = r.read_u32().map_err(binary)?;
    if !(TEMPLATE_FORMAT_VERSION..=VERSION).contains(&version) {
        return Err(binary(BinaryError::UnsupportedVersion));
    }
    r.version = version;
    let pool_size = r.read_checked_len().map_err(binary)?;
    let mut strings = Vec::with_capacity(pool_size);
    for _ in 0..pool_size {
        strings.push(r.read_raw_str().map_err(binary)?);
    }
    r.pool = Some(strings);
    let header = read_template_header(&mut r).map_err(binary)?;
    let module = read_module_sections::<TemplateRef>(&mut r, version).map_err(binary)?;
    let template = crate::template::Template { header, module };
    template.check_structure()?;
    Ok(template)
}

/// A template's identity: SHA-256 under `trust_ir.template.v1` of its blob
/// (amendment S, S12). A structurally invalid template has none.
pub(crate) fn template_digest(
    template: &crate::template::Template,
) -> Result<ProofDigest, crate::template::TemplateError> {
    let bytes = serialize_template(template)?;
    Ok(ProofDigest::sha256_domain(
        crate::template::TEMPLATE_DIGEST_DOMAIN,
        &bytes,
    ))
}

/// The module section sequence after the header and the string pool, at
/// either level: a module blob's body (`X = NoExt`) and a template blob's
/// (`X = TemplateRef`, amendment S) are the same sections written by the same
/// writers. Trailing bytes are refused here, for both.
fn read_module_sections<X: WireExt>(
    r: &mut Reader<'_>,
    version: u32,
) -> Result<ModuleG<X>, BinaryError> {
    // Module name
    let name = r.read_str()?;

    // Func types
    let ft_count = r.read_checked_len()?;
    let mut func_types = Vec::with_capacity(ft_count);
    for _ in 0..ft_count {
        func_types.push(read_func_ty(r)?);
    }

    // Structs
    let struct_count = r.read_checked_len()?;
    let mut structs = Vec::with_capacity(struct_count);
    for _ in 0..struct_count {
        structs.push(read_struct_def(r)?);
    }

    // Enums
    let enum_count = r.read_checked_len()?;
    let mut enums = Vec::with_capacity(enum_count);
    for _ in 0..enum_count {
        enums.push(read_enum_def(r)?);
    }

    // Records
    let record_count = r.read_checked_len()?;
    let mut records = Vec::with_capacity(record_count);
    for _ in 0..record_count {
        records.push(read_record_def(r)?);
    }

    // Closure types
    let closure_ty_count = r.read_checked_len()?;
    let mut closure_types = Vec::with_capacity(closure_ty_count);
    for _ in 0..closure_ty_count {
        closure_types.push(read_closure_ty(r)?);
    }

    // Globals
    let global_count = r.read_checked_len()?;
    let mut globals = Vec::with_capacity(global_count);
    for _ in 0..global_count {
        globals.push(read_global(r, version)?);
    }

    // Types
    let type_count = r.read_checked_len()?;
    let mut types = Vec::with_capacity(type_count);
    for _ in 0..type_count {
        types.push(read_ty(r)?);
    }

    // Functions
    let func_count = r.read_checked_len()?;
    let mut functions = Vec::with_capacity(func_count);
    for _ in 0..func_count {
        functions.push(read_function(r, version)?);
    }

    // Proof obligations
    let po_count = r.read_checked_len()?;
    let mut proof_obligations = Vec::with_capacity(po_count);
    for _ in 0..po_count {
        proof_obligations.push(read_proof_obligation(r, version)?);
    }

    // Proof certificates
    let cert_count = r.read_checked_len()?;
    let mut proof_certificates = Vec::with_capacity(cert_count);
    for _ in 0..cert_count {
        proof_certificates.push(read_proof_certificate(r)?);
    }

    // Target info
    let target_info = match r.read_u8()? {
        0 => None,
        1 => {
            let triple = r.read_str()?;
            let pointer_size = r.read_v32()?;
            let endianness = read_endianness(r)?;
            // ABI pinning (VERSION >= 20); pre-v20 records stop at endianness.
            let (abi, struct_passing) = if version >= 20 {
                let abi = read_opt_str(r)?;
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
            spec_modules.push(read_spec_module(r)?);
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
            universes.push(read_universe(r)?);
        }
        let p_count = r.read_checked_len()?;
        let mut predicates = Vec::with_capacity(p_count);
        for _ in 0..p_count {
            predicates.push(read_pred(r)?);
        }
        (universes, predicates)
    } else {
        (Vec::new(), Vec::new())
    };

    // v41 trailing sections, read BEFORE the trailing-byte refusal below.
    let (global_asm, imports) = if version >= CONTRACT_SURFACE_FORMAT_VERSION {
        let n = r.read_checked_len()?;
        let mut global_asm = Vec::with_capacity(n);
        for _ in 0..n {
            global_asm.push(r.read_str()?);
        }
        let n = r.read_checked_len()?;
        let mut imports = Vec::with_capacity(n);
        for _ in 0..n {
            imports.push(read_module_import(r)?);
        }
        (global_asm, imports)
    } else {
        (Vec::new(), Vec::new())
    };

    let mut tuple_layouts = Vec::new();
    if version >= TUPLE_LAYOUT_FORMAT_VERSION {
        let count = r.read_checked_len()?;
        for _ in 0..count {
            let tuple_type = TyId::new(r.read_v32()?);
            let size = r.read_v64()?;
            let align = r.read_v64()?;
            let fields = r.read_checked_len()?;
            let mut field_offsets = Vec::with_capacity(fields);
            for _ in 0..fields {
                field_offsets.push(r.read_v64()?);
            }
            tuple_layouts.push(crate::TupleLayoutDescriptor {
                tuple_type,
                size,
                align,
                field_offsets,
            });
        }
    }

    // v55 (amendment D): the drop-glue table. Its ONE order is checked here,
    // before any validator runs (`refuse/blob_drop_glue_not_canonical`):
    // glue ids strictly ascending, no key twice. Whether a glue id names a
    // function is the validator's question (ids are sparse keys).
    let mut drop_glue = Vec::new();
    if version >= DROP_GLUE_FORMAT_VERSION {
        let count = r.read_checked_len()?;
        let mut keys: HashSet<Ty> = HashSet::with_capacity(count);
        let mut previous: Option<u32> = None;
        for _ in 0..count {
            let glue = r.read_func_id()?;
            let ty = read_ty(r)?;
            if previous.is_some_and(|previous| glue.index() <= previous) {
                return Err(BinaryError::InvalidData(format!(
                    "drop-glue table out of canonical order: glue @func.{} does not follow \
                     @func.{} (rows are strictly ascending by glue)",
                    glue.index(),
                    previous.unwrap_or_default()
                )));
            }
            if !keys.insert(ty.clone()) {
                return Err(BinaryError::InvalidData(format!(
                    "drop-glue table states two rows for type {ty} (one row per type)"
                )));
            }
            previous = Some(glue.index());
            drop_glue.push(crate::DropGlueEntry { glue, ty });
        }
    }

    // v58 declared closure layouts, after the v55 drop-glue table.
    let mut closure_layouts = Vec::new();
    if version >= NOMINAL_IDENTITY_FORMAT_VERSION {
        let count = r.read_checked_len()?;
        for _ in 0..count {
            let closure = ClosureTyId::new(r.read_v32()?);
            let size = r.read_v64()?;
            let align = r.read_v64()?;
            let captures = r.read_checked_len()?;
            let mut capture_offsets = Vec::with_capacity(captures);
            for _ in 0..captures {
                capture_offsets.push(r.read_v64()?);
            }
            let origin = if version >= CLOSURE_ORIGIN_FORMAT_VERSION {
                read_type_origin(r)?
            } else {
                None
            };
            closure_layouts.push(crate::ClosureLayoutDescriptor {
                origin,
                closure,
                size,
                align,
                capture_offsets,
            });
        }
    }

    // v70: the blob table, after the v58 closure layouts. Its ONE order is
    // checked here, before any validator runs
    // (`refuse/blob_tensor_blob_table_not_canonical`): digests strictly
    // ascending, so each is listed once. Whether a row's bytes hash to its
    // digest is the validator's question (`InvalidBlobTable`).
    let mut blobs: Vec<crate::blob::Blob> = Vec::new();
    if version >= TENSOR_BLOB_FORMAT_VERSION {
        let count = r.read_checked_len()?;
        for _ in 0..count {
            let mut digest = [0u8; 32];
            digest.copy_from_slice(&r.read_exact(32)?);
            let len = r.read_checked_len()?;
            let data = r.read_exact(len)?;
            blobs.push(crate::blob::Blob {
                digest: crate::blob::BlobDigest(digest),
                data,
            });
        }
        if let Some(reason) = crate::blob::blob_table_order_refusal(&blobs) {
            return Err(BinaryError::InvalidData(reason));
        }
    }

    if r.bytes_remaining() != 0 {
        return Err(BinaryError::InvalidData(
            "trailing bytes after canonical module payload".to_string(),
        ));
    }

    Ok(ModuleG {
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
        global_asm,
        imports,
        tuple_layouts,
        // WS5.3b: no binary version carries a completeness claim yet, so a
        // decoded module makes NONE (never `Complete`).
        completeness: None,
        drop_glue,
        closure_layouts,
        blobs,
    })
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

// The wire-allocation census (`wire-allocations.toml` at the repo root): every
// version constant here, every tag of every wire enum this file SPELLS (a
// source scan finds them; a tag a writer computed instead of spelling would
// escape it) and every version-suffixed identity string must have a registry
// row. A child module, so it reads the private writers. DO NOT DROP THIS HOOK
// in a merge: without it the census runs zero tests, which `cargo test` calls
// success. Gate 0 (`wire_alloc.py check`) and gate 10 both refuse its absence.
#[cfg(test)]
mod wire_census;

#[cfg(test)]
mod wire_image_refusal_tests;

#[cfg(test)]
mod tests {
    use super::*;

    /// A sealed string table for a writer test. `seed` is the test's stand-in
    /// for the collection walk: it runs the real `collect_*` where one fits
    /// the sample, or interns the literal strings a hand-forged record
    /// spells. The `write_*` functions take `&SealedStringPool`, so a test
    /// cannot let the writer mint an id the table never received either.
    fn sealed_pool(seed: impl FnOnce(&mut StringPoolBuilder)) -> SealedStringPool {
        let mut builder = StringPoolBuilder::new();
        seed(&mut builder);
        builder.seal()
    }

    /// The same, for a record whose writer only emits a version-gated field
    /// once the collection walk has raised the header.
    fn sealed_pool_at(version: u32, seed: impl FnOnce(&mut StringPoolBuilder)) -> SealedStringPool {
        sealed_pool(|builder| {
            builder.raise_to(version);
            seed(builder);
        })
    }

    /// A legacy-content module — one bodied function, no codegen license, no
    /// v39+ feature — so the writer selects `BASE_FORMAT_VERSION` for it.
    fn legacy_bodied_module() -> Module {
        let mut module = Module::new("wire-version-provenance");
        let signature = module
            .add_func_type(FuncTy {
                params: vec![Ty::I64],
                returns: vec![Ty::I64],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut block = Block::new(BlockId::new(0));
        block.params.push((ValueId::new(0), Ty::I64));
        block.body.push(InstrNode::new(Inst::Return {
            values: vec![ValueId::new(0)],
        }));
        let mut function = Function::new(FuncId::new(0), "identity", signature, BlockId::new(0));
        function.blocks.push(block);
        module
            .try_add_function(function)
            .expect("Module::try_add_function: test fixture");
        module
    }

    /// The header version reaches the caller BESIDE the module and nowhere
    /// else: the module is the plain entry point's module, and the version is
    /// exactly the header word — the one place a `WireVersion` is minted.
    #[test]
    fn decode_keeps_the_declared_header_version_beside_the_module() {
        let module = legacy_bodied_module();
        let bytes = serialize_module(&module).expect("serialize_module: test fixture");
        assert_eq!(&bytes[8..12], &BASE_FORMAT_VERSION.to_le_bytes());
        let (decoded, wire_version) =
            deserialize_module_with_wire_version(&bytes).expect("legacy blob decodes");
        assert_eq!(wire_version.get(), BASE_FORMAT_VERSION);
        assert!(!wire_version.claims_contract_surface());
        assert_eq!(wire_version.to_string(), format!("v{BASE_FORMAT_VERSION}"));
        assert_eq!(decoded, module);
        assert_eq!(
            deserialize_module(&bytes).expect("plain entry point decodes"),
            decoded,
            "the plain entry point is the same decoder minus the version"
        );
        // A refused header mints nothing: the version is validated before it
        // is returned, so every `WireVersion` is one this build accepts.
        let mut relabelled = bytes.clone();
        relabelled[8..12].copy_from_slice(&(VERSION + 1).to_le_bytes());
        assert_eq!(
            deserialize_module_with_wire_version(&relabelled).err(),
            Some(BinaryError::UnsupportedVersion)
        );
    }

    /// The wire version is decode PROVENANCE, not content: the same module
    /// written at the current version decodes to an EQUAL module with an
    /// EQUAL `stable_digest`, and only the `WireVersion` beside it differs.
    /// This is the measurement behind the `WireVersion` doc's claim that the
    /// version must not (and does not) enter module identity.
    #[test]
    fn wire_version_is_not_module_content() {
        let module = legacy_bodied_module();
        let base = serialize_module(&module).expect("serialize_module: test fixture");
        let mut builder = StringPoolBuilder::new();
        builder.raise_to(VERSION);
        let pool = collect_strings_into(&module, None, builder);
        let mut raised = Vec::new();
        write_module_with_pool(&module, None, &pool, &mut raised);
        assert_eq!(&base[8..12], &BASE_FORMAT_VERSION.to_le_bytes());
        assert_eq!(&raised[8..12], &VERSION.to_le_bytes());
        assert_ne!(base, raised, "the two spellings differ on the wire");

        let (from_base, base_version) =
            deserialize_module_with_wire_version(&base).expect("base blob decodes");
        let (from_raised, raised_version) =
            deserialize_module_with_wire_version(&raised).expect("raised blob decodes");
        assert_eq!(base_version.get(), BASE_FORMAT_VERSION);
        assert_eq!(raised_version.get(), VERSION);
        assert!(!base_version.claims_contract_surface());
        assert!(raised_version.claims_contract_surface());
        assert_eq!(from_base, from_raised, "same content, whatever the header");
        assert_eq!(
            from_base.stable_digest(),
            from_raised.stable_digest(),
            "decode provenance never enters module identity"
        );
        // And the bodied function's tag-0 license survives the v41+ spelling
        // as `None` — which is exactly the state the producer rule is about.
        assert_eq!(from_raised.functions[0].body_gate, None);
    }

    #[derive(Default)]
    struct ChunkSink {
        chunks: Vec<Vec<u8>>,
    }

    impl BinarySink for ChunkSink {
        fn append_bytes(&mut self, bytes: &[u8]) {
            self.chunks.push(bytes.to_vec());
        }

        fn refuse(&mut self, refusal: WireRefusal) {
            refusal.panic_unencodable()
        }

        fn note_over_limit(&mut self, _what: &'static str, _count: u64) {}
    }

    struct Sha256Sink(Sha256);

    impl Default for Sha256Sink {
        fn default() -> Self {
            Self(Sha256::new())
        }
    }

    impl BinarySink for Sha256Sink {
        fn append_bytes(&mut self, bytes: &[u8]) {
            self.0.update(bytes);
        }

        fn refuse(&mut self, refusal: WireRefusal) {
            refusal.panic_unencodable()
        }

        fn note_over_limit(&mut self, _what: &'static str, _count: u64) {}
    }

    #[derive(Default)]
    struct AppendCountSink {
        calls: usize,
        bytes: usize,
    }

    impl BinarySink for AppendCountSink {
        fn append_bytes(&mut self, bytes: &[u8]) {
            self.calls += 1;
            self.bytes += bytes.len();
        }

        fn refuse(&mut self, refusal: WireRefusal) {
            refusal.panic_unencodable()
        }

        fn note_over_limit(&mut self, _what: &'static str, _count: u64) {}
    }

    #[derive(Default)]
    struct RecordingWriter {
        calls: usize,
        write_lengths: Vec<usize>,
        bytes: Vec<u8>,
    }

    impl IoWrite for RecordingWriter {
        fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
            self.calls += 1;
            self.write_lengths.push(bytes.len());
            self.bytes.extend_from_slice(bytes);
            Ok(bytes.len())
        }

        fn flush(&mut self) -> io::Result<()> {
            Ok(())
        }
    }

    fn assert_shared_module_writer(module: &Module) {
        let expected = serialize_module(module).expect("serialize_module: test fixture");
        let expected_domain_digest = ProofDigest::sha256_domain("trust_ir.module.v2", &expected);

        let mut counted = CountingSink::default();
        write_module(module, &mut counted);
        assert_eq!(counted.len, expected.len());

        let mut chunked = ChunkSink::default();
        write_module(module, &mut chunked);
        assert_eq!(chunked.chunks.concat(), expected);

        let mut hashed = Sha256Sink::default();
        write_module(module, &mut hashed);
        assert_eq!(hashed.0.finalize()[..], Sha256::digest(&expected)[..]);

        let mut plan = ModuleBinaryPlan::new(module);
        assert!(
            expected.len() < BINARY_STREAM_BUFFER_BYTES,
            "actual-plan batching fixture must fit one stream buffer"
        );
        let mut callback_calls = 0;
        let mut callback_bytes = Vec::new();
        plan.for_each_chunk(|chunk| {
            callback_calls += 1;
            callback_bytes.extend_from_slice(chunk);
        });
        assert_eq!(callback_bytes, expected);
        assert_eq!(callback_calls, 1, "scalar callback writes must coalesce");

        let mut writer = RecordingWriter::default();
        plan.write_to(&mut writer)
            .expect("recording writer cannot fail");
        assert_eq!(writer.bytes, expected);
        assert_eq!(writer.calls, 1, "scalar writer calls must coalesce");
        assert_eq!(
            plan.encoded_len, None,
            "callback and writer streaming must not add an encoded-length prepass"
        );
        assert_eq!(plan.encoded_len(), expected.len());
        assert_eq!(plan.to_vec().expect("to_vec: test fixture"), expected);

        let prefix = b"binary-plan-prefix.v1\0";
        let mut expected_prefixed = Sha256::new();
        expected_prefixed.update(prefix);
        expected_prefixed.update(&expected);
        assert_eq!(
            plan.sha256_prefixed(prefix),
            <[u8; 32]>::from(expected_prefixed.finalize())
        );
        assert_eq!(
            plan.sha256_domain("trust_ir.module.v2"),
            expected_domain_digest
        );
        assert_eq!(
            module.stable_digest_under(IdentityScheme::V2),
            expected_domain_digest
        );
        // V3 over a module with an EMPTY file table is the same image under
        // the v3 domain (there is no path string to project).
        if module.files.is_empty() {
            assert_eq!(
                module.stable_digest(),
                ProofDigest::sha256_domain("trust_ir.module.v3", &expected)
            );
        }
    }

    #[test]
    fn module_wire_walk_is_identical_for_vec_count_chunk_and_hash_sinks() {
        assert_shared_module_writer(&Module::new("empty-streaming-fixture"));
        assert_shared_module_writer(&vector_instruction_module("full-streaming-fixture"));
    }

    /// A module carrying every proof-side sidecar plus source provenance and
    /// an on-IR `ProofRef`, so a projection test can see what is stripped and
    /// what is retained. Carries no codegen license and no v41 ABI residue.
    fn executable_domain_canary() -> Module {
        let mut module = Module::new("executable-domain-canary");
        let signature = module
            .add_func_type(FuncTy {
                params: vec![Ty::I64],
                returns: vec![Ty::I64],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let proof_id = ProofId::new(7);
        let mut block = Block::new(BlockId::new(5));
        block.params.push((ValueId::new(41), Ty::I64));
        block.body.push(
            InstrNode::new(Inst::Return {
                values: vec![ValueId::new(41)],
            })
            .with_proof(ProofAnnotation::ProofRef(proof_id)),
        );
        let mut function = Function::new(FuncId::new(0), "identity", signature, BlockId::new(5));
        function.blocks.push(block);
        function.source_provenance = Some(SourceProvenance::new(
            ProofDigest::sha256([1; 32]),
            ProofDigest::sha256([2; 32]),
            vec![SourceLoopProvenance {
                source_loop_id: 0,
                hir_local_id: 1,
                header: BlockId::new(5),
                bindings: vec![SourceBindingProvenance {
                    name: "argument".into(),
                    hir_local_id: 2,
                    place: SourcePlace::FunctionParameter { index: 0 },
                }],
            }],
        ));
        module.functions.push(function);
        module.proof_obligations.push(ProofObligation::new(
            proof_id,
            ObligationKind::ArithmeticSafety,
            ProofStatus::Pending,
            "proof-only obligation",
        ));
        module.proof_certificates.push(ProofCertificate {
            obligation: proof_id,
            prover: "proof-only prover".into(),
            evidence: ProofEvidence::Trusted("proof-only evidence".into()),
            assurance: None,
        });
        module.obligation_diagnostics.push(
            crate::proof::ObligationDiagnostic::note(proof_id, "proof-only diagnostic")
                .with_detail("proof-only detail"),
        );
        module
    }

    #[test]
    fn executable_content_digest_v1_matches_standard_domain_framing() {
        let module = executable_domain_canary();
        let proof_id = ProofId::new(7);

        let mut plan = executable_content_binary_plan_v1(&module);
        let projected_bytes = plan.to_vec().expect("to_vec: test fixture");
        assert_eq!(
            executable_content_digest_v1(&module),
            ProofDigest::sha256_domain(EXECUTABLE_CONTENT_DIGEST_V1_DOMAIN, &projected_bytes,),
            "the public recipe must use the shared exact-length domain framing",
        );

        let projected = deserialize_module(&projected_bytes).expect("projection is valid v38");
        assert!(projected.proof_obligations.is_empty());
        assert!(projected.proof_certificates.is_empty());
        assert!(projected.obligation_diagnostics.is_empty());
        assert!(projected.functions[0].source_provenance.is_some());
        assert_eq!(
            projected.functions[0].blocks[0].body[0].proofs,
            [ProofAnnotation::ProofRef(proof_id)],
            "on-IR proof references stay in the identity preimage",
        );
    }

    #[test]
    fn executable_content_projection_strips_the_codegen_license() {
        let authority = "trust-verifier";
        let path = "crate::identity";
        let unlicensed = executable_domain_canary();

        // Licensed AND carrying a genuine v41 ABI feature: the image stays a
        // v41 blob (`naked` is identity-bearing) but decodes unlicensed, and
        // neither license string reaches the pool the writer indexes into.
        let mut licensed_naked = executable_domain_canary();
        licensed_naked.functions[0].body_gate = Some(crate::BodyGate::Gated {
            authority: authority.into(),
            evidence: None,
        });
        licensed_naked.functions[0].display_path = Some(path.into());
        licensed_naked.functions[0].attrs.naked = true;
        let mut plan = executable_content_binary_plan_v1(&licensed_naked);
        let projected_bytes = plan.to_vec().expect("to_vec: test fixture");
        assert_eq!(
            executable_content_digest_v1(&licensed_naked),
            ProofDigest::sha256_domain(EXECUTABLE_CONTENT_DIGEST_V1_DOMAIN, &projected_bytes),
            "the stripped projection still uses the shared exact-length domain framing",
        );
        assert_eq!(
            header_version(&projected_bytes),
            CONTRACT_SURFACE_FORMAT_VERSION
        );
        let projected =
            deserialize_module(&projected_bytes).expect("projection is a valid v41 blob");
        assert_eq!(projected.functions[0].body_gate, None);
        assert_eq!(projected.functions[0].display_path, None);
        assert!(projected.functions[0].attrs.naked);
        assert!(
            !plan.pool.strings().iter().any(|s| &**s == authority),
            "the gate authority must not be pooled by the identity projection"
        );
        assert!(
            !plan.pool.strings().iter().any(|s| &**s == path),
            "the display path must not be pooled by the identity projection"
        );

        // License-only: the projection is the exact pre-v41 image of the same
        // module unlicensed, so verify-then-license leaves the identity the
        // license names untouched. The exact structural identity still sees it.
        let mut licensed = executable_domain_canary();
        licensed.functions[0].body_gate = Some(crate::BodyGate::Gated {
            authority: authority.into(),
            evidence: None,
        });
        licensed.functions[0].display_path = Some(path.into());
        let licensed_bytes = executable_content_binary_plan_v1(&licensed)
            .to_vec()
            .expect("to_vec: test fixture");
        assert_eq!(header_version(&licensed_bytes), BASE_FORMAT_VERSION);
        assert_eq!(
            licensed_bytes,
            executable_content_binary_plan_v1(&unlicensed)
                .to_vec()
                .expect("to_vec: test fixture")
        );
        assert_eq!(
            executable_content_digest_v1(&licensed),
            executable_content_digest_v1(&unlicensed)
        );
        assert_ne!(licensed.stable_digest(), unlicensed.stable_digest());
    }

    #[test]
    fn explicit_v38_projections_refuse_a_licensed_module() {
        // The strip is executable-identity-only, never a downgrade path: a
        // faithful projection pinned to v38 must still refuse the license.
        let licenses: [fn(&mut Function); 3] = [
            |f| f.body_gate = Some(crate::BodyGate::Ungated),
            |f| {
                f.body_gate = Some(crate::BodyGate::Gated {
                    authority: "trust-verifier".into(),
                    evidence: None,
                })
            },
            |f| f.display_path = Some("crate::identity".into()),
        ];
        for license in licenses {
            let mut module = executable_domain_canary();
            license(&mut module.functions[0]);
            assert_eq!(
                header_version(&serialize_module(&module).expect("serialize_module: test fixture")),
                CONTRACT_SURFACE_FORMAT_VERSION,
                "the faithful writer selects v41 for a licensed module"
            );
            for body in [ModuleBinaryBody::RawV38, ModuleBinaryBody::CanonicalV38] {
                assert!(matches!(
                    ProjectedModuleBinaryPlan::try_new(
                        &module,
                        ModuleBinaryOptions {
                            body,
                            ..Default::default()
                        }
                    ),
                    Err(BinaryProjectionError::ContractSurfaceRequiresV41)
                ));
            }
        }
    }

    fn assert_scalar_heavy_stream_observation(
        expected: &[u8],
        observed: &[u8],
        chunk_lengths: &[usize],
    ) {
        assert_eq!(observed, expected);
        let ideal_calls = expected.len().div_ceil(BINARY_STREAM_BUFFER_BYTES);
        assert!(
            (ideal_calls..=ideal_calls + 1).contains(&chunk_lengths.len()),
            "scalar stream used {} calls for {} bytes; expected {ideal_calls} or {}",
            chunk_lengths.len(),
            expected.len(),
            ideal_calls + 1,
        );
        assert!(
            chunk_lengths
                .iter()
                .all(|&len| (1..=BINARY_STREAM_BUFFER_BYTES).contains(&len)),
            "scalar-only stream emitted an empty or oversized chunk: {chunk_lengths:?}",
        );
        assert_eq!(chunk_lengths.iter().sum::<usize>(), expected.len());
    }

    fn scalar_heavy_streaming_module() -> Module {
        let mut module = Module::new("scalar-heavy");
        module.types = vec![Ty::I8; BINARY_STREAM_BUFFER_BYTES * 8 + 17];
        module
    }

    #[test]
    fn public_binary_plans_batch_multi_buffer_scalar_images() {
        let module = scalar_heavy_streaming_module();
        let expected = serialize_module(&module).expect("serialize_module: test fixture");
        assert!(expected.len() > BINARY_STREAM_BUFFER_BYTES * 8);

        let mut raw = ModuleBinaryPlan::new(&module);
        let mut raw_callback_lengths = Vec::new();
        let mut raw_callback_bytes = Vec::new();
        raw.for_each_chunk(|chunk| {
            raw_callback_lengths.push(chunk.len());
            raw_callback_bytes.extend_from_slice(chunk);
        });
        assert_scalar_heavy_stream_observation(
            &expected,
            &raw_callback_bytes,
            &raw_callback_lengths,
        );
        let mut raw_writer = RecordingWriter::default();
        raw.write_to(&mut raw_writer)
            .expect("recording writer cannot fail");
        assert_scalar_heavy_stream_observation(
            &expected,
            &raw_writer.bytes,
            &raw_writer.write_lengths,
        );
        assert_eq!(raw_writer.calls, raw_callback_lengths.len());
        assert_eq!(raw_writer.write_lengths, raw_callback_lengths);
        assert_eq!(
            raw.encoded_len, None,
            "raw streaming must remain one wire pass without a length prepass",
        );

        let mut projected_image = module.clone();
        projected_image.name = "projected".into();
        let expected_projected =
            serialize_module(&projected_image).expect("serialize_module: test fixture");
        let mut projected = ProjectedModuleBinaryPlan::try_new(
            &module,
            ModuleBinaryOptions {
                body: ModuleBinaryBody::CanonicalV38,
                symbols: ModuleSymbolProjection::StableIdOrdinalNames {
                    module_name: "projected",
                    function_prefix: "f",
                    global_prefix: "g",
                },
                obligations: ModuleObligationRows::All,
            },
        )
        .expect("canonical projected scalar fixture");
        let mut projected_callback_lengths = Vec::new();
        let mut projected_callback_bytes = Vec::new();
        projected.for_each_chunk(|chunk| {
            projected_callback_lengths.push(chunk.len());
            projected_callback_bytes.extend_from_slice(chunk);
        });
        assert_scalar_heavy_stream_observation(
            &expected_projected,
            &projected_callback_bytes,
            &projected_callback_lengths,
        );
        let mut projected_writer = RecordingWriter::default();
        projected
            .write_to(&mut projected_writer)
            .expect("recording writer cannot fail");
        assert_scalar_heavy_stream_observation(
            &expected_projected,
            &projected_writer.bytes,
            &projected_writer.write_lengths,
        );
        assert_eq!(projected_writer.calls, projected_callback_lengths.len());
        assert_eq!(projected_writer.write_lengths, projected_callback_lengths);
        assert_eq!(
            projected.encoded_len, None,
            "projected streaming must remain one wire pass without a length prepass",
        );
    }

    #[test]
    fn buffered_binary_sink_coalesces_many_scalar_writes_deterministically() {
        const TINY_WRITES: usize = BINARY_STREAM_BUFFER_BYTES * 8 + 17;
        let mut counted = AppendCountSink::default();
        {
            let mut buffered =
                BufferedBinarySink::<_, BINARY_STREAM_BUFFER_BYTES>::new(&mut counted);
            for byte in 0..TINY_WRITES {
                buffered.push(byte as u8);
            }
            buffered.finish();
        }

        assert_eq!(counted.bytes, TINY_WRITES);
        assert_eq!(counted.calls, 9, "eight full buffers plus one tail");
    }

    #[test]
    fn v38_projection_contract_is_locked_to_the_v38_writer() {
        assert_eq!(PROJECTED_MODULE_BINARY_VERSION, 38);
        assert_eq!(PROJECTED_MODULE_BINARY_VERSION, BASE_FORMAT_VERSION);
    }

    struct FailingWriter;

    impl std::io::Write for FailingWriter {
        fn write(&mut self, _bytes: &[u8]) -> io::Result<usize> {
            Err(io::Error::new(io::ErrorKind::BrokenPipe, "injected"))
        }

        fn flush(&mut self) -> io::Result<()> {
            Ok(())
        }
    }

    struct FailOnNthWriter {
        fail_on: usize,
        calls: usize,
        bytes: Vec<u8>,
    }

    impl FailOnNthWriter {
        fn new(fail_on: usize) -> Self {
            Self {
                fail_on,
                calls: 0,
                bytes: Vec::new(),
            }
        }
    }

    impl IoWrite for FailOnNthWriter {
        fn write(&mut self, bytes: &[u8]) -> io::Result<usize> {
            self.calls += 1;
            if self.calls == self.fail_on {
                return Err(io::Error::new(io::ErrorKind::BrokenPipe, "injected nth"));
            }
            self.bytes.extend_from_slice(bytes);
            Ok(bytes.len())
        }

        fn flush(&mut self) -> io::Result<()> {
            Ok(())
        }
    }

    #[test]
    fn binary_plans_report_writer_failure() {
        let module = Module::new("failing-writer-fixture");
        let error = ModuleBinaryPlan::new(&module)
            .write_to(&mut FailingWriter)
            .expect_err("injected writer failure must propagate");
        assert_eq!(error.kind(), io::ErrorKind::BrokenPipe);
        assert_eq!(error.to_string(), "injected");

        let mut projected =
            ProjectedModuleBinaryPlan::try_new(&module, ModuleBinaryOptions::default())
                .expect("raw projection");
        let error = projected
            .write_to(&mut FailingWriter)
            .expect_err("injected projected-writer failure must propagate");
        assert_eq!(error.kind(), io::ErrorKind::BrokenPipe);
        assert_eq!(error.to_string(), "injected");
    }

    #[test]
    fn binary_plans_latch_writer_failure_after_a_successful_batch() {
        let module = scalar_heavy_streaming_module();
        let expected = serialize_module(&module).expect("serialize_module: test fixture");

        let mut writer = FailOnNthWriter::new(2);
        let error = ModuleBinaryPlan::new(&module)
            .write_to(&mut writer)
            .expect_err("second batched write must fail");
        assert_eq!(error.kind(), io::ErrorKind::BrokenPipe);
        assert_eq!(error.to_string(), "injected nth");
        assert_eq!(writer.calls, 2, "no writes may follow the latched error");
        assert_eq!(writer.bytes, expected[..BINARY_STREAM_BUFFER_BYTES]);

        let mut writer = FailOnNthWriter::new(2);
        let mut projected =
            ProjectedModuleBinaryPlan::try_new(&module, ModuleBinaryOptions::default())
                .expect("raw projection");
        let error = projected
            .write_to(&mut writer)
            .expect_err("second projected batched write must fail");
        assert_eq!(error.kind(), io::ErrorKind::BrokenPipe);
        assert_eq!(error.to_string(), "injected nth");
        assert_eq!(writer.calls, 2, "no writes may follow the latched error");
        assert_eq!(writer.bytes, expected[..BINARY_STREAM_BUFFER_BYTES]);
    }

    #[cfg(feature = "fmt")]
    fn projected_binary_fixture() -> Module {
        use crate::dialect::{AttrValue, DialectInst};

        let mut module = Module::new("adapter-local-module");
        let signature = module
            .add_func_type(FuncTy {
                params: vec![Ty::I64],
                returns: vec![Ty::I64],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        module.globals.push(Global {
            name: "adapter_global_a".into(),
            ty: Ty::I64,
            mutable: false,
            initializer: Some(Constant::Int(7)),
            linkage: Linkage::Internal,
            tls: None,
            align: None,
            section: None,
            visibility: crate::Visibility::Default,
            retained: false,
        });
        module.globals.push(Global {
            name: "adapter_global_b".into(),
            ty: Ty::I64,
            mutable: false,
            initializer: Some(Constant::SymbolAddr {
                symbol: "external-symbol".into(),
                addend: -4,
            }),
            linkage: Linkage::External,
            tls: None,
            align: None,
            section: None,
            visibility: crate::Visibility::Default,
            retained: false,
        });

        let mut later = Function::new(FuncId::new(9), "adapter_later", signature, b(5));
        later.attrs.params.push(ParamAttrs::default());
        later.value_names = Some(vec![(v(50), "input".into()), (v(300), "allocation".into())]);

        let mut low_block = Block::new(b(1));
        low_block.params.push((v(50), Ty::I64));
        low_block.body.push(
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: v(50),
                rhs: v(999),
            })
            .with_result(v(70)),
        );
        low_block.body.push(InstrNode::new(Inst::Br {
            target: b(5),
            args: vec![v(70)],
        }));

        let mut high_block = Block::new(b(5));
        high_block.params.push((v(100), Ty::I64));
        high_block.params.push((v(200), Ty::Ptr));
        high_block.body.push(
            InstrNode::new(Inst::Alloca {
                ty: Ty::I64,
                count: Some(v(100)),
                align: Some(8),
            })
            .with_result(v(300)),
        );
        high_block.body.push(
            InstrNode::new(Inst::HeapAlloc {
                ty: Ty::I64,
                count: Some(v(100)),
                align: Some(8),
                origin: AllocOrigin::RustHeap,
            })
            .with_result(v(301)),
        );
        high_block.body.push(
            InstrNode::new(Inst::CmpXchg {
                ty: Ty::I64,
                ptr: v(200),
                expected: v(100),
                desired: v(70),
                success: Ordering::SeqCst,
                failure: Ordering::Acquire,
                weak: false,
            })
            .with_result(v(302)),
        );
        let dialect = DialectInst::new("fixture", "projected")
            .with_operand(v(302))
            .with_result_ty(Ty::I64)
            .with_attr("weight", AttrValue::F64(-0.0));
        high_block
            .body
            .push(InstrNode::new(Inst::DialectOp(Box::new(dialect))).with_result(v(303)));
        high_block.body.push(InstrNode::new(Inst::Return {
            values: vec![v(303)],
        }));
        later.blocks.extend([high_block, low_block]);

        let mut earlier = later.clone();
        earlier.id = FuncId::new(2);
        earlier.name = "adapter_earlier".into();
        module.functions.extend([later, earlier]);
        module
    }

    #[cfg(feature = "fmt")]
    fn legacy_neutral_canonical_bytes(module: &Module) -> Vec<u8> {
        let mut image = module.clone();
        image.name = "neutral-module".into();
        image.functions.sort_by_key(|function| function.id.index());
        for function in &mut image.functions {
            function.name = format!("neutral-function-{}", function.id.index());
        }
        for (index, global) in image.globals.iter_mut().enumerate() {
            global.name = format!("neutral-global-{index}");
        }
        serialize_module(&crate::format::canonicalize(&image))
            .expect("serialize_module: test fixture")
    }

    #[cfg(feature = "fmt")]
    fn neutral_canonical_options<'a>(
        obligations: ModuleObligationRows<'a>,
    ) -> ModuleBinaryOptions<'a> {
        ModuleBinaryOptions {
            body: ModuleBinaryBody::CanonicalV38,
            symbols: ModuleSymbolProjection::StableIdOrdinalNames {
                module_name: "neutral-module",
                function_prefix: "neutral-function-",
                global_prefix: "neutral-global-",
            },
            obligations,
        }
    }

    #[cfg(feature = "fmt")]
    fn assert_canonical_projection_path(module: &Module, expect_identity_fast_path: bool) {
        let expected = serialize_module(&crate::format::canonicalize(module))
            .expect("serialize_module: test fixture");
        let mut projected = ProjectedModuleBinaryPlan::try_new(
            module,
            ModuleBinaryOptions {
                body: ModuleBinaryBody::CanonicalV38,
                ..ModuleBinaryOptions::default()
            },
        )
        .expect("canonical projection");
        let functions = projected
            .view
            .canonical_functions
            .as_ref()
            .expect("CanonicalV38 has per-function projection choices");
        assert_eq!(functions.len(), module.functions.len());
        assert_eq!(
            functions.iter().all(Option::is_none),
            expect_identity_fast_path,
            "unexpected canonical function projection path"
        );
        assert_eq!(projected.to_vec().expect("to_vec: test fixture"), expected);
    }

    #[cfg(feature = "fmt")]
    fn large_canonical_projection_fixture(block_count: u32) -> Module {
        let mut module = Module::new("already-canonical-large");
        let signature = module
            .add_func_type(FuncTy {
                params: vec![Ty::I64],
                returns: vec![Ty::I64],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut function = Function::new(FuncId::new(0), "canonical", signature, b(0));
        function.attrs.params.push(ParamAttrs {
            nonnull: true,
            ..ParamAttrs::default()
        });
        function.source_provenance = Some(SourceProvenance::new(d(1), d(2), Vec::new()));

        // Canonical numbering visits every block parameter before any result.
        for index in 0..block_count {
            let mut block = Block::new(b(index));
            block.params.push((v(index), Ty::I64));
            block.body.push(
                InstrNode::new(Inst::Copy {
                    ty: Ty::I64,
                    operand: v(index),
                })
                .with_result(v(block_count + index)),
            );
            block.body.push(InstrNode::new(Inst::Return {
                values: vec![v(block_count + index)],
            }));
            function.blocks.push(block);
        }
        module.functions.push(function);
        module
    }

    #[cfg(feature = "fmt")]
    #[test]
    fn projected_plan_matches_materialized_canonical_and_symbol_projection() {
        let module = projected_binary_fixture();

        let expected_canonical = serialize_module(&crate::format::canonicalize(&module))
            .expect("serialize_module: test fixture");
        let mut canonical = ProjectedModuleBinaryPlan::try_new(
            &module,
            ModuleBinaryOptions {
                body: ModuleBinaryBody::CanonicalV38,
                ..ModuleBinaryOptions::default()
            },
        )
        .expect("canonical projection");
        assert_eq!(
            canonical.to_vec().expect("to_vec: test fixture"),
            expected_canonical
        );

        let expected_neutral = legacy_neutral_canonical_bytes(&module);
        let mut neutral = ProjectedModuleBinaryPlan::try_new(
            &module,
            neutral_canonical_options(ModuleObligationRows::All),
        )
        .expect("neutral canonical projection");
        assert!(
            expected_neutral.len() < BINARY_STREAM_BUFFER_BYTES,
            "projected actual-plan batching fixture must fit one stream buffer"
        );
        let mut callback_calls = 0;
        let mut callback_bytes = Vec::new();
        neutral.for_each_chunk(|chunk| {
            callback_calls += 1;
            callback_bytes.extend_from_slice(chunk);
        });
        assert_eq!(callback_bytes, expected_neutral);
        assert_eq!(
            callback_calls, 1,
            "projected scalar callback writes must coalesce"
        );

        let mut writer = RecordingWriter::default();
        neutral
            .write_to(&mut writer)
            .expect("recording writer cannot fail");
        assert_eq!(writer.bytes, expected_neutral);
        assert_eq!(
            writer.calls, 1,
            "projected scalar writer calls must coalesce"
        );
        assert_eq!(
            neutral.sha256_prefixed(b"projection-prefix\0"),
            Sha256::digest([b"projection-prefix\0".as_slice(), &expected_neutral].concat())
                .as_slice()
        );
        assert_eq!(
            neutral.encoded_len, None,
            "prefix hashing must remain a single projected wire pass"
        );
        assert_eq!(neutral.encoded_len(), expected_neutral.len());
        assert_eq!(
            neutral.to_vec().expect("to_vec: test fixture"),
            expected_neutral
        );

        let mut raw = ProjectedModuleBinaryPlan::try_new(&module, ModuleBinaryOptions::default())
            .expect("raw exact projection");
        assert_eq!(
            raw.to_vec().expect("to_vec: test fixture"),
            serialize_module(&module).expect("serialize_module: test fixture")
        );
    }

    #[cfg(feature = "fmt")]
    #[test]
    fn canonical_projection_skips_per_function_maps_for_large_identity_input() {
        let module = large_canonical_projection_fixture(1_024);
        assert_canonical_projection_path(&module, true);
    }

    #[cfg(feature = "fmt")]
    #[test]
    fn canonical_projection_identity_path_matches_legacy_on_malformed_ssa() {
        let mut module = large_canonical_projection_fixture(1);
        let function = &mut module.functions[0];
        function.blocks[0].params.push((v(0), Ty::I64));
        function.blocks[0].body[0].inst = Inst::Copy {
            ty: Ty::I64,
            operand: v(999),
        };

        // Duplicate %0 is already mapped to %0 by the legacy first-definition
        // rule, while undefined %999 is deliberately absent from the map and
        // therefore remains %999. Neither malformed condition needs scratch.
        assert_canonical_projection_path(&module, true);
    }

    #[cfg(feature = "fmt")]
    #[test]
    fn canonical_projection_falls_back_for_each_uncertain_or_changed_axis() {
        let canonical = large_canonical_projection_fixture(2);

        let mut interior_empty_attrs = canonical.clone();
        interior_empty_attrs.functions[0]
            .attrs
            .params
            .insert(0, ParamAttrs::default());
        assert_canonical_projection_path(&interior_empty_attrs, true);

        let mut descending_blocks = canonical.clone();
        descending_blocks.functions[0].blocks.swap(0, 1);
        assert_canonical_projection_path(&descending_blocks, false);

        let mut sparse_definition = canonical.clone();
        sparse_definition.functions[0].blocks[0].params[0].0 = v(42);
        assert_canonical_projection_path(&sparse_definition, false);

        let mut trailing_empty_attrs = canonical.clone();
        trailing_empty_attrs.functions[0]
            .attrs
            .params
            .push(ParamAttrs::default());
        assert_canonical_projection_path(&trailing_empty_attrs, false);

        let mut non_reflexive_provenance_carrier = canonical;
        non_reflexive_provenance_carrier.functions[0]
            .proofs
            .push(ProofAnnotation::BoundedOutput {
                lo: f64::NAN,
                hi: 1.0,
            });
        assert_canonical_projection_path(&non_reflexive_provenance_carrier, false);
    }

    #[cfg(feature = "fmt")]
    fn provenance_projection_fixture() -> Module {
        let mut module = Module::new("provenance");
        let signature = module
            .add_func_type(FuncTy {
                params: vec![Ty::I64],
                returns: vec![Ty::I64],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut function = Function::new(FuncId::new(0), "identity", signature, b(0));
        let mut block = Block::new(b(0));
        block.params.push((v(0), Ty::I64));
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![v(0)] }));
        function.blocks.push(block);
        function.source_provenance = Some(SourceProvenance::new(
            d(1),
            d(2),
            vec![SourceLoopProvenance {
                source_loop_id: 0,
                hir_local_id: 0,
                header: b(0),
                bindings: vec![SourceBindingProvenance {
                    name: "x".into(),
                    hir_local_id: 0,
                    place: SourcePlace::FunctionParameter { index: 0 },
                }],
            }],
        ));
        module.functions.push(function);
        module
    }

    #[cfg(feature = "fmt")]
    fn assert_canonical_projection_parity(module: &Module) -> Module {
        let expected_module = crate::format::canonicalize(module);
        let expected = serialize_module(&expected_module).expect("serialize_module: test fixture");
        let mut plan = ProjectedModuleBinaryPlan::try_new(
            module,
            ModuleBinaryOptions {
                body: ModuleBinaryBody::CanonicalV38,
                ..ModuleBinaryOptions::default()
            },
        )
        .expect("canonical projection");
        assert_eq!(plan.to_vec().expect("to_vec: test fixture"), expected);
        expected_module
    }

    #[cfg(feature = "fmt")]
    #[test]
    fn projected_provenance_matches_legacy_nan_partial_eq_behavior() {
        let plain = provenance_projection_fixture();
        assert!(
            assert_canonical_projection_parity(&plain).functions[0]
                .source_provenance
                .is_some()
        );

        let mut constant_nan = plain.clone();
        constant_nan.functions[0].blocks[0].body.insert(
            0,
            InstrNode::new(Inst::Const {
                ty: Ty::F64,
                value: Constant::Float(f64::NAN),
            })
            .with_result(v(1)),
        );
        assert!(
            assert_canonical_projection_parity(&constant_nan).functions[0]
                .source_provenance
                .is_some()
        );

        let mut bounded_nan = plain.clone();
        bounded_nan.functions[0]
            .proofs
            .push(ProofAnnotation::BoundedOutput {
                lo: f64::NAN,
                hi: 1.0,
            });
        assert!(
            assert_canonical_projection_parity(&bounded_nan).functions[0]
                .source_provenance
                .is_none()
        );

        let mut dialect_nan = plain;
        dialect_nan.functions[0].blocks[0].body.insert(
            0,
            InstrNode::new(Inst::DialectOp(Box::new(
                crate::dialect::DialectInst::new("fixture", "nan")
                    .with_operand(v(0))
                    .with_result_ty(Ty::I64)
                    .with_attr("nan", crate::dialect::AttrValue::F64(f64::NAN)),
            )))
            .with_result(v(1)),
        );
        assert!(
            assert_canonical_projection_parity(&dialect_nan).functions[0]
                .source_provenance
                .is_none()
        );
    }

    #[cfg(feature = "fmt")]
    fn omission_fixture() -> Module {
        let mut module = provenance_projection_fixture();
        module.functions[0].source_provenance = None;
        module.proof_obligations.extend([
            ProofObligation::new(
                ProofId::new(7),
                ObligationKind::TranslationValidation,
                ProofStatus::Pending,
                "unique omitted description",
            ),
            ProofObligation::new(
                ProofId::new(9),
                ObligationKind::PanicFreedom,
                ProofStatus::Pending,
                "retained description",
            ),
        ]);
        module
    }

    #[cfg(feature = "fmt")]
    fn omission_error(module: &Module) -> BinaryProjectionError {
        ProjectedModuleBinaryPlan::try_new(
            module,
            neutral_canonical_options(ModuleObligationRows::OmitIds(&[ProofId::new(7)])),
        )
        .err()
        .expect("unsafe omission must fail")
    }

    #[cfg(feature = "fmt")]
    #[test]
    fn obligation_omission_matches_physical_deletion_and_rejects_dangling_authority() {
        use crate::proof::{DiagnosticSeverity, ObligationDiagnostic, ProofContext};

        let module = omission_fixture();
        let mut physically_deleted = module.clone();
        physically_deleted
            .proof_obligations
            .retain(|row| row.id != ProofId::new(7));
        let expected = legacy_neutral_canonical_bytes(&physically_deleted);
        let mut projected = ProjectedModuleBinaryPlan::try_new(
            &module,
            neutral_canonical_options(ModuleObligationRows::OmitIds(&[ProofId::new(7)])),
        )
        .expect("closed pending-row omission");
        assert_eq!(projected.to_vec().expect("to_vec: test fixture"), expected);

        assert_eq!(
            ProjectedModuleBinaryPlan::try_new(
                &module,
                neutral_canonical_options(ModuleObligationRows::OmitIds(&[
                    ProofId::new(7),
                    ProofId::new(7),
                ])),
            )
            .err(),
            Some(BinaryProjectionError::DuplicateOmission(ProofId::new(7)))
        );
        assert_eq!(
            ProjectedModuleBinaryPlan::try_new(
                &module,
                neutral_canonical_options(ModuleObligationRows::OmitIds(&[ProofId::new(42)])),
            )
            .err(),
            Some(BinaryProjectionError::UnknownOmission(ProofId::new(42)))
        );

        let mut ambiguous = module.clone();
        ambiguous
            .proof_obligations
            .push(ambiguous.proof_obligations[0].clone());
        assert_eq!(
            omission_error(&ambiguous),
            BinaryProjectionError::AmbiguousOmission(ProofId::new(7))
        );

        let mut non_pending = module.clone();
        non_pending.proof_obligations[0].status = ProofStatus::Discharged;
        assert_eq!(
            omission_error(&non_pending),
            BinaryProjectionError::NonPendingOmission(ProofId::new(7))
        );

        let mut function_ref = module.clone();
        function_ref.functions[0]
            .proofs
            .push(ProofAnnotation::ProofRef(ProofId::new(7)));
        assert!(matches!(
            omission_error(&function_ref),
            BinaryProjectionError::RetainedReference {
                location: "function proof annotation",
                ..
            }
        ));

        let mut node_ref = module.clone();
        node_ref.functions[0].blocks[0].body[0]
            .proofs
            .push(ProofAnnotation::ProofRef(ProofId::new(7)));
        assert!(matches!(
            omission_error(&node_ref),
            BinaryProjectionError::RetainedReference {
                location: "instruction proof annotation",
                ..
            }
        ));

        let mut context_ref = module.clone();
        context_ref.functions[0].blocks[0].body[0].proof_context = Some(ProofContext {
            assumes: vec![ProofId::new(7)],
            establishes: Vec::new(),
        });
        assert!(matches!(
            omission_error(&context_ref),
            BinaryProjectionError::RetainedReference {
                location: "proof-context assumption",
                ..
            }
        ));

        let mut certificate_ref = module.clone();
        certificate_ref.proof_certificates.push(ProofCertificate {
            obligation: ProofId::new(7),
            prover: "fixture".into(),
            evidence: ProofEvidence::Trusted("fixture".into()),
            assurance: None,
        });
        assert!(matches!(
            omission_error(&certificate_ref),
            BinaryProjectionError::RetainedReference {
                location: "proof certificate",
                ..
            }
        ));

        let mut inherited_ref = module.clone();
        inherited_ref.proof_certificates.push(ProofCertificate {
            obligation: ProofId::new(9),
            prover: "fixture".into(),
            evidence: ProofEvidence::InheritedFromCallee {
                callee: FuncId::new(0),
                obligation: ProofId::new(7),
                external: None,
            },
            assurance: None,
        });
        assert!(matches!(
            omission_error(&inherited_ref),
            BinaryProjectionError::RetainedReference {
                location: "inherited proof evidence",
                ..
            }
        ));

        // v61: a license's evidence cites the omitted row.
        let mut evidence_ref = module.clone();
        evidence_ref.functions[0].body_gate = Some(crate::BodyGate::Gated {
            authority: "fixture".into(),
            evidence: Some(crate::GateEvidence {
                obligation: ProofId::new(7),
                body_digest: crate::proof::ProofDigest::sha256([1; 32]),
            }),
        });
        assert!(matches!(
            omission_error(&evidence_ref),
            BinaryProjectionError::RetainedReference {
                location: "codegen license evidence",
                ..
            }
        ));

        let mut diagnostic_ref = module.clone();
        diagnostic_ref
            .obligation_diagnostics
            .push(ObligationDiagnostic {
                obligation: ProofId::new(7),
                severity: DiagnosticSeverity::Note,
                message: "fixture".into(),
                location: None,
                detail: None,
            });
        assert!(matches!(
            omission_error(&diagnostic_ref),
            BinaryProjectionError::RetainedReference {
                location: "obligation diagnostic",
                ..
            }
        ));

        let mut provenance_ref = module;
        provenance_ref.functions[0].source_provenance = provenance_projection_fixture().functions
            [0]
        .source_provenance
        .clone();
        assert!(matches!(
            omission_error(&provenance_ref),
            BinaryProjectionError::RetainedReference {
                location: "source-provenance carrier",
                ..
            }
        ));
    }

    #[cfg(feature = "fmt")]
    #[test]
    fn obligation_omission_preserves_request_order_error_precedence() {
        let module = omission_fixture();

        assert_eq!(
            ProjectedModuleBinaryPlan::try_new(
                &module,
                neutral_canonical_options(ModuleObligationRows::OmitIds(&[
                    ProofId::new(42),
                    ProofId::new(7),
                    ProofId::new(7),
                ])),
            )
            .err(),
            Some(BinaryProjectionError::UnknownOmission(ProofId::new(42)))
        );

        let mut ambiguous = module.clone();
        ambiguous
            .proof_obligations
            .push(ambiguous.proof_obligations[0].clone());
        assert_eq!(
            ProjectedModuleBinaryPlan::try_new(
                &ambiguous,
                neutral_canonical_options(ModuleObligationRows::OmitIds(&[
                    ProofId::new(7),
                    ProofId::new(7),
                ])),
            )
            .err(),
            Some(BinaryProjectionError::AmbiguousOmission(ProofId::new(7)))
        );

        let mut non_pending = module;
        non_pending.proof_obligations[0].status = ProofStatus::Discharged;
        assert_eq!(
            ProjectedModuleBinaryPlan::try_new(
                &non_pending,
                neutral_canonical_options(ModuleObligationRows::OmitIds(&[
                    ProofId::new(7),
                    ProofId::new(7),
                ])),
            )
            .err(),
            Some(BinaryProjectionError::NonPendingOmission(ProofId::new(7)))
        );
    }

    #[test]
    fn obligation_omission_indexes_large_requested_and_row_sets() {
        const ROWS: u32 = 4_096;
        let mut module = Module::new("large-omission-index");
        module.proof_obligations = (0..ROWS)
            .map(|index| {
                ProofObligation::new(
                    ProofId::new(index),
                    ObligationKind::TranslationValidation,
                    ProofStatus::Pending,
                    format!("obligation {index}"),
                )
            })
            .collect();
        let omitted: Vec<_> = (0..ROWS).step_by(2).map(ProofId::new).collect();

        let retained =
            projected_obligation_rows(&module, ModuleObligationRows::OmitIds(&omitted), None)
                .expect("every requested row is unique, pending, and unreferenced");

        assert_eq!(retained.len(), (ROWS / 2) as usize);
        assert!(
            retained
                .iter()
                .enumerate()
                .all(|(ordinal, &row)| row == ordinal * 2 + 1)
        );
    }

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
            assurance: None,
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
        let bytes = serialize_module(module).expect("serialize_module: test fixture");
        let back = deserialize_module(&bytes).expect("deserialize should succeed");
        assert_eq!(module, &back, "round-trip mismatch");
        back
    }

    /// Walk a deliberately minimal, single-global module blob up to the
    /// `Global.align` presence byte and return its offset. Every table before
    /// the globals must be empty and the global uninitialized and non-TLS, so
    /// the walk reads only fields whose layout is fixed. The header version is
    /// the writer's minimum lossless version, not [`VERSION`]; the walk reads
    /// at that version exactly as [`deserialize_module`] does.
    fn minimal_global_align_tag_offset(bytes: &[u8]) -> usize {
        let mut r = Reader::new(bytes);
        assert_eq!(r.read_array::<{ MAGIC.len() }>().unwrap()[..], MAGIC[..]);
        let version = r.read_u32().unwrap();
        assert!(
            version > *AMBIGUOUS_LINEAGE_VERSIONS.end(),
            "a global align presence byte is written only from v29 on (got v{version})"
        );
        r.version = version;

        let pool_size = r.read_checked_len().unwrap();
        let mut strings = Vec::with_capacity(pool_size);
        for _ in 0..pool_size {
            strings.push(r.read_raw_str().unwrap());
        }
        r.pool = Some(strings);

        let _module_name = r.read_str().unwrap();
        for table in ["func types", "structs", "enums", "records", "closures"] {
            assert_eq!(r.read_checked_len().unwrap(), 0, "non-empty {table}");
        }
        assert_eq!(r.read_checked_len().unwrap(), 1, "expected one global");
        let _name = r.read_str().unwrap();
        let _ty: Ty = read_ty(&mut r).unwrap();
        let _mutable = r.read_bool().unwrap();
        assert_eq!(r.read_u8().unwrap(), 0, "test global must be uninitialized");
        let _linkage = read_linkage(&mut r).unwrap();
        assert_eq!(r.read_u8().unwrap(), 0, "test global must be non-TLS");
        r.cursor.position() as usize
    }

    /// One function whose only body instruction is a compare-exchange of the given strength.
    fn cmpxchg_module(weak: bool) -> Module {
        let mut module = Module::new("cmpxchg_strength");
        let ft = module
            .add_func_type(FuncTy {
                abi: None,
                params: vec![Ty::Ptr, Ty::I8, Ty::I8],
                returns: vec![],
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut func = Function::new(FuncId::new(0), "cas", ft, BlockId::new(0));
        let mut entry = Block::new(BlockId::new(0));
        entry
            .params
            .extend([(v(0), Ty::Ptr), (v(1), Ty::I8), (v(2), Ty::I8)]);
        entry.body.push(
            InstrNode::new(Inst::CmpXchg {
                ty: Ty::I8,
                ptr: v(0),
                expected: v(1),
                desired: v(2),
                success: Ordering::AcqRel,
                failure: Ordering::Acquire,
                weak,
            })
            .with_result(v(3))
            .with_result(v(4)),
        );
        entry
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        func.blocks.push(entry);
        module.functions.push(func);
        module
    }

    /// Crystal lane (D3): a WEAK compare-exchange survives the codec as weak, and raises only
    /// ITS module to `WEAK_CMPXCHG_FORMAT_VERSION`; a strong one keeps tag 13 and the base
    /// version byte for byte.
    #[test]
    fn weak_cmpxchg_round_trips_at_its_version_and_strong_stays_at_the_base_version() {
        let strong = cmpxchg_module(false);
        let strong_bytes = serialize_module(&strong).expect("serialize_module: test fixture");
        assert_eq!(&strong_bytes[8..12], &BASE_FORMAT_VERSION.to_le_bytes());
        round_trip(&strong);

        let weak = cmpxchg_module(true);
        let weak_bytes = serialize_module(&weak).expect("serialize_module: test fixture");
        assert_eq!(
            &weak_bytes[8..12],
            &WEAK_CMPXCHG_FORMAT_VERSION.to_le_bytes()
        );
        let back = round_trip(&weak);
        assert!(matches!(
            back.functions[0].blocks[0].body[0].inst,
            Inst::CmpXchg { weak: true, .. }
        ));
        // The two encodings differ, and ONLY by the instruction tag and the header version:
        // a weak CAS read back as strong would delete its spurious-failure executions.
        assert_ne!(strong_bytes, weak_bytes);
    }

    /// Crystal lane (D3): tag 58 is read-gated. A blob that CLAIMS any older readable version
    /// and carries a weak compare-exchange is malformed and refused -- never silently read as
    /// strong. The explicit v38 projections refuse it by name.
    #[test]
    fn weak_cmpxchg_tag_is_refused_below_its_version() {
        let bytes =
            serialize_module(&cmpxchg_module(true)).expect("serialize_module: test fixture");
        for older in [WEAK_CMPXCHG_FORMAT_VERSION - 1, BASE_FORMAT_VERSION] {
            let mut forged = bytes.clone();
            forged[8..12].copy_from_slice(&older.to_le_bytes());
            assert_eq!(
                deserialize_module(&forged),
                Err(BinaryError::InvalidTag(58)),
                "a v{older}-labelled blob carrying instruction tag 58 must be refused"
            );
        }
        for body in [ModuleBinaryBody::RawV38, ModuleBinaryBody::CanonicalV38] {
            let options = ModuleBinaryOptions {
                body,
                ..Default::default()
            };
            assert_eq!(
                ProjectedModuleBinaryPlan::try_new(&cmpxchg_module(true), options).err(),
                Some(BinaryProjectionError::WeakCmpXchgRequiresV48)
            );
            // The STRONG instruction projects at v38 exactly as it always did.
            assert!(ProjectedModuleBinaryPlan::try_new(&cmpxchg_module(false), options).is_ok());
        }
    }

    /// Every `AssertKind` but `Unspecified`, operands over the block params.
    fn every_assert_kind() -> Vec<AssertKind> {
        let mut kinds: Vec<AssertKind> = AssertOverflowOp::ALL
            .into_iter()
            .map(AssertKind::Overflow)
            .collect();
        kinds.extend([
            AssertKind::DivByZero,
            AssertKind::RemByZero,
            AssertKind::BoundsCheck {
                index: v(1),
                len: v(2),
            },
            AssertKind::MisalignedPtr {
                required: v(2),
                found: v(1),
            },
            AssertKind::NullPtr,
        ]);
        kinds
    }

    /// One function `check(c: bool, a: usize, b: usize)` whose body is one
    /// assert of `c` per kind in `kinds`, in order.
    fn assert_kind_module(kinds: &[AssertKind]) -> Module {
        let mut module = Module::new("assert_kind");
        let ft = module
            .add_func_type(FuncTy {
                abi: None,
                params: vec![Ty::Bool, Ty::Usize, Ty::Usize],
                returns: vec![],
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut func = Function::new(FuncId::new(0), "check", ft, BlockId::new(0));
        let mut entry = Block::new(BlockId::new(0));
        entry
            .params
            .extend([(v(0), Ty::Bool), (v(1), Ty::Usize), (v(2), Ty::Usize)]);
        for kind in kinds {
            entry.body.push(InstrNode::new(Inst::Assert {
                cond: v(0),
                kind: *kind,
                site: None,
            }));
        }
        entry
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        func.blocks.push(entry);
        module.functions.push(func);
        module
    }

    /// Plan item P: EVERY kind survives the binary codec exactly, one module
    /// per kind, and raises its module to `ASSERT_KIND_FORMAT_VERSION`; the
    /// kindless assert keeps tag 29 and the base version byte for byte.
    #[test]
    fn every_assert_kind_round_trips_at_its_version_and_unspecified_stays_at_the_base() {
        let unspecified = assert_kind_module(&[AssertKind::Unspecified]);
        let bytes = serialize_module(&unspecified).expect("serialize_module: test fixture");
        assert_eq!(&bytes[8..12], &BASE_FORMAT_VERSION.to_le_bytes());
        assert_eq!(round_trip(&unspecified), unspecified);

        let mut encodings = std::collections::BTreeSet::new();
        for kind in every_assert_kind() {
            let module = assert_kind_module(&[kind]);
            let bytes = serialize_module(&module).expect("serialize_module: test fixture");
            assert_eq!(
                &bytes[8..12],
                &ASSERT_KIND_FORMAT_VERSION.to_le_bytes(),
                "{kind:?} selects the assert-kind version"
            );
            let back = round_trip(&module);
            assert_eq!(back, module, "{kind:?} must round-trip exactly");
            assert!(encodings.insert(bytes), "{kind:?} shares an encoding");
        }
        // All kinds in one body, in order, survive together.
        let all = assert_kind_module(&every_assert_kind());
        assert_eq!(round_trip(&all), all);
    }

    /// Plan item P: the kind is the TAG. A kindless assert is Inst tag 29 with
    /// the condition only (its pre-v52 bytes); a kinded one is tag 63, the
    /// condition, then the AssertKind byte and its payload.
    #[test]
    fn assert_kind_wire_spelling_is_pinned() {
        let encode = |kind: AssertKind| {
            SealedStringPool::by_replay(|pool, buf| {
                write_inst(
                    buf,
                    pool,
                    None,
                    &Inst::Assert {
                        cond: v(5),
                        kind,
                        site: None,
                    },
                );
            })
        };
        assert_eq!(encode(AssertKind::Unspecified), vec![29, 5]);
        assert_eq!(
            encode(AssertKind::Overflow(AssertOverflowOp::Neg)),
            vec![63, 5, 0, 7]
        );
        assert_eq!(encode(AssertKind::DivByZero), vec![63, 5, 1]);
        assert_eq!(encode(AssertKind::RemByZero), vec![63, 5, 2]);
        assert_eq!(
            encode(AssertKind::BoundsCheck {
                index: v(1),
                len: v(2)
            }),
            vec![63, 5, 3, 1, 2]
        );
        assert_eq!(
            encode(AssertKind::MisalignedPtr {
                required: v(3),
                found: v(4)
            }),
            vec![63, 5, 4, 3, 4]
        );
        assert_eq!(encode(AssertKind::NullPtr), vec![63, 5, 5]);
    }

    /// Plan item P: an assert in a blob written WITHOUT a kind (tag 29) decodes
    /// to `AssertKind::Unspecified` — the kind it never recorded — both at the
    /// base header and at the last header before the kind existed (a module
    /// that needs v51 for another feature). Real pre-v52 goldens are decoded
    /// the same way by the conformance crate
    /// (`every_pre_assert_kind_golden_assert_decodes_as_unspecified`).
    #[test]
    fn an_older_blob_assert_decodes_as_unspecified() {
        let base = assert_kind_module(&[AssertKind::Unspecified]);
        let mut at_v51 = base.clone();
        // A rotate is read-gated on v51, so it lifts the header to exactly 51.
        at_v51.functions[0].blocks[0].body.insert(
            0,
            InstrNode::new(Inst::BinOp {
                op: BinOp::RotL,
                ty: Ty::Usize,
                lhs: v(1),
                rhs: v(2),
            })
            .with_result(v(3)),
        );
        for (module, header) in [
            (base, BASE_FORMAT_VERSION),
            (at_v51, ASSERT_KIND_FORMAT_VERSION - 1),
        ] {
            let bytes = serialize_module(&module).expect("serialize_module: test fixture");
            assert_eq!(&bytes[8..12], &header.to_le_bytes());
            let decoded = deserialize_module(&bytes).expect("decodes");
            let asserts: Vec<&Inst> = decoded.functions[0].blocks[0]
                .body
                .iter()
                .map(|node| &node.inst)
                .filter(|inst| matches!(inst, Inst::Assert { .. }))
                .collect();
            assert_eq!(
                asserts,
                vec![&Inst::Assert {
                    cond: v(0),
                    kind: AssertKind::Unspecified,
                    site: None
                }],
                "v{header}"
            );
        }
    }

    /// Plan item P: tag 63 is read-gated. A blob that CLAIMS an older readable
    /// version and carries a kinded assert is refused, never read with its kind
    /// dropped; the v38 projections refuse it by name.
    #[test]
    fn kinded_assert_tag_is_refused_below_its_version() {
        let kinded = assert_kind_module(&[AssertKind::DivByZero]);
        let bytes = serialize_module(&kinded).expect("serialize_module: test fixture");
        for older in [ASSERT_KIND_FORMAT_VERSION - 1, BASE_FORMAT_VERSION] {
            let mut forged = bytes.clone();
            forged[8..12].copy_from_slice(&older.to_le_bytes());
            assert_eq!(
                deserialize_module(&forged),
                Err(BinaryError::InvalidTag(63)),
                "a v{older}-labelled blob carrying instruction tag 63 must be refused"
            );
        }
        for body in [ModuleBinaryBody::RawV38, ModuleBinaryBody::CanonicalV38] {
            let options = ModuleBinaryOptions {
                body,
                ..Default::default()
            };
            assert_eq!(
                ProjectedModuleBinaryPlan::try_new(&kinded, options).err(),
                Some(BinaryProjectionError::AssertKindRequiresV52)
            );
            let unspecified = assert_kind_module(&[AssertKind::Unspecified]);
            assert!(ProjectedModuleBinaryPlan::try_new(&unspecified, options).is_ok());
        }
    }

    /// Plan item P: the AssertKind and AssertOverflowOp bytes are closed. A
    /// tag-63 assert whose kind byte is past the last kind, or whose overflow
    /// op byte is past `Neg`, is refused — there is no byte for `Unspecified`
    /// to smuggle a second spelling through.
    #[test]
    fn an_unknown_assert_kind_or_overflow_op_byte_is_refused() {
        let module = assert_kind_module(&[AssertKind::Overflow(AssertOverflowOp::Add)]);
        let bytes = serialize_module(&module).expect("serialize_module: test fixture");
        let at = bytes
            .windows(4)
            .position(|w| w == [63, 0, 0, 0])
            .expect("the kinded assert's bytes: tag 63, cond %0, Overflow, Add");
        let mut bad_kind = bytes.clone();
        bad_kind[at + 2] = 6;
        assert_eq!(
            deserialize_module(&bad_kind),
            Err(BinaryError::InvalidTag(6))
        );
        let mut bad_op = bytes.clone();
        bad_op[at + 3] = 8;
        assert_eq!(deserialize_module(&bad_op), Err(BinaryError::InvalidTag(8)));
    }

    /// Plan item P: the stable digest keeps a kindless module's identity (it
    /// spells tag 29 as before) and tells kinds apart.
    #[test]
    fn the_stable_digest_separates_assert_kinds() {
        let digest = |kind| assert_kind_module(&[kind]).stable_digest();
        let mut seen = vec![digest(AssertKind::Unspecified)];
        for kind in every_assert_kind() {
            let d = digest(kind);
            assert!(!seen.contains(&d), "{kind:?} digests like another kind");
            seen.push(d);
        }
    }

    // ── Amendment P (wire v54): the panic site ───────────────────────────

    fn site(entry: u32, location: PanicLocation) -> PanicSite {
        PanicSite {
            entry: FuncId::new(entry),
            location,
        }
    }

    /// `check(c: bool, a: usize, b: usize, p: ptr)` carrying `insts` before
    /// its return, with an entry declaration (function 1) and a location
    /// global (global 0). `insts` may end the block early (an
    /// `AssertInvoke`), so a second block that returns is always present.
    fn panic_site_module(insts: &[Inst]) -> Module {
        let mut module = Module::new("panic_site");
        let ft = module
            .add_func_type(FuncTy {
                params: vec![Ty::Bool, Ty::Usize, Ty::Usize, Ty::Ptr],
                returns: vec![],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let entry_ft = module
            .add_func_type(FuncTy {
                abi: None,
                params: vec![Ty::Usize, Ty::Usize, Ty::Ptr],
                returns: vec![],
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut func = Function::new(FuncId::new(0), "check", ft, BlockId::new(0));
        let mut entry = Block::new(BlockId::new(0));
        entry.params.extend([
            (v(0), Ty::Bool),
            (v(1), Ty::Usize),
            (v(2), Ty::Usize),
            (v(3), Ty::Ptr),
        ]);
        for inst in insts {
            entry.body.push(InstrNode::new(inst.clone()));
        }
        entry
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        let mut tail = Block::new(BlockId::new(1));
        tail.body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        func.blocks.extend([entry, tail]);
        module.functions.push(func);
        module.functions.push(Function::new(
            FuncId::new(1),
            "panic_entry",
            entry_ft,
            BlockId::new(0),
        ));
        module.globals.push(crate::Global {
            name: "loc".into(),
            ty: Ty::U64,
            mutable: false,
            initializer: Some(Constant::Int(7)),
            linkage: crate::Linkage::Internal,
            tls: None,
            align: None,
            section: None,
            visibility: Default::default(),
            retained: false,
        });
        module
    }

    /// One assert per wire spelling: tag 29 (kindless, siteless), 63
    /// (kinded, siteless), 66 (sited: Unspecified and kinded, both location
    /// spellings) and 67 (`AssertInvoke`).
    fn every_assert_spelling() -> Vec<(u8, Inst)> {
        let bounds = AssertKind::BoundsCheck {
            index: v(1),
            len: v(2),
        };
        vec![
            (
                29,
                Inst::Assert {
                    cond: v(0),
                    kind: AssertKind::Unspecified,
                    site: None,
                },
            ),
            (
                63,
                Inst::Assert {
                    cond: v(0),
                    kind: bounds,
                    site: None,
                },
            ),
            (
                66,
                Inst::Assert {
                    cond: v(0),
                    kind: AssertKind::Unspecified,
                    site: Some(site(1, PanicLocation::Global(GlobalId::new(0)))),
                },
            ),
            (
                66,
                Inst::Assert {
                    cond: v(0),
                    kind: bounds,
                    site: Some(site(1, PanicLocation::Value(v(3)))),
                },
            ),
            (
                67,
                Inst::AssertInvoke {
                    cond: v(0),
                    kind: AssertKind::DivByZero,
                    site: site(1, PanicLocation::Global(GlobalId::new(0))),
                    normal_dest: BlockId::new(1),
                    normal_args: vec![],
                    unwind_dest: BlockId::new(1),
                },
            ),
        ]
    }

    /// Amendment P: EVERY assert spelling survives the binary codec exactly,
    /// at its own version: tags 29 and 63 keep the versions they had, tags 66
    /// and 67 raise the module to `PANIC_SITE_FORMAT_VERSION`.
    #[test]
    fn every_assert_spelling_round_trips_at_its_version() {
        for (tag, inst) in every_assert_spelling() {
            let module = panic_site_module(std::slice::from_ref(&inst));
            let bytes = serialize_module(&module).expect("serialize_module: test fixture");
            let expected = match tag {
                29 => BASE_FORMAT_VERSION,
                63 => ASSERT_KIND_FORMAT_VERSION,
                _ => PANIC_SITE_FORMAT_VERSION,
            };
            assert_eq!(
                &bytes[8..12],
                &expected.to_le_bytes(),
                "tag {tag}: {inst:?}"
            );
            assert_eq!(round_trip(&module), module, "tag {tag}: {inst:?}");
        }
        let all: Vec<Inst> = every_assert_spelling()
            .into_iter()
            .map(|(_, inst)| inst)
            .collect();
        let module = panic_site_module(&all);
        assert_eq!(round_trip(&module), module);
    }

    /// Amendment P: the site is the TAG and its payload is pinned byte for
    /// byte — the condition, the kind-presence byte (0 Unspecified, 1 a kind
    /// follows), the kind, the entry, the PanicLocation byte (0 Global, 1
    /// Value) and its id; `AssertInvoke` appends `Invoke`'s successors.
    #[test]
    fn panic_site_wire_spelling_is_pinned() {
        let encode = |inst: Inst| {
            SealedStringPool::by_replay(|pool, buf| {
                write_inst(buf, pool, None, &inst);
            })
        };
        assert_eq!(
            encode(Inst::Assert {
                cond: v(5),
                kind: AssertKind::Unspecified,
                site: Some(site(7, PanicLocation::Global(GlobalId::new(3)))),
            }),
            vec![66, 5, 0, 7, 0, 3]
        );
        assert_eq!(
            encode(Inst::Assert {
                cond: v(5),
                kind: AssertKind::BoundsCheck {
                    index: v(1),
                    len: v(2),
                },
                site: Some(site(4, PanicLocation::Value(v(9)))),
            }),
            vec![66, 5, 1, 3, 1, 2, 4, 1, 9]
        );
        assert_eq!(
            encode(Inst::Assert {
                cond: v(5),
                kind: AssertKind::Overflow(AssertOverflowOp::Add),
                site: Some(site(3, PanicLocation::Value(v(7)))),
            }),
            vec![66, 5, 1, 0, 0, 3, 1, 7]
        );
        assert_eq!(
            encode(Inst::AssertInvoke {
                cond: v(5),
                kind: AssertKind::DivByZero,
                site: site(5, PanicLocation::Global(GlobalId::new(1))),
                normal_dest: BlockId::new(2),
                normal_args: vec![v(6)],
                unwind_dest: BlockId::new(7),
            }),
            vec![67, 5, 1, 1, 5, 0, 1, 2, 1, 6, 7]
        );
        // The siteless spellings are unchanged.
        assert_eq!(
            encode(Inst::Assert {
                cond: v(5),
                kind: AssertKind::Unspecified,
                site: None,
            }),
            vec![29, 5]
        );
    }

    /// Amendment P: tags 66 and 67 are read-gated. A blob that CLAIMS an
    /// older readable version and carries one is refused, never read with
    /// its site dropped.
    #[test]
    fn sited_assert_and_assert_invoke_tags_are_refused_below_their_version() {
        for (tag, inst) in every_assert_spelling()
            .into_iter()
            .filter(|(tag, _)| matches!(*tag, 66 | 67))
        {
            let bytes = serialize_module(&panic_site_module(&[inst]))
                .expect("serialize_module: test fixture");
            // The last header before the site existed reads everything else
            // this module carries, so it refuses exactly the instruction tag.
            let older = PANIC_SITE_FORMAT_VERSION - 1;
            let mut forged = bytes.clone();
            forged[8..12].copy_from_slice(&older.to_le_bytes());
            assert_eq!(
                deserialize_module(&forged),
                Err(BinaryError::InvalidTag(tag)),
                "a v{older}-labelled blob carrying instruction tag {tag} must be refused"
            );
            // An older header still refuses the blob (at whichever byte it
            // first cannot read), never decodes it with the site dropped.
            let mut forged = bytes.clone();
            forged[8..12].copy_from_slice(&BASE_FORMAT_VERSION.to_le_bytes());
            assert!(
                deserialize_module(&forged).is_err(),
                "tag {tag} at the base header"
            );
        }
    }

    /// Amendment P: the v38 projections refuse a panic site by name, the
    /// highest arm of the cascade.
    #[test]
    fn the_v38_projections_refuse_a_panic_site() {
        for (tag, inst) in every_assert_spelling() {
            let module = panic_site_module(&[inst]);
            for body in [ModuleBinaryBody::RawV38, ModuleBinaryBody::CanonicalV38] {
                let options = ModuleBinaryOptions {
                    body,
                    ..Default::default()
                };
                let verdict = ProjectedModuleBinaryPlan::try_new(&module, options).err();
                let expected = match tag {
                    29 => None,
                    63 => Some(BinaryProjectionError::AssertKindRequiresV52),
                    _ => Some(BinaryProjectionError::PanicSiteRequiresV54),
                };
                assert_eq!(verdict, expected, "tag {tag}");
            }
        }
    }

    /// Amendment P: the PanicLocation and kind-presence bytes are closed.
    #[test]
    fn an_unknown_panic_location_or_kind_presence_byte_is_refused() {
        let module = panic_site_module(&[Inst::Assert {
            cond: v(0),
            kind: AssertKind::Unspecified,
            site: Some(site(1, PanicLocation::Global(GlobalId::new(0)))),
        }]);
        let bytes = serialize_module(&module).expect("serialize_module: test fixture");
        let at = bytes
            .windows(6)
            .position(|w| w == [66, 0, 0, 1, 0, 0])
            .expect("the sited assert's bytes: tag 66, cond %0, Unspecified, entry 1, Global, 0");
        let mut bad_location = bytes.clone();
        bad_location[at + 4] = 2;
        assert_eq!(
            deserialize_module(&bad_location),
            Err(BinaryError::InvalidTag(2))
        );
        let mut bad_presence = bytes.clone();
        bad_presence[at + 2] = 2;
        assert_eq!(
            deserialize_module(&bad_presence),
            Err(BinaryError::InvalidTag(2))
        );
    }

    /// Amendment P: a module without a site keeps its version, its bytes and
    /// its digest — the siteless spellings are exactly what they were.
    #[test]
    fn a_module_without_a_panic_site_keeps_its_bytes_and_digest() {
        let siteless = assert_kind_module(&every_assert_kind());
        let bytes = serialize_module(&siteless).expect("serialize_module: test fixture");
        assert_eq!(&bytes[8..12], &ASSERT_KIND_FORMAT_VERSION.to_le_bytes());
        assert!(
            !bytes.windows(2).any(|w| w[0] == 66 || w[0] == 67) || {
                // A 66/67 byte may occur inside other payloads; the decode
                // proves no instruction was read as a sited assert.
                let decoded = deserialize_module(&bytes).expect("decodes");
                decoded.functions[0].blocks[0]
                    .body
                    .iter()
                    .all(|node| node.inst.panic_site().is_none())
            }
        );
        let unspecified = assert_kind_module(&[AssertKind::Unspecified]);
        let base = serialize_module(&unspecified).expect("serialize_module: test fixture");
        assert_eq!(&base[8..12], &BASE_FORMAT_VERSION.to_le_bytes());
        // Adding a site to the same module raises it and changes its digest;
        // removing it again restores both exactly.
        let mut sited = unspecified.clone();
        if let Inst::Assert { site: s, .. } = &mut sited.functions[0].blocks[0].body[0].inst {
            *s = Some(site(0, PanicLocation::Value(v(1))));
        }
        assert_ne!(sited.stable_digest(), unspecified.stable_digest());
        let mut restored = sited.clone();
        if let Inst::Assert { site: s, .. } = &mut restored.functions[0].blocks[0].body[0].inst {
            *s = None;
        }
        assert_eq!(
            serialize_module(&restored).expect("serialize_module: test fixture"),
            base
        );
        assert_eq!(restored.stable_digest(), unspecified.stable_digest());
    }

    /// Amendment P: the stable digest tells sites apart — the entry, Global
    /// vs Value, the global id, the value id, and Unspecified vs kinded.
    #[test]
    fn the_stable_digest_separates_panic_sites() {
        let assert_with = |kind, site| Inst::Assert {
            cond: v(0),
            kind,
            site,
        };
        let variants = [
            assert_with(AssertKind::Unspecified, None),
            assert_with(
                AssertKind::Unspecified,
                Some(site(1, PanicLocation::Global(GlobalId::new(0)))),
            ),
            assert_with(
                AssertKind::Unspecified,
                Some(site(0, PanicLocation::Global(GlobalId::new(0)))),
            ),
            assert_with(
                AssertKind::Unspecified,
                Some(site(1, PanicLocation::Global(GlobalId::new(1)))),
            ),
            assert_with(
                AssertKind::Unspecified,
                Some(site(1, PanicLocation::Value(v(3)))),
            ),
            assert_with(
                AssertKind::Unspecified,
                Some(site(1, PanicLocation::Value(v(2)))),
            ),
            assert_with(
                AssertKind::NullPtr,
                Some(site(1, PanicLocation::Global(GlobalId::new(0)))),
            ),
        ];
        let mut seen = Vec::new();
        for inst in variants {
            let digest = panic_site_module(std::slice::from_ref(&inst)).stable_digest();
            assert!(
                !seen.contains(&digest),
                "{inst:?} digests like another site"
            );
            seen.push(digest);
        }
    }

    /// One function that builds `Option<u64>` as a flat `{ isize, u64 }` NONE: the tag lane
    /// written, the payload lane an unwritten `uninit` (crystal E3b), and returns it.
    fn uninit_lane_module(unwritten: bool) -> Module {
        let mut module = Module::new("uninit_lane");
        module.add_struct(StructDef {
            id: StructId::new(0),
            name: "core::option::Option".to_string(),
            fields: vec![
                FieldDef {
                    name: "tag".to_string(),
                    ty: Ty::Isize,
                    offset: None,
                },
                FieldDef {
                    name: "payload".to_string(),
                    ty: Ty::U64,
                    offset: None,
                },
            ],
            size: None,
            align: None,
            repr: Default::default(),
            origin: None,
        });
        let agg = Ty::Struct(StructId::new(0));
        let ft = module
            .add_func_type(FuncTy {
                params: vec![],
                returns: vec![agg.clone()],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut func = Function::new(FuncId::new(0), "none", ft, BlockId::new(0));
        let mut entry = Block::new(BlockId::new(0));
        let lane = if unwritten {
            Constant::Uninit
        } else {
            Constant::Int(0)
        };
        entry.body.push(
            InstrNode::new(Inst::Const {
                ty: agg,
                value: Constant::Aggregate(vec![Constant::Int(0), lane]),
            })
            .with_result(v(0)),
        );
        entry
            .body
            .push(InstrNode::new(Inst::Return { values: vec![v(0)] }));
        func.blocks.push(entry);
        module.functions.push(func);
        module
    }

    /// Crystal lane (E3b): an unwritten lane survives the codec as `Constant::Uninit` and raises
    /// only ITS module to `UNINIT_LANE_FORMAT_VERSION`; the same module with a written lane stays
    /// at the base version byte for byte.
    #[test]
    fn uninit_lane_round_trips_at_its_version_and_a_written_lane_stays_at_the_base_version() {
        let written = uninit_lane_module(false);
        let written_bytes = serialize_module(&written).expect("serialize_module: test fixture");
        assert_eq!(&written_bytes[8..12], &BASE_FORMAT_VERSION.to_le_bytes());
        round_trip(&written);

        let unwritten = uninit_lane_module(true);
        let unwritten_bytes = serialize_module(&unwritten).expect("serialize_module: test fixture");
        assert_eq!(
            &unwritten_bytes[8..12],
            &UNINIT_LANE_FORMAT_VERSION.to_le_bytes()
        );
        let back = round_trip(&unwritten);
        assert!(matches!(
            &back.functions[0].blocks[0].body[0].inst,
            Inst::Const { value: Constant::Aggregate(lanes), .. }
                if lanes.as_slice() == [Constant::Int(0), Constant::Uninit]
        ));
    }

    /// Crystal lane (E3b): constant tag 15 is read-gated. A blob that CLAIMS any older readable
    /// version and carries an unwritten lane is malformed and refused -- never read as some
    /// other constant. The explicit v38 projections refuse it by name.
    #[test]
    fn uninit_lane_tag_is_refused_below_its_version() {
        let bytes =
            serialize_module(&uninit_lane_module(true)).expect("serialize_module: test fixture");
        for older in [UNINIT_LANE_FORMAT_VERSION - 1, BASE_FORMAT_VERSION] {
            let mut forged = bytes.clone();
            forged[8..12].copy_from_slice(&older.to_le_bytes());
            assert_eq!(
                deserialize_module(&forged),
                Err(BinaryError::InvalidTag(15)),
                "a v{older}-labelled blob carrying constant tag 15 must be refused"
            );
        }
        for body in [ModuleBinaryBody::RawV38, ModuleBinaryBody::CanonicalV38] {
            let options = ModuleBinaryOptions {
                body,
                ..Default::default()
            };
            assert_eq!(
                ProjectedModuleBinaryPlan::try_new(&uninit_lane_module(true), options).err(),
                Some(BinaryProjectionError::UninitLaneRequiresV49)
            );
            assert!(
                ProjectedModuleBinaryPlan::try_new(&uninit_lane_module(false), options).is_ok()
            );
        }
    }

    /// Opaque island declaration bytes of the wire fixture: a pattern no
    /// other field of the fixture spells, so a test can find the island's
    /// presence byte in the encoding.
    const ISLAND_FIXTURE_BYTES: [u8; 5] = [0xD1; 5];

    /// A module whose one certificate carries a CleanCic directive, bound
    /// (`bound = true`, every optional binding field populated — the WS1.13
    /// island included) or not.
    fn certificate_binding_module(bound: bool) -> Module {
        use crate::proof::{
            CertificateBinding, CleanCicKernelRecheck, IslandEnvironment, ProofCertificate,
            ProofDigest, ProofEvidence, SourceDefinitionRef,
        };
        let mut module = Module::new("certificate_binding_wire");
        module.proof_certificates.push(ProofCertificate {
            obligation: ProofId::new(0),
            prover: "wire fixture; not certified".into(),
            evidence: ProofEvidence::CleanCic {
                term: vec![1, 2],
                context: vec![3],
                lineage: ProofDigest::sha256([4; 32]),
                kernel_recheck: Some(CleanCicKernelRecheck {
                    module: "Wire.Fixture".into(),
                    theorems: vec!["Wire.thm".into()],
                    anchor: "wire_fixture".into(),
                    allowed_axioms: vec![],
                    binding: bound.then(|| {
                        let mut binding = CertificateBinding::new(
                            ProofDigest::sha256([5; 32]),
                            ProofDigest::sha256([6; 32]),
                        );
                        binding.origin_module = Some(ProofDigest::sha256([7; 32]));
                        binding.source = Some(SourceDefinitionRef {
                            decl: "Lib.addmul".into(),
                            closure_digest: ProofDigest::sha256([8; 32]),
                        });
                        binding.callees = vec!["minus".into(), "plus".into()];
                        binding.environment =
                            Some(IslandEnvironment::new(ISLAND_FIXTURE_BYTES.to_vec()));
                        Box::new(binding)
                    }),
                }),
            },
            assurance: None,
        });
        module
    }

    /// A certificate binding survives the codec field for field and raises
    /// only ITS module to `CERTIFICATE_BINDING_FORMAT_VERSION`; the unbound
    /// twin keeps an older header.
    #[test]
    fn certificate_binding_round_trips_at_its_version_and_unbound_stays_older() {
        let unbound = certificate_binding_module(false);
        let unbound_bytes = serialize_module(&unbound).expect("serialize_module: test fixture");
        assert!(
            u32::from_le_bytes(unbound_bytes[8..12].try_into().expect("header"))
                < CERTIFICATE_BINDING_FORMAT_VERSION
        );
        round_trip(&unbound);

        let bound = certificate_binding_module(true);
        let bound_bytes = serialize_module(&bound).expect("serialize_module: test fixture");
        assert_eq!(
            &bound_bytes[8..12],
            &CERTIFICATE_BINDING_FORMAT_VERSION.to_le_bytes()
        );
        assert_eq!(round_trip(&bound), bound);
        assert_ne!(bound.stable_digest(), unbound.stable_digest());
    }

    /// WS1.13 (the `SPEC_RATIFICATIONS` §8 amendment): the island rides the
    /// carrier losslessly as OPAQUE bytes with the digest it RECORDS. Three
    /// adversarial inputs: (1) dropping the island changes the encoding and
    /// the identity (a codec that skipped it could not tell the two apart);
    /// (2) a FORGED island digest survives the codec verbatim — the reader
    /// never recomputes it, so the validator still sees the forgery and
    /// refuses it, instead of a codec laundering it into a true digest; (3)
    /// the island's presence byte is closed (`2` is `InvalidTag(2)`), and a
    /// declaration length running past the end of the blob is refused.
    #[test]
    fn certificate_binding_carries_its_island_losslessly_and_verbatim() {
        use crate::proof::{IslandEnvironment, ProofDigest};
        let bound = certificate_binding_module(true);
        let bytes = serialize_module(&bound).expect("serialize_module: test fixture");

        // (1) the island is on the wire, and it is identity.
        let mut islandless = bound.clone();
        if let crate::proof::ProofEvidence::CleanCic {
            kernel_recheck: Some(recheck),
            ..
        } = &mut islandless.proof_certificates[0].evidence
        {
            recheck.binding.as_mut().expect("bound").environment = None;
        }
        let islandless_bytes =
            serialize_module(&islandless).expect("serialize_module: test fixture");
        assert_ne!(bytes, islandless_bytes, "the island is written");
        assert_ne!(bound.stable_digest(), islandless.stable_digest());
        assert_eq!(round_trip(&islandless), islandless);

        // (2) a forged digest is carried, never recomputed.
        let mut forged = bound.clone();
        let forged_digest = ProofDigest::sha256([0xEE; 32]);
        if let crate::proof::ProofEvidence::CleanCic {
            kernel_recheck: Some(recheck),
            ..
        } = &mut forged.proof_certificates[0].evidence
        {
            recheck.binding.as_mut().expect("bound").environment = Some(IslandEnvironment {
                declarations: ISLAND_FIXTURE_BYTES.to_vec(),
                digest: forged_digest,
            });
        }
        let back = round_trip(&forged);
        assert_eq!(back, forged);
        let carried = back.proof_certificates[0]
            .evidence
            .clean_cic_kernel_recheck()
            .and_then(|r| r.binding.as_deref())
            .and_then(|b| b.environment.clone())
            .expect("the island survives");
        assert_eq!(
            carried.digest, forged_digest,
            "the recorded digest, verbatim"
        );
        assert_ne!(
            carried.digest,
            crate::proof::island_declarations_digest(&carried.declarations),
            "control: the carried digest really is a forgery"
        );

        // (3) the presence byte is closed, and the length frame is checked.
        let window: Vec<u8> = [1_u8, 5].into_iter().chain(ISLAND_FIXTURE_BYTES).collect();
        let marker = bytes
            .windows(window.len())
            .position(|w| w == window.as_slice())
            .expect("presence 1, length 5, then the island bytes");
        let mut raised = bytes.clone();
        raised[marker] = 2;
        assert_eq!(deserialize_module(&raised), Err(BinaryError::InvalidTag(2)));
        // A declared island length far past the end of the blob (LEB128
        // 2^28 - 1 in place of the one-byte 5) is refused before allocating.
        let mut overlong = bytes.clone();
        overlong.splice(marker + 1..marker + 2, [0xFF, 0xFF, 0xFF, 0x7F]);
        assert!(
            matches!(
                deserialize_module(&overlong),
                Err(BinaryError::TooLarge { .. })
            ),
            "{:?}",
            deserialize_module(&overlong)
        );
    }

    /// The carrier is read-gated and its presence byte is closed: a bound blob
    /// relabelled as an older readable version never decodes, an undefined
    /// presence tag is `InvalidTag`, and the explicit v38 projections refuse a
    /// bound module by name.
    #[test]
    fn certificate_binding_is_refused_below_its_version_and_by_v38_projections() {
        let bound = certificate_binding_module(true);
        let bytes = serialize_module(&bound).expect("serialize_module: test fixture");
        let mut exercised = 0;
        for older in [
            CERTIFICATE_BINDING_FORMAT_VERSION - 1,
            UNINIT_LANE_FORMAT_VERSION,
            BASE_FORMAT_VERSION,
        ] {
            if !(MIN_READ_VERSION..=VERSION).contains(&older)
                || AMBIGUOUS_LINEAGE_VERSIONS.contains(&older)
            {
                continue;
            }
            let mut probe = MAGIC.to_vec();
            probe.extend_from_slice(&older.to_le_bytes());
            if matches!(
                deserialize_module(&probe),
                Err(BinaryError::UnsupportedVersion)
            ) {
                continue; // a reserved number: no reader accepts its header yet
            }
            let mut forged = bytes.clone();
            forged[8..12].copy_from_slice(&older.to_le_bytes());
            assert!(
                deserialize_module(&forged).is_err(),
                "a v{older}-labelled blob carrying a binding must be refused"
            );
            exercised += 1;
        }
        assert!(
            exercised > 0,
            "at least one older READABLE header was probed"
        );
        // The binding's presence byte (1) is followed by the environment
        // digest: algorithm byte 0 (SHA-256), then the fixture's 32 bytes of 5.
        // Rewriting that presence byte to 2 must be refused by name.
        let mut raised = bytes.clone();
        let marker = raised
            .windows(34)
            .position(|w| w[0] == 1 && w[1] == 0 && w[2..].iter().all(|b| *b == 5))
            .expect("the binding presence byte precedes the environment digest");
        raised[marker] = 2;
        assert_eq!(deserialize_module(&raised), Err(BinaryError::InvalidTag(2)));

        for body in [ModuleBinaryBody::RawV38, ModuleBinaryBody::CanonicalV38] {
            let options = ModuleBinaryOptions {
                body,
                ..Default::default()
            };
            assert_eq!(
                ProjectedModuleBinaryPlan::try_new(&bound, options).err(),
                Some(BinaryProjectionError::CertificateBindingRequiresV61)
            );
            assert!(
                ProjectedModuleBinaryPlan::try_new(&certificate_binding_module(false), options)
                    .is_ok()
            );
        }
    }

    /// A one-function module licensed `clean-kernel-tv`, with (`evidenced`)
    /// or without `GateEvidence`.
    fn evidenced_license_module(evidenced: bool) -> Module {
        let mut module = Module::new("evidenced_license");
        let ft = module
            .add_func_type(FuncTy {
                params: vec![],
                returns: vec![Ty::U64],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut func = Function::new(FuncId::new(0), "f", ft, BlockId::new(0));
        let mut entry = Block::new(BlockId::new(0));
        entry.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::U64,
                value: Constant::Int(1),
            })
            .with_result(v(0)),
        );
        entry
            .body
            .push(InstrNode::new(Inst::Return { values: vec![v(0)] }));
        func.blocks.push(entry);
        func.body_gate = Some(crate::BodyGate::Gated {
            authority: "clean-kernel-tv".to_string(),
            evidence: evidenced.then(|| crate::GateEvidence {
                obligation: ProofId::new(0),
                body_digest: crate::proof::ProofDigest::sha256([9; 32]),
            }),
        });
        module.functions.push(func);
        module
    }

    /// v61 tag 3: an evidenced license round-trips at the proof-surface
    /// version, the evidence-free license keeps tag 2 and its older header,
    /// tag 3 under the header just below it is `InvalidTag(3)` and under any
    /// older readable header is refused (never read as an evidence-free
    /// license), and the v38 projections refuse it by name.
    #[test]
    fn evidenced_license_round_trips_at_its_version_and_is_refused_below_it() {
        let plain = evidenced_license_module(false);
        let plain_bytes = serialize_module(&plain).expect("serialize_module: test fixture");
        assert!(
            u32::from_le_bytes(plain_bytes[8..12].try_into().expect("header"))
                < CERTIFICATE_BINDING_FORMAT_VERSION
        );
        assert_eq!(round_trip(&plain), plain);

        let evidenced = evidenced_license_module(true);
        let bytes = serialize_module(&evidenced).expect("serialize_module: test fixture");
        assert_eq!(
            &bytes[8..12],
            &CERTIFICATE_BINDING_FORMAT_VERSION.to_le_bytes()
        );
        assert_eq!(round_trip(&evidenced), evidenced);

        let mut exercised = 0;
        for older in [
            CERTIFICATE_BINDING_FORMAT_VERSION - 1,
            UNINIT_LANE_FORMAT_VERSION,
            CONTRACT_SURFACE_FORMAT_VERSION,
        ] {
            if AMBIGUOUS_LINEAGE_VERSIONS.contains(&older)
                || !(MIN_READ_VERSION..CERTIFICATE_BINDING_FORMAT_VERSION).contains(&older)
            {
                continue;
            }
            let mut probe = MAGIC.to_vec();
            probe.extend_from_slice(&older.to_le_bytes());
            if matches!(
                deserialize_module(&probe),
                Err(BinaryError::UnsupportedVersion)
            ) {
                continue; // a reserved number: no reader accepts its header yet
            }
            let mut forged = bytes.clone();
            forged[8..12].copy_from_slice(&older.to_le_bytes());
            let decoded = deserialize_module(&forged);
            if older + 1 == CERTIFICATE_BINDING_FORMAT_VERSION {
                // The header just below the carrier reads every byte before
                // the license as written, so the refusal is AT the tag.
                assert_eq!(
                    decoded,
                    Err(BinaryError::InvalidTag(3)),
                    "a v{older}-labelled blob carrying body-gate tag 3 must be refused at the tag"
                );
            } else {
                // Below v60 the reader also stops reading v60's per-FuncTy
                // `abi` presence byte, so the forged stream is refused before
                // the license is reached; refused either way, and never
                // decoded as the evidence-free twin.
                assert!(
                    decoded.is_err(),
                    "a v{older}-labelled blob carrying body-gate tag 3 must be refused: {decoded:?}"
                );
            }
            exercised += 1;
        }
        assert!(
            exercised > 0,
            "at least one older readable header was probed"
        );

        for body in [ModuleBinaryBody::RawV38, ModuleBinaryBody::CanonicalV38] {
            let options = ModuleBinaryOptions {
                body,
                ..Default::default()
            };
            assert_eq!(
                ProjectedModuleBinaryPlan::try_new(&evidenced, options).err(),
                Some(BinaryProjectionError::CertificateBindingRequiresV61)
            );
        }
        // The executable projection strips the license, evidence included.
        assert_eq!(
            evidenced.executable_content_digest_v1(),
            plain.executable_content_digest_v1()
        );
    }

    // --- Separate-compilation contract (v18) ---

    #[test]
    fn function_summary_declaration_round_trips() {
        use crate::{FunctionSummary, ProofFormula};
        let mut module = Module::new("composition");
        let ft = module
            .add_func_type(FuncTy {
                params: vec![Ty::I32],
                returns: vec![Ty::I32],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
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
        module
            .try_add_function(decl)
            .expect("Module::try_add_function: test fixture");

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
        let ft = module
            .add_func_type(FuncTy {
                params: vec![Ty::I32],
                returns: vec![Ty::I32],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
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
        module
            .try_add_function(named)
            .expect("Module::try_add_function: test fixture");
        let mut anon = Function::new(FuncId::new(1), "anon", ft, BlockId(0));
        anon.blocks.push(Block {
            id: BlockId(0),
            params: vec![(ValueId::new(0), Ty::I32)],
            body: vec![InstrNode::new(Inst::Return {
                values: vec![ValueId::new(0)],
            })],
        });
        module
            .try_add_function(anon)
            .expect("Module::try_add_function: test fixture");

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
        let ft = module
            .add_func_type(FuncTy {
                params: vec![Ty::I32],
                returns: vec![Ty::I32],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
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
                inlined_at: None,
            },
            ScopeData {
                parent: Some(0),
                span: Some(SourceSpan {
                    file: 0,
                    line: 2,
                    col: 4,
                }),
                inlined_at: None,
            },
            // A span-less scope is legal: the producer knew the nesting but not
            // the location. Pinned so the presence bytes stay independent.
            ScopeData {
                parent: Some(1),
                span: None,
                inlined_at: None,
            },
        ]);
        module
            .try_add_function(scoped)
            .expect("Module::try_add_function: test fixture");
        let mut flat = Function::new(FuncId::new(1), "flat", ft, BlockId(0));
        flat.blocks.push(Block {
            id: BlockId(0),
            params: Vec::new(),
            body: Vec::new(),
        });
        module
            .try_add_function(flat)
            .expect("Module::try_add_function: test fixture");

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
                        }),
                        inlined_at: None,
                    },
                    ScopeData {
                        parent: Some(0),
                        span: Some(SourceSpan {
                            file: 0,
                            line: 2,
                            col: 4
                        }),
                        inlined_at: None,
                    },
                    ScopeData {
                        parent: Some(1),
                        span: None,
                        inlined_at: None,
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
        let ft = module
            .add_func_type(FuncTy {
                params: vec![],
                returns: vec![Ty::Unit],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        for (i, producer) in producers.iter().enumerate() {
            let mut func = Function::new(FuncId::new(i as u32), format!("f{i}"), ft, b(0));
            func.producer = Some(producer.clone());
            let mut block = Block::new(b(0));
            block
                .body
                .push(InstrNode::new(Inst::Return { values: vec![] }));
            func.blocks.push(block);
            module
                .try_add_function(func)
                .expect("Module::try_add_function: test fixture");
        }
        // Plus one untagged function: None must round-trip as None.
        let mut untagged = Function::new(FuncId::new(6), "untagged", ft, b(0));
        let mut block = Block::new(b(0));
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        untagged.blocks.push(block);
        module
            .try_add_function(untagged)
            .expect("Module::try_add_function: test fixture");

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
        let ft = module
            .add_func_type(FuncTy {
                params: vec![],
                returns: vec![Ty::Unit],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut func = Function::new(FuncId::new(0), "f", ft, b(0));
        let mut block = Block::new(b(0));
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        func.blocks.push(block);
        assert!(func.has_body());
        assert!(func.summary.is_none());
        module
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");
        let back = round_trip(&module);
        assert!(back.functions[0].summary.is_none());
    }

    // --- Header tests ---

    #[test]
    fn header_magic_and_version() {
        let module = Module::new("header_test");
        let bytes = serialize_module(&module).expect("serialize_module: test fixture");
        assert_eq!(&bytes[0..8], b"TRUST_IR");
        assert_eq!(
            u32::from_le_bytes([bytes[8], bytes[9], bytes[10], bytes[11]]),
            BASE_FORMAT_VERSION
        );
    }

    #[test]
    fn v25_spec_anchor_defaults_trailing_function_to_none() {
        // Forge exactly the pre-v26 SpecModule record: project is the final
        // anchor field, immediately followed by the waiver count. The v26
        // reader must not consume that count as a function presence tag.
        let pool = sealed_pool(|p| {
            for s in [
                "crate::Machine",
                "Step",
                "crate::Machine::step",
                "fixture.rs:1:1",
                "crate::project",
            ] {
                p.intern(s);
            }
        });
        let mut bytes = Vec::new();
        write_str(&mut bytes, &pool, "crate::Machine");
        write_v32(&mut bytes, 0); // vars
        write_v32(&mut bytes, 1); // actions
        write_str(&mut bytes, &pool, "Step");
        write_v32(&mut bytes, 0); // invariants
        write_v32(&mut bytes, 1); // anchors
        write_str(&mut bytes, &pool, "crate::Machine");
        write_str(&mut bytes, &pool, "Step");
        write_str(&mut bytes, &pool, "crate::Machine::step");
        write_str(&mut bytes, &pool, "fixture.rs:1:1");
        write_u8(&mut bytes, 1); // project Some
        write_str(&mut bytes, &pool, "crate::project");
        // v25 has no SpecAnchor.function bytes here.
        write_v32(&mut bytes, 0); // waivers
        write_u8(&mut bytes, 0); // embedded origin
        write_v32(&mut bytes, 0); // proofs (v14+)

        let mut reader = Reader::new(&bytes);
        reader.version = 25;
        reader.pool = Some(pool.into_reader_strings());
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
        let pool = sealed_pool(|p| {
            for s in [
                "crate::Machine",
                "Step",
                "crate::Machine::step",
                "fixture.rs:1:1",
                "crate::project",
            ] {
                p.intern(s);
            }
        });
        let mut bytes = Vec::new();
        write_str(&mut bytes, &pool, "crate::Machine");
        write_v32(&mut bytes, 0); // vars
        write_v32(&mut bytes, 1); // actions
        write_str(&mut bytes, &pool, "Step");
        write_v32(&mut bytes, 0); // invariants
        write_v32(&mut bytes, 1); // anchors
        write_str(&mut bytes, &pool, "crate::Machine");
        write_str(&mut bytes, &pool, "Step");
        write_str(&mut bytes, &pool, "crate::Machine::step");
        write_str(&mut bytes, &pool, "fixture.rs:1:1");
        write_u8(&mut bytes, 1);
        write_str(&mut bytes, &pool, "crate::project");
        write_u8(&mut bytes, 1); // action function Some
        write_v32(&mut bytes, 7);
        // v26 has no projection-target bytes here.
        write_v32(&mut bytes, 0); // waivers
        write_u8(&mut bytes, 0); // embedded origin
        write_v32(&mut bytes, 0); // proofs
        // v26 has no enforcement byte here.

        let mut reader = Reader::new(&bytes);
        reader.version = 26;
        reader.pool = Some(pool.into_reader_strings());
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
        let pool = sealed_pool(|p| {
            for s in ["Machine", "Step", "step", "fixture.rs:1:1", "project"] {
                p.intern(s);
            }
        });
        let mut bad_projection = Vec::new();
        write_str(&mut bad_projection, &pool, "Machine");
        write_v32(&mut bad_projection, 0); // vars
        write_v32(&mut bad_projection, 1); // actions
        write_str(&mut bad_projection, &pool, "Step");
        write_v32(&mut bad_projection, 0); // invariants
        write_v32(&mut bad_projection, 1); // anchors
        write_str(&mut bad_projection, &pool, "Machine");
        write_str(&mut bad_projection, &pool, "Step");
        write_str(&mut bad_projection, &pool, "step");
        write_str(&mut bad_projection, &pool, "fixture.rs:1:1");
        write_u8(&mut bad_projection, 1);
        write_str(&mut bad_projection, &pool, "project");
        write_u8(&mut bad_projection, 0); // action function None
        write_u8(&mut bad_projection, 99); // invalid projection target

        let mut reader = Reader::new(&bad_projection);
        reader.version = 27;
        reader.pool = Some(pool.into_reader_strings());
        assert_eq!(
            read_spec_module(&mut reader),
            Err(BinaryError::InvalidTag(99))
        );

        let pool = sealed_pool(|p| {
            p.intern("Machine");
        });
        let mut bad_enforcement = Vec::new();
        write_str(&mut bad_enforcement, &pool, "Machine");
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
        reader.pool = Some(pool.into_reader_strings());
        assert_eq!(
            read_spec_module(&mut reader),
            Err(BinaryError::InvalidTag(99))
        );
    }

    #[test]
    fn invalid_magic_rejected() {
        let mut bytes =
            serialize_module(&Module::new("test")).expect("serialize_module: test fixture");
        bytes[0] = b'X';
        assert_eq!(deserialize_module(&bytes), Err(BinaryError::InvalidMagic));
    }

    #[test]
    fn unsupported_version_rejected() {
        let mut bytes =
            serialize_module(&Module::new("test")).expect("serialize_module: test fixture");
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
            let mut bytes =
                serialize_module(&Module::new("test")).expect("serialize_module: test fixture");
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
        let bytes = serialize_module(&Module::new("test")).expect("serialize_module: test fixture");
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
            module
                .add_type(ty.clone())
                .expect("Module::add_type: test fixture");
        }
        round_trip(&module);
    }

    #[test]
    fn module_with_composite_types() {
        let mut module = Module::new("composites");
        module
            .add_type(Ty::Struct(StructId::new(0)))
            .expect("Module::add_type: test fixture");
        module
            .add_type(Ty::Array(TyId::new(0), 16))
            .expect("Module::add_type: test fixture");
        module
            .add_type(Ty::Tuple(vec![Ty::I32, Ty::Bool]))
            .expect("Module::add_type: test fixture");
        module
            .add_type(Ty::Enum(EnumId::new(0)))
            .expect("Module::add_type: test fixture");
        module
            .add_type(Ty::Func(FuncTyId::new(0)))
            .expect("Module::add_type: test fixture");
        module
            .add_type(Ty::Ref(Box::new(Ty::I32)))
            .expect("Module::add_type: test fixture");
        module
            .add_type(Ty::RefMut(Box::new(Ty::I64)))
            .expect("Module::add_type: test fixture");
        module
            .add_type(Ty::PtrConst(Box::new(Ty::U32)))
            .expect("Module::add_type: test fixture");
        module
            .add_type(Ty::PtrMut(Box::new(Ty::F64)))
            .expect("Module::add_type: test fixture");
        module
            .add_type(Ty::Rc(Box::new(Ty::Bool)))
            .expect("Module::add_type: test fixture");
        module
            .add_type(Ty::Vector(Box::new(Ty::I32), 4))
            .expect("Module::add_type: test fixture");
        module
            .add_type(Ty::Vector(Box::new(Ty::Bool), 8))
            .expect("Module::add_type: test fixture");
        // Nested reference types
        module
            .add_type(Ty::Ref(Box::new(Ty::RefMut(Box::new(Ty::I32)))))
            .expect("Module::add_type: test fixture");
        module
            .add_type(Ty::Rc(Box::new(Ty::Tuple(vec![Ty::I32, Ty::U64]))))
            .expect("Module::add_type: test fixture");
        round_trip(&module);
    }

    fn vector_instruction_module(name: &str) -> Module {
        let v4i32 = Ty::Vector(Box::new(Ty::I32), 4);
        let v4bool = Ty::Vector(Box::new(Ty::Bool), 4);

        let mut module = Module::new(name);
        module
            .add_type(v4i32.clone())
            .expect("Module::add_type: test fixture");
        module
            .add_type(v4bool.clone())
            .expect("Module::add_type: test fixture");
        let ft = module
            .add_func_type(FuncTy {
                params: vec![Ty::Ptr, v4i32.clone(), v4i32.clone()],
                returns: vec![v4i32.clone(), v4bool.clone()],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");

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
        module
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");
        module
    }

    fn invalid_vector_select_physical_mask_module(name: &str) -> Module {
        let v4i32 = Ty::Vector(Box::new(Ty::I32), 4);

        let mut module = Module::new(name);
        let ft = module
            .add_func_type(FuncTy {
                params: vec![v4i32.clone(), v4i32.clone(), v4i32.clone()],
                returns: vec![v4i32.clone()],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");

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
        module
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");
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
            section: None,
            visibility: crate::Visibility::Default,
            retained: false,
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
            section: None,
            visibility: crate::Visibility::Default,
            retained: false,
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
                section: None,
                visibility: crate::Visibility::Default,
                retained: false,
            });

            let back = round_trip(&module);
            assert_eq!(back.globals[0].tls, Some(tls));
        }
    }

    fn single_global_module(name: &str, align: Option<u32>) -> Module {
        let mut module = Module::new(name);
        module.globals.push(Global {
            name: "G".to_string(),
            ty: Ty::I64,
            mutable: true,
            initializer: None,
            linkage: Linkage::Internal,
            tls: None,
            align,
            section: None,
            visibility: crate::Visibility::Default,
            retained: false,
        });
        module
    }

    #[test]
    fn global_alignment_round_trip_and_v25_default() {
        let aligned = single_global_module("global_align_binary", Some(64));
        let back = round_trip(&aligned);
        assert_eq!(back.globals[0].align, Some(64));

        // A pre-v26 blob has no align presence byte at all; the reader must
        // default the field to `None` rather than consume the next record's
        // first byte as a presence tag. Forge one from the minimal module's
        // base-version bytes by removing every field v25 does not have: the
        // align presence byte, and the two v30 trailing table counts
        // (universes, predicates). Nothing else in an otherwise empty module
        // is gated above v25, and nothing past v30 is written below v41.
        let legacy = single_global_module("global_align_binary", None);
        let mut v25 = serialize_module(&legacy).expect("serialize_module: test fixture");
        let header = u32::from_le_bytes(v25[MAGIC.len()..MAGIC.len() + 4].try_into().unwrap());
        assert_eq!(
            header, BASE_FORMAT_VERSION,
            "a minimal module is written at the base version"
        );
        assert!(
            (30..CONTRACT_SURFACE_FORMAT_VERSION).contains(&header),
            "the forge below strips exactly the v26..v40 fields of this module"
        );
        let align_tag = minimal_global_align_tag_offset(&v25);
        assert_eq!(v25[align_tag], 0, "None uses the zero presence tag");
        v25.remove(align_tag);
        assert_eq!(
            v25[v25.len() - 2..],
            [0, 0],
            "empty universe and predicate tables end the blob"
        );
        v25.truncate(v25.len() - 2);
        v25[MAGIC.len()..MAGIC.len() + 4].copy_from_slice(&25u32.to_le_bytes());

        let decoded = deserialize_module(&v25).expect("v25 global remains readable");
        assert_eq!(decoded.globals[0].align, None);
        assert_eq!(decoded, legacy);
    }

    #[test]
    fn malformed_global_alignment_presence_tag_is_rejected() {
        let module = single_global_module("bad_global_align_tag", None);
        let mut bytes = serialize_module(&module).expect("serialize_module: test fixture");
        let align_tag = minimal_global_align_tag_offset(&bytes);
        assert_eq!(bytes[align_tag], 0, "None uses the zero presence tag");
        bytes[align_tag] = 2;
        assert_eq!(deserialize_module(&bytes), Err(BinaryError::InvalidTag(2)));
    }

    #[test]
    fn version_2_blob_rejected_below_read_floor() {
        let mut bytes = Vec::new();
        let pool = sealed_pool(|p| collect_type_strings(&Ty::I64, p));
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
        write_ty(&mut bytes, &pool, &Ty::I64);
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
            section: None,
            visibility: crate::Visibility::Default,
            retained: false,
        });
        module.globals.push(Global {
            name: "H".to_string(),
            ty: Ty::U128,
            mutable: false,
            initializer: Some(Constant::U128(i128::MAX as u128 + 1)),
            linkage: Linkage::External,
            tls: None,
            align: None,
            section: None,
            visibility: crate::Visibility::Default,
            retained: false,
        });
        let bytes = serialize_module(&module).expect("serialize_module: test fixture");
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
        let tid = module
            .add_type(Ty::U8)
            .expect("Module::add_type: test fixture");
        module.globals.push(Global {
            name: "RAW".to_string(),
            ty: Ty::Array(tid, 3),
            mutable: false,
            initializer: Some(Constant::bytes(vec![0u8, 255, 16])),
            linkage: Linkage::External,
            tls: None,
            align: None,
            section: None,
            visibility: crate::Visibility::Default,
            retained: false,
        });
        module.globals.push(Global {
            name: "STR".to_string(),
            ty: Ty::Array(tid, 2),
            mutable: false,
            initializer: Some(Constant::str_bytes("hi")),
            linkage: Linkage::External,
            tls: None,
            align: None,
            section: None,
            visibility: crate::Visibility::Default,
            retained: false,
        });
        let bytes = serialize_module(&module).expect("serialize_module: test fixture");
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
            section: None,
            visibility: crate::Visibility::Default,
            retained: false,
        });
        let mut bytes = serialize_module(&module).expect("serialize_module: test fixture");
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
        ))
        .expect("serialize_module: test fixture");
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

        let ft = module
            .add_func_type(FuncTy {
                params: vec![Ty::I32, Ty::I32],
                returns: vec![Ty::I32],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");

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
            origin: None,
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
            origin: None,
        });

        module
            .add_type(Ty::I32)
            .expect("Module::add_type: test fixture");

        module.globals.push(Global {
            name: "COUNTER".to_string(),
            ty: Ty::I64,
            mutable: true,
            initializer: Some(Constant::Int(0)),
            linkage: Linkage::External,
            tls: None,
            align: None,
            section: None,
            visibility: crate::Visibility::Default,
            retained: false,
        });
        module.globals.push(Global {
            name: "UNINIT".to_string(),
            ty: Ty::I32,
            mutable: false,
            initializer: None,
            linkage: Linkage::External,
            tls: None,
            align: None,
            section: None,
            visibility: crate::Visibility::Default,
            retained: false,
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
        module
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");

        module.proof_obligations.push(ProofObligation {
            id: ProofId::new(0),
            kind: ObligationKind::PanicFreedom,
            status: ProofStatus::Discharged,
            description: "add does not overflow".to_string(),
            formula: Some(ProofFormula::smtlib2("(bvadd_no_overflow a b)", "Bool")),
            function: None,
            source: None,
            site: None,
            spec: None,
        });

        module.proof_certificates.push(ProofCertificate {
            obligation: ProofId::new(0),
            prover: "ay".to_string(),
            evidence: ProofEvidence::SmtProof(vec![0xDE, 0xAD]),
            assurance: None,
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

        let encoded = serialize_module(&module).expect("serialize_module: test fixture");
        assert_eq!(&encoded[8..12], &BASE_FORMAT_VERSION.to_le_bytes());
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

        let encoded = serialize_module(&module).expect("serialize_module: test fixture");
        assert_eq!(&encoded[8..12], &BASE_FORMAT_VERSION.to_le_bytes());
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

        let mut encoded = serialize_module(&module).expect("serialize_module: test fixture");
        encoded[8..12].copy_from_slice(&36u32.to_le_bytes());
        assert_eq!(
            deserialize_module(&encoded).expect_err("v36 must not decode the v37 encoding tag"),
            BinaryError::InvalidTag(2)
        );
    }

    #[test]
    fn v30_enum_record_defaults_v31_fields_without_desynchronizing() {
        let pool = sealed_pool(|p| {
            p.intern("Legacy");
            p.intern("Value");
            collect_type_strings(&Ty::I32, p);
        });
        let mut bytes = Vec::new();
        write_enum_id(&mut bytes, EnumId::new(0));
        write_str(&mut bytes, &pool, "Legacy");
        write_v32(&mut bytes, 1);
        write_str(&mut bytes, &pool, "Value");
        write_v32(&mut bytes, 1);
        write_ty(&mut bytes, &pool, &Ty::I32);
        write_v32(&mut bytes, 0); // implicit discriminants
        write_u8(&mut bytes, 0); // no repr; v30 record ends here

        let mut reader = Reader::new(&bytes);
        reader.version = 30;
        reader.pool = Some(pool.into_reader_strings());
        let decoded: EnumDef = read_enum_def(&mut reader).expect("v30 enum record");
        assert!(decoded.variants[0].field_names.is_empty());
        assert_eq!(decoded.layout, None);
        assert_eq!(reader.cursor.position() as usize, bytes.len());
    }

    // --- fast-2: function/parameter attributes (v7) ---

    #[test]
    fn func_attrs_round_trips() {
        let mut module = Module::new("attrs");
        let ft = module
            .add_func_type(FuncTy {
                params: vec![Ty::Ptr, Ty::I32],
                returns: vec![Ty::I32],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
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
                ext: crate::ArgExt::None,
                pass: None,
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
        module
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");

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
        let ft = module
            .add_func_type(FuncTy {
                params: vec![],
                returns: vec![],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut func = Function::new(FuncId::new(0), "g", ft, b(0));
        let mut block = Block::new(b(0));
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        func.blocks.push(block);
        module
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");

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

        let bytes = serialize_module(&module).expect("serialize_module: test fixture");
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

    fn container_vtable_module() -> Module {
        let fat = Ty::FatPtr(FatPtrKind::ContainerVtable);
        let mut module = Module::new("container_vtable_v40");
        let ft = module
            .add_func_type(FuncTy {
                params: vec![fat.clone()],
                returns: vec![fat.clone()],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut func = Function::new(FuncId::new(0), "id_dyn_tail", ft, b(0));
        let mut block = Block::new(b(0));
        block.params.push((v(0), fat.clone()));
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![v(0)] }));
        func.blocks.push(block);
        module
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");
        module
    }

    fn header_version(bytes: &[u8]) -> u32 {
        u32::from_le_bytes(bytes[8..12].try_into().unwrap())
    }

    #[test]
    fn container_vtable_fat_pointer_is_v40_gated() {
        // v40: the dyn-tail container pointer round-trips at the current
        // version, and the SAME bytes relabelled v39 are refused at the tag.
        // Tag 4 did not exist in v39 (v39 is nominal dialect types only);
        // lowering the header must not let a malformed pre-v40 blob smuggle
        // the new kind through an older schema identity (the v36/v37
        // discipline, applied to a fat-pointer sub-tag).
        let fat = Ty::FatPtr(FatPtrKind::ContainerVtable);
        let module = container_vtable_module();

        let bytes = serialize_module(&module).expect("serialize_module: test fixture");
        assert_eq!(
            header_version(&bytes),
            CONTAINER_VTABLE_FORMAT_VERSION,
            "a module whose only post-v38 feature is a ContainerVtable selects v40"
        );
        assert_eq!(header_version(&bytes), 40);
        let back = round_trip(&module);
        assert_eq!(back.func_types[0].params, vec![fat.clone()]);
        assert_eq!(back.functions[0].blocks[0].params[0].1, fat);

        let mut forged_v39 = bytes.clone();
        forged_v39[8..12].copy_from_slice(&39_u32.to_le_bytes());
        assert_eq!(
            deserialize_module(&forged_v39),
            Err(BinaryError::InvalidTag(4)),
            "a v39-labelled blob carrying fat-pointer-kind tag 4 must fail closed"
        );
        let mut forged_v38 = bytes;
        forged_v38[8..12].copy_from_slice(&38_u32.to_le_bytes());
        assert_eq!(
            deserialize_module(&forged_v38),
            Err(BinaryError::InvalidTag(4)),
            "a v38-labelled blob carrying fat-pointer-kind tag 4 must fail closed"
        );
    }

    /// Crystal lane (wave-DS): one function whose body drops the object behind its pointer
    /// parameter and returns.
    fn drop_module() -> Module {
        let mut module = Module::new("inst_drop");
        let ft = module
            .add_func_type(FuncTy {
                params: vec![Ty::Ptr],
                returns: vec![],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut func = Function::new(FuncId::new(0), "drop_it", ft, b(0));
        let mut block = Block::new(b(0));
        block.params.push((v(0), Ty::Ptr));
        block.body.push(InstrNode::new(Inst::Drop {
            ty: Ty::Tuple(vec![Ty::I32, Ty::Ptr]),
            ptr: v(0),
        }));
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        func.blocks.push(block);
        module
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");
        module
    }

    #[test]
    fn inst_drop_round_trips_at_its_version_and_is_gated_below_it() {
        // A module whose only post-v38 feature is a drop selects exactly
        // DROP_INST_FORMAT_VERSION, round-trips, and the SAME bytes relabelled
        // at any older readable version are refused at instruction tag 57 --
        // never silently promoted through an older schema identity.
        let module = drop_module();
        let bytes = serialize_module(&module).expect("serialize_module: test fixture");
        assert_eq!(header_version(&bytes), DROP_INST_FORMAT_VERSION);
        let back = round_trip(&module);
        assert!(matches!(
            &back.functions[0].blocks[0].body[0].inst,
            Inst::Drop { ty: Ty::Tuple(lanes), ptr } if lanes.len() == 2 && *ptr == v(0)
        ));
        for older in [DROP_INST_FORMAT_VERSION - 1, BASE_FORMAT_VERSION] {
            let mut forged = bytes.clone();
            forged[8..12].copy_from_slice(&older.to_le_bytes());
            assert_eq!(
                deserialize_module(&forged),
                Err(BinaryError::InvalidTag(57)),
                "a v{older}-labelled blob carrying instruction tag 57 must fail closed"
            );
        }
        // The SAME function without the drop keeps the base version: the
        // instruction raises only the module that contains it.
        let mut without = module;
        without.functions[0].blocks[0].body.remove(0);
        assert_eq!(
            header_version(&serialize_module(&without).expect("serialize_module: test fixture")),
            BASE_FORMAT_VERSION
        );
        // The explicit v38 projections refuse it by name.
        for body in [ModuleBinaryBody::RawV38, ModuleBinaryBody::CanonicalV38] {
            let options = ModuleBinaryOptions {
                body,
                ..Default::default()
            };
            assert_eq!(
                ProjectedModuleBinaryPlan::try_new(&drop_module(), options).err(),
                Some(BinaryProjectionError::DropInstRequiresV47)
            );
        }
    }

    /// v51: one function whose body carries exactly `inst` over block
    /// parameters `%0..%3` (the reader does not type-check, so the operand
    /// types are placeholders), then returns.
    fn inst_wire_batch_module(inst: Inst) -> Module {
        let mut module = Module::new("inst_wire_batch");
        let ft = module
            .add_func_type(FuncTy {
                params: vec![Ty::Ptr, Ty::Ptr, Ty::U64, Ty::U8],
                returns: vec![],
                is_vararg: false,
                abi: None,
            })
            .expect("Module::add_func_type: test fixture");
        let mut func = Function::new(FuncId::new(0), "carrier", ft, b(0));
        let mut block = Block::new(b(0));
        block.params.push((v(0), Ty::Ptr));
        block.params.push((v(1), Ty::Ptr));
        block.params.push((v(2), Ty::U64));
        block.params.push((v(3), Ty::U8));
        block.body.push(InstrNode::new(inst));
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        func.blocks.push(block);
        module
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");
        module
    }

    /// Every member of the INST wire batch, each with the tag byte an older
    /// reader must refuse (the Inst tag, or the sub-op tag inside the
    /// unchanged `BinOp` / `UnOp` payload).
    fn inst_wire_batch_members() -> Vec<(Inst, u8)> {
        let mut members = vec![
            (
                Inst::MakeAggregate {
                    ty: Ty::Tuple(vec![Ty::U64, Ty::U8]),
                    variant: None,
                    fields: vec![v(2), v(3)],
                },
                60,
            ),
            (
                Inst::MakeAggregate {
                    ty: Ty::Enum(crate::value::EnumId::new(0)),
                    variant: Some(1),
                    fields: vec![v(3)],
                },
                60,
            ),
            (
                Inst::MemCopy {
                    dst: v(0),
                    src: v(1),
                    bytes: v(2),
                    overlap: false,
                },
                61,
            ),
            (
                Inst::MemCopy {
                    dst: v(0),
                    src: v(1),
                    bytes: v(2),
                    overlap: true,
                },
                61,
            ),
            (
                Inst::MemSet {
                    dst: v(0),
                    byte: v(3),
                    bytes: v(2),
                },
                62,
            ),
        ];
        for (op, tag) in [(BinOp::RotL, 23), (BinOp::RotR, 24), (BinOp::FCopySign, 25)] {
            members.push((
                Inst::BinOp {
                    op,
                    ty: Ty::U64,
                    lhs: v(2),
                    rhs: v(2),
                },
                tag,
            ));
        }
        for (op, tag) in [
            (UnOp::CtLz, 9),
            (UnOp::CtTz, 10),
            (UnOp::BSwap, 11),
            (UnOp::BitReverse, 12),
        ] {
            members.push((
                Inst::UnOp {
                    op,
                    ty: Ty::U64,
                    operand: v(2),
                },
                tag,
            ));
        }
        members
    }

    #[test]
    fn inst_wire_batch_tags_are_read_gated() {
        // Each member alone selects exactly INST_WIRE_BATCH_FORMAT_VERSION
        // (the collector's predicate covers it), round-trips losslessly, has
        // a stable digest (the infallible writer no longer panics), and the
        // SAME bytes relabelled at any older readable version are refused at
        // the member's tag byte — never decoded through an older schema.
        for (inst, tag) in inst_wire_batch_members() {
            assert!(carries_inst_wire_batch_member(&inst), "{inst:?}");
            assert_eq!(inst.binary_wire_gap(), None, "{inst:?} has a wire tag");
            let module = inst_wire_batch_module(inst.clone());
            let bytes = serialize_module(&module).expect("serialize_module: test fixture");
            assert_eq!(
                header_version(&bytes),
                INST_WIRE_BATCH_FORMAT_VERSION,
                "{inst:?} raises the header to the batch version"
            );
            let back = round_trip(&module);
            assert_eq!(back.functions[0].blocks[0].body[0].inst, inst);
            assert_eq!(back.stable_digest(), module.stable_digest());
            for older in [INST_WIRE_BATCH_FORMAT_VERSION - 1, BASE_FORMAT_VERSION] {
                let mut forged = bytes.clone();
                forged[8..12].copy_from_slice(&older.to_le_bytes());
                assert_eq!(
                    deserialize_module(&forged),
                    Err(BinaryError::InvalidTag(tag)),
                    "a v{older}-labelled blob carrying {inst:?} (tag {tag}) must fail closed"
                );
            }
            // The explicit v38 projections refuse it by name.
            for body in [ModuleBinaryBody::RawV38, ModuleBinaryBody::CanonicalV38] {
                let options = ModuleBinaryOptions {
                    body,
                    ..Default::default()
                };
                assert_eq!(
                    ProjectedModuleBinaryPlan::try_new(&module, options).err(),
                    Some(BinaryProjectionError::InstWireBatchRequiresV51),
                    "{inst:?}"
                );
            }
        }
        // The SAME function without a batch member keeps the base version:
        // the batch raises only the module that contains one.
        let mut without = inst_wire_batch_module(Inst::BinOp {
            op: BinOp::Add,
            ty: Ty::U64,
            lhs: v(2),
            rhs: v(2),
        });
        assert_eq!(
            header_version(&serialize_module(&without).expect("serialize_module: test fixture")),
            BASE_FORMAT_VERSION
        );
        without.functions[0].blocks[0].body.remove(0);
        assert_eq!(
            header_version(&serialize_module(&without).expect("serialize_module: test fixture")),
            BASE_FORMAT_VERSION
        );
    }

    #[test]
    fn a_memcopy_overlap_byte_and_a_variant_presence_byte_are_closed() {
        // The two one-byte fields the batch added take 0 or 1 only; anything
        // else is `InvalidTag`, never a truthy byte. Each byte is located
        // differentially — two encodings that differ only in that field.
        let memcopy = |overlap| {
            serialize_module(&inst_wire_batch_module(Inst::MemCopy {
                dst: v(0),
                src: v(1),
                bytes: v(2),
                overlap,
            }))
            .expect("serialize_module: test fixture")
        };
        let make = |variant| {
            serialize_module(&inst_wire_batch_module(Inst::MakeAggregate {
                ty: Ty::Enum(crate::value::EnumId::new(0)),
                variant,
                fields: vec![v(3)],
            }))
            .expect("serialize_module: test fixture")
        };
        for (off, on, what) in [
            (memcopy(false), memcopy(true), "overlap"),
            (make(None), make(Some(0)), "variant presence"),
        ] {
            let at = off
                .iter()
                .zip(&on)
                .position(|(a, b)| a != b)
                .expect("the two encodings differ");
            assert_eq!((off[at], on[at]), (0, 1), "{what} is a 0/1 byte");
            let mut forged = on.clone();
            forged[at] = 2;
            assert_eq!(
                deserialize_module(&forged),
                Err(BinaryError::InvalidTag(2)),
                "a {what} byte of 2 must be refused"
            );
        }
    }

    fn handle_module() -> Module {
        let handle = Ty::handle("Nat", "trust_bignum::Nat");
        let mut module = Module::new("handle_v43");
        let ft = module
            .add_func_type(FuncTy {
                params: vec![handle.clone()],
                returns: vec![handle.clone()],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut func = Function::new(FuncId::new(0), "id_handle", ft, b(0));
        let mut block = Block::new(b(0));
        block.params.push((v(0), handle));
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![v(0)] }));
        func.blocks.push(block);
        module
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");
        module
    }

    #[test]
    fn handle_type_is_v43_gated_and_heads_the_projection_refusal_chain() {
        // v43: a module whose only post-v38 feature is a handle selects 43;
        // the SAME bytes relabelled v42 are refused at the type tag, because
        // tag 38 did not exist in v42 and lowering the header must not let a
        // blob smuggle the new type through an older schema identity.
        let handle = Ty::handle("Nat", "trust_bignum::Nat");
        let module = handle_module();
        let bytes = serialize_module(&module).expect("serialize_module: test fixture");
        assert_eq!(header_version(&bytes), HANDLE_TYPE_FORMAT_VERSION);
        assert_eq!(header_version(&bytes), 43);
        let back = round_trip(&module);
        assert_eq!(back.func_types[0].params, vec![handle.clone()]);
        assert_eq!(back.functions[0].blocks[0].params[0].1, handle);

        for older in [42_u32, 41, 40, 39, 38] {
            let mut forged = bytes.clone();
            forged[8..12].copy_from_slice(&older.to_le_bytes());
            assert_eq!(
                deserialize_module(&forged),
                Err(BinaryError::InvalidTag(38)),
                "a v{older}-labelled blob carrying type tag 38 must fail closed"
            );
        }

        // The projection refusal names the HIGHEST requirement: a module with
        // a handle AND a ContainerVtable AND a dialect type is refused for the
        // handle, never for the lower feature.
        let mut everything = container_vtable_module();
        let nominal = Ty::Dialect(Box::new(crate::DialectTy::new("example", "value", 1)));
        everything.types.push(nominal);
        everything.types.push(handle);
        for body in [ModuleBinaryBody::RawV38, ModuleBinaryBody::CanonicalV38] {
            let options = ModuleBinaryOptions {
                body,
                ..Default::default()
            };
            assert_eq!(
                ProjectedModuleBinaryPlan::try_new(&module, options).err(),
                Some(BinaryProjectionError::HandleTypeRequiresV43)
            );
            assert_eq!(
                ProjectedModuleBinaryPlan::try_new(&everything, options).err(),
                Some(BinaryProjectionError::HandleTypeRequiresV43)
            );
        }
        assert_eq!(
            header_version(&serialize_module(&everything).expect("serialize_module: test fixture")),
            43
        );
    }

    #[test]
    fn a_handle_and_a_declared_tuple_layout_coexist_at_v43() {
        // The v42/v43 collision resolution: the tuple table (v42, pushed and
        // goldened) and the handle type (v43) are independent features of the
        // same module, and the header is the HIGHEST requirement, not the last
        // one the string collector happened to see. `Ty::Handle` is a row of
        // the TYPE table, which every version writes ahead of both the v41
        // imports section and the v42 tuple table, so nothing is reordered:
        // the round trip must recover both.
        let handle = Ty::handle("Nat", "trust_bignum::Nat");
        let mut module = handle_module();
        module.target_info = Some(TargetInfo {
            triple: "x86_64-unknown-linux-gnu".into(),
            pointer_size: 8,
            endianness: Endianness::Little,
            abi: None,
            struct_passing: StructPassingPolicy::default(),
        });
        // The handle also occupies a TYPE-TABLE row, so the two features are
        // carried by two different sections of the same module.
        module.types.push(handle.clone());
        let tuple = Ty::Tuple(vec![Ty::U8, Ty::U64, Ty::U8]);
        let tuple_type = module
            .add_type(tuple.clone())
            .expect("Module::add_type: test fixture");
        module.tuple_layouts.push(crate::TupleLayoutDescriptor {
            tuple_type,
            size: 24,
            align: 8,
            field_offsets: vec![0, 8, 16],
        });
        module
            .validate_tuple_layouts()
            .expect("the descriptor must be coherent, or the test proves nothing");

        let bytes = serialize_module(&module).expect("serialize_module: test fixture");
        assert_eq!(header_version(&bytes), HANDLE_TYPE_FORMAT_VERSION);
        assert_eq!(header_version(&bytes), 43);

        let back = deserialize_module(&bytes).expect("v43 handle + v42 tuple table round trips");
        assert_eq!(back, module);
        assert_eq!(back.tuple_layouts, module.tuple_layouts);
        assert_eq!(back.types[tuple_type.as_usize()], tuple);
        assert!(
            back.types.contains(&handle),
            "the handle row survived the tuple table"
        );
        assert_eq!(
            serialize_module(&back).expect("serialize_module: test fixture"),
            bytes,
            "and the bytes are stable"
        );

        // A tuple table alone still selects 42 — the handle is what raises it.
        let mut tuple_only = module.clone();
        tuple_only.types.retain(|ty| !matches!(ty, Ty::Handle(_)));
        tuple_only.func_types.clear();
        tuple_only.functions.clear();
        tuple_only.tuple_layouts[0].tuple_type = TyId::new(0);
        tuple_only
            .validate_tuple_layouts()
            .expect("still coherent after dropping the handle row");
        assert_eq!(
            header_version(&serialize_module(&tuple_only).expect("serialize_module: test fixture")),
            TUPLE_LAYOUT_FORMAT_VERSION
        );
    }

    #[test]
    fn writer_selects_the_minimum_lossless_version_per_module() {
        // The header is the minimum version that can carry the module:
        // 38 for a legacy module, 39 with a nominal dialect type, 40 with a
        // ContainerVtable — and the max of the two when both occur.
        let legacy = {
            let mut module = Module::new("legacy_v38");
            let ft = module
                .add_func_type(FuncTy {
                    params: vec![Ty::I32],
                    returns: vec![Ty::I32],
                    abi: None,
                    is_vararg: false,
                })
                .expect("Module::add_func_type: test fixture");
            let mut func = Function::new(FuncId::new(0), "id", ft, b(0));
            let mut block = Block::new(b(0));
            block.params.push((v(0), Ty::I32));
            block
                .body
                .push(InstrNode::new(Inst::Return { values: vec![v(0)] }));
            func.blocks.push(block);
            module
                .try_add_function(func)
                .expect("Module::try_add_function: test fixture");
            module
        };
        assert_eq!(
            header_version(&serialize_module(&legacy).expect("serialize_module: test fixture")),
            BASE_FORMAT_VERSION
        );
        assert_eq!(
            header_version(&serialize_module(&legacy).expect("serialize_module: test fixture")),
            38
        );

        let nominal = Ty::Dialect(Box::new(crate::DialectTy::new("example", "value", 1)));
        let dialect_only = {
            let mut module = Module::new("dialect_v39");
            let ft = module
                .add_func_type(FuncTy {
                    params: vec![nominal.clone()],
                    returns: vec![nominal.clone()],
                    abi: None,
                    is_vararg: false,
                })
                .expect("Module::add_func_type: test fixture");
            let mut func = Function::new(FuncId::new(0), "id", ft, b(0));
            let mut block = Block::new(b(0));
            block.params.push((v(0), nominal.clone()));
            block
                .body
                .push(InstrNode::new(Inst::Return { values: vec![v(0)] }));
            func.blocks.push(block);
            module
                .try_add_function(func)
                .expect("Module::try_add_function: test fixture");
            module
        };
        assert_eq!(
            header_version(
                &serialize_module(&dialect_only).expect("serialize_module: test fixture")
            ),
            DIALECT_TYPE_FORMAT_VERSION
        );
        assert_eq!(
            header_version(
                &serialize_module(&dialect_only).expect("serialize_module: test fixture")
            ),
            39
        );

        let both = {
            let mut module = container_vtable_module();
            let ft = module
                .add_func_type(FuncTy {
                    params: vec![nominal.clone()],
                    returns: vec![nominal.clone()],
                    abi: None,
                    is_vararg: false,
                })
                .expect("Module::add_func_type: test fixture");
            let mut func = Function::new(FuncId::new(1), "id_nominal", ft, b(0));
            let mut block = Block::new(b(0));
            block.params.push((v(0), nominal.clone()));
            block
                .body
                .push(InstrNode::new(Inst::Return { values: vec![v(0)] }));
            func.blocks.push(block);
            module
                .try_add_function(func)
                .expect("Module::try_add_function: test fixture");
            module
        };
        let bytes = serialize_module(&both).expect("serialize_module: test fixture");
        assert_eq!(header_version(&bytes), CONTAINER_VTABLE_FORMAT_VERSION);
        let back =
            deserialize_module(&bytes).expect("dialect + ContainerVtable round-trips at v40");
        assert_eq!(back.func_types[1].params, vec![nominal.clone()]);
        assert_eq!(
            back.func_types[0].params,
            vec![Ty::FatPtr(FatPtrKind::ContainerVtable)]
        );

        // Explicit v38 projections refuse both, naming the highest requirement.
        for body in [ModuleBinaryBody::RawV38, ModuleBinaryBody::CanonicalV38] {
            let options = ModuleBinaryOptions {
                body,
                ..Default::default()
            };
            assert_eq!(
                ProjectedModuleBinaryPlan::try_new(&container_vtable_module(), options).err(),
                Some(BinaryProjectionError::ContainerVtableRequiresV40)
            );
            assert_eq!(
                ProjectedModuleBinaryPlan::try_new(&both, options).err(),
                Some(BinaryProjectionError::ContainerVtableRequiresV40)
            );
            assert_eq!(
                ProjectedModuleBinaryPlan::try_new(&dialect_only, options).err(),
                Some(BinaryProjectionError::DialectTypeRequiresV39)
            );
            assert!(ProjectedModuleBinaryPlan::try_new(&legacy, options).is_ok());
        }
    }

    // --- fast-3 D.2: GEP.inbounds (v8) ---

    #[test]
    fn gep_inbounds_round_trips() {
        let mut module = Module::new("gep_ib");
        let ft = module
            .add_func_type(FuncTy {
                params: vec![Ty::Ptr],
                returns: vec![Ty::Ptr],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
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
        module
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");

        let back = round_trip(&module);
        assert!(
            matches!(
                back.functions[0].blocks[0].body[0].inst,
                Inst::GEP { inbounds: true, .. }
            ),
            "GEP.inbounds=true must round-trip"
        );
        let bytes = serialize_module(&module).expect("serialize_module: test fixture");
        assert_eq!(
            u32::from_le_bytes([bytes[8], bytes[9], bytes[10], bytes[11]]),
            BASE_FORMAT_VERSION
        );
    }

    // --- Clean RC heap: AllocOrigin::CleanHeap (origin byte 3, v22) ---

    #[test]
    fn clean_heap_origin_round_trips() {
        let mut module = Module::new("clean_heap_bin");
        let ft = module
            .add_func_type(FuncTy {
                params: vec![],
                returns: vec![Ty::Ptr],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
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
        module
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");

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
        let bytes = serialize_module(&module).expect("serialize_module: test fixture");
        assert_eq!(
            u32::from_le_bytes([bytes[8], bytes[9], bytes[10], bytes[11]]),
            BASE_FORMAT_VERSION,
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
        let ft = module
            .add_func_type(FuncTy {
                params: vec![Ty::Ptr],
                returns: vec![Ty::I64],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
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
        module
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");

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
        let bytes = serialize_module(&module).expect("serialize_module: test fixture");
        assert_eq!(
            u32::from_le_bytes([bytes[8], bytes[9], bytes[10], bytes[11]]),
            BASE_FORMAT_VERSION,
            "VERSION must be bumped for the CoroSuspend opcode"
        );
    }

    // --- exceptions: Inst::Invoke / LandingPad / Resume (tags 51..=53, v17) ---

    #[test]
    fn eh_opcodes_round_trip() {
        let mut module = Module::new("eh_bin");
        // callee: () -> i32 (may throw); caller: () -> i32 that invokes it.
        let callee_ft = module
            .add_func_type(FuncTy {
                params: vec![],
                returns: vec![Ty::I32],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let caller_ft = module
            .add_func_type(FuncTy {
                params: vec![],
                returns: vec![Ty::I32],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let callee = Function::new(FuncId::new(0), "may_throw", callee_ft, b(0));
        module
            .try_add_function(callee)
            .expect("Module::try_add_function: test fixture");

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
        module
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");

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
        let bytes = serialize_module(&module).expect("serialize_module: test fixture");
        assert_eq!(
            u32::from_le_bytes([bytes[8], bytes[9], bytes[10], bytes[11]]),
            BASE_FORMAT_VERSION,
            "VERSION must be bumped for the EH opcodes"
        );
    }

    #[test]
    fn gep_default_inbounds_false_round_trips() {
        let mut module = Module::new("gep_default");
        let ft = module
            .add_func_type(FuncTy {
                params: vec![Ty::Ptr],
                returns: vec![Ty::Ptr],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
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
        module
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");
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
        let ft = module
            .add_func_type(FuncTy {
                params: vec![Ty::I32],
                returns: vec![Ty::I32],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut func = Function::new(FuncId::new(0), "id", ft, b(0));
        let mut block = Block::new(b(0));
        block.params.push((v(0), Ty::I32));
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![v(0)] }));
        func.blocks.push(block);
        module
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");

        let binary = serialize_module(&module).expect("serialize_module: test fixture");
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
        let ft = module
            .add_func_type(FuncTy {
                params: vec![],
                returns: vec![],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
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
                weak: false,
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
            InstrNode::new(Inst::Assert {
                cond: v(0),
                kind: crate::inst::AssertKind::Unspecified,
                site: None,
            }),
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

        module
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");
        round_trip(&module);
    }

    // --- All proof annotation variants ---

    #[test]
    fn all_proof_annotation_variants_round_trip() {
        let mut module = Module::new("proofs");
        let ft = module
            .add_func_type(FuncTy {
                params: vec![],
                returns: vec![],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
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
        module
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");
        round_trip(&module);
    }

    #[test]
    fn fresh_symbolic_havoc_has_stable_public_wire_tag() {
        // This is a semantic marker, not an unforgeable capability. Lock both
        // sides of its public wire representation so consumers cannot silently
        // reinterpret an old artifact after an enum/tag edit.
        let mut bytes = Vec::new();
        let pool = sealed_pool(|_| {});
        write_proof_annotation(&mut bytes, &pool, &ProofAnnotation::FreshSymbolicHavoc);
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
            spec: None,
        });
        module.proof_certificates.push(ProofCertificate {
            obligation: ProofId::new(0),
            prover: "ay".to_string(),
            evidence: ProofEvidence::SmtProof(vec![0xDE, 0xAD, 0xBE, 0xEF]),
            assurance: None,
        });
        module.proof_certificates.push(ProofCertificate {
            obligation: ProofId::new(0),
            prover: "lean4".to_string(),
            evidence: ProofEvidence::LeanProof("theorem foo : True := trivial".to_string()),
            assurance: None,
        });
        module.proof_certificates.push(ProofCertificate {
            obligation: ProofId::new(0),
            prover: "kani".to_string(),
            evidence: ProofEvidence::KaniHarness("check_bounds".to_string()),
            assurance: None,
        });
        module.proof_certificates.push(ProofCertificate {
            obligation: ProofId::new(0),
            prover: "gamma-crown".to_string(),
            evidence: ProofEvidence::GammaCrownBound {
                epsilon: 0.001,
                verified_layers: 12,
            },
            assurance: None,
        });
        module.proof_certificates.push(ProofCertificate {
            obligation: ProofId::new(0),
            prover: "tv".to_string(),
            evidence: ProofEvidence::TranslationValidation {
                rule_name: "inline_expansion".to_string(),
                smt_hash: [0xAB; 32],
            },
            assurance: None,
        });
        module.proof_certificates.push(ProofCertificate {
            obligation: ProofId::new(0),
            prover: "manual".to_string(),
            evidence: ProofEvidence::Trusted("manual audit 2026-04-16".to_string()),
            assurance: None,
        });
        module.proof_certificates.push(ProofCertificate {
            obligation: ProofId::new(0),
            prover: "compose".to_string(),
            evidence: ProofEvidence::InheritedFromCallee {
                callee: FuncId::new(7),
                obligation: ProofId::new(3),
                external: None,
            },
            assurance: None,
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
                spec: None,
            });
        }
        round_trip(&module);
    }

    // --- Complex module with multiple functions ---

    #[test]
    fn multi_function_module_round_trip() {
        let mut module = Module::new("multi_func");

        let ft_add = module
            .add_func_type(FuncTy {
                params: vec![Ty::I32, Ty::I32],
                returns: vec![Ty::I32],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let ft_main = module
            .add_func_type(FuncTy {
                params: vec![],
                returns: vec![Ty::I32],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let ft_vararg = module
            .add_func_type(FuncTy {
                params: vec![Ty::Ptr],
                returns: vec![Ty::I32],
                abi: None,
                is_vararg: true,
            })
            .expect("Module::add_func_type: test fixture");

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
            origin: None,
        });

        module
            .add_type(Ty::I32)
            .expect("Module::add_type: test fixture");
        module
            .add_type(Ty::Array(TyId::new(0), 10))
            .expect("Module::add_type: test fixture");

        module.globals.push(Global {
            name: "FLAG".to_string(),
            ty: Ty::Bool,
            mutable: true,
            initializer: Some(Constant::Bool(false)),
            linkage: Linkage::External,
            tls: None,
            align: None,
            section: None,
            visibility: crate::Visibility::Default,
            retained: false,
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
        module
            .try_add_function(f_add)
            .expect("Module::try_add_function: test fixture");

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
        module
            .try_add_function(f_main)
            .expect("Module::try_add_function: test fixture");

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
        module
            .try_add_function(f_va)
            .expect("Module::try_add_function: test fixture");

        round_trip(&module);
    }

    // --- InstrNode metadata ---

    #[test]
    fn instr_node_with_full_metadata_round_trip() {
        let mut module = Module::new("metadata");
        let ft = module
            .add_func_type(FuncTy {
                params: vec![],
                returns: vec![],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
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
        module
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");
        round_trip(&module);
    }

    #[test]
    fn semantic_source_provenance_v35_round_trip() {
        let mut module = Module::new("source_provenance");
        let ft = module
            .add_func_type(FuncTy {
                params: vec![Ty::U64],
                returns: vec![],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
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
        module
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");

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
        let ft = module
            .add_func_type(FuncTy {
                params: vec![],
                returns: vec![],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
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
        module
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");
        round_trip(&module);
    }

    // --- New aggregate / closure types (issue #30) ---

    #[test]
    fn set_type_round_trip_both_reprs() {
        let mut module = Module::new("set_types");
        module
            .add_type(Ty::Set(TyId::new(0), SetRepr::Bitset))
            .expect("Module::add_type: test fixture");
        module
            .add_type(Ty::Set(TyId::new(3), SetRepr::Boxed))
            .expect("Module::add_type: test fixture");
        round_trip(&module);
    }

    #[test]
    fn sequence_type_round_trip() {
        let mut module = Module::new("seq_types");
        module
            .add_type(Ty::Sequence(TyId::new(0)))
            .expect("Module::add_type: test fixture");
        module
            .add_type(Ty::Sequence(TyId::new(7)))
            .expect("Module::add_type: test fixture");
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
        module
            .add_type(Ty::Record(RecordId::new(0)))
            .expect("Module::add_type: test fixture");
        round_trip(&module);
    }

    #[test]
    fn closure_type_round_trip_with_captures() {
        let mut module = Module::new("closure_types");
        let ft = module
            .add_func_type(FuncTy {
                params: vec![Ty::I32],
                returns: vec![Ty::I32],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        module
            .add_closure_type(ClosureTy {
                func: ft,
                captures: vec![Ty::I32, Ty::Bool],
            })
            .expect("Module::add_closure_type: test fixture");
        module
            .add_type(Ty::Closure(ClosureTyId::new(0)))
            .expect("Module::add_type: test fixture");
        round_trip(&module);
    }

    #[test]
    fn closure_type_round_trip_empty_captures() {
        let mut module = Module::new("bare_closure");
        let ft = module
            .add_func_type(FuncTy {
                params: vec![],
                returns: vec![],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        module
            .add_closure_type(ClosureTy::bare(ft))
            .expect("Module::add_closure_type: test fixture");
        module
            .add_type(Ty::Closure(ClosureTyId::new(0)))
            .expect("Module::add_type: test fixture");
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
            section: None,
            visibility: crate::Visibility::Default,
            retained: false,
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
            section: None,
            visibility: crate::Visibility::Default,
            retained: false,
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
            section: None,
            visibility: crate::Visibility::Default,
            retained: false,
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
            section: None,
            visibility: crate::Visibility::Default,
            retained: false,
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
            section: None,
            visibility: crate::Visibility::Default,
            retained: false,
        });
        module.globals.push(Global {
            name: "EMPTY_SET".to_string(),
            ty: Ty::Set(TyId::new(0), SetRepr::Boxed),
            mutable: false,
            initializer: Some(Constant::Set(vec![])),
            linkage: Linkage::Internal,
            tls: None,
            align: None,
            section: None,
            visibility: crate::Visibility::Default,
            retained: false,
        });
        module.globals.push(Global {
            name: "EMPTY_REC".to_string(),
            ty: Ty::Record(RecordId::new(0)),
            mutable: false,
            initializer: Some(Constant::Record(vec![])),
            linkage: Linkage::Internal,
            tls: None,
            align: None,
            section: None,
            visibility: crate::Visibility::Default,
            retained: false,
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
            section: None,
            visibility: crate::Visibility::Default,
            retained: false,
        });
        round_trip(&module);
    }

    // --- NaN handling ---

    #[test]
    fn nan_round_trip() {
        let mut module = Module::new("nan");
        let ft = module
            .add_func_type(FuncTy {
                params: vec![],
                returns: vec![],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
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
        module
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");

        let bytes = serialize_module(&module).expect("serialize_module: test fixture");
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
        let ft = module
            .add_func_type(FuncTy {
                params: vec![Ty::Ptr, Ty::I64],
                returns: vec![Ty::Ptr],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
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
        module
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");

        round_trip(&module);
    }

    #[test]
    fn native_verification_bundle_round_trip() {
        use crate::request::*;
        let mut module = Module::new("bundle_test");
        let ft = module
            .add_func_type(FuncTy {
                params: vec![Ty::I32],
                returns: vec![Ty::I32],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut func = Function::new(FuncId::new(0), "f", ft, b(0));
        let mut block = Block::new(b(0));
        block.params.push((v(0), Ty::I32));
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![v(0)] }));
        func.blocks.push(block);
        module
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");

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
    fn native_verification_bundle_refuses_a_module_completeness_claim() {
        use crate::request::*;
        // WS5.3b: the module segment has no carrier for a completeness claim
        // yet. The fallible envelope must refuse by name, not panic inside
        // `serialize_module`, and not drop the claim.
        for claim in [
            crate::ModuleCompleteness::Complete,
            crate::ModuleCompleteness::Partial(vec![crate::UnloweredRow {
                symbol: "total".into(),
                display_path: None,
                reason: "unsupported shape".into(),
            }]),
        ] {
            let mut module = Module::new("claimed");
            module.completeness = Some(claim);
            let bundle = NativeVerificationBundle::new(
                NativeBundleProducer::TrustIr,
                NativeAdapterInput::TrustIrModule,
                crate::proof::ProofDigest::zero(),
                module,
                proof_lineage_manifest(),
            );
            match serialize_native_verification_bundle(&bundle) {
                Err(BinaryError::Unencodable(what)) => {
                    assert!(what.contains("Module.completeness"), "{what}");
                }
                other => panic!("expected a named Unencodable refusal, got {other:?}"),
            }
        }
        // Control: the same bundle with NO claim encodes and round-trips.
        let bundle = NativeVerificationBundle::new(
            NativeBundleProducer::TrustIr,
            NativeAdapterInput::TrustIrModule,
            crate::proof::ProofDigest::zero(),
            Module::new("claimed"),
            proof_lineage_manifest(),
        );
        let bytes = serialize_native_verification_bundle(&bundle).expect("serialize");
        let back = deserialize_native_verification_bundle(&bytes).expect("deserialize");
        assert_eq!(back.module.completeness, None);
        assert_eq!(back.module, bundle.module);
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
        let pool = sealed_pool(|p| collect_type_strings(ty, p));
        let mut buf = Vec::new();
        write_ty(&mut buf, &pool, ty);
        buf[0]
    }

    fn first_tag_constant(c: &Constant) -> u8 {
        let pool = sealed_pool(|p| collect_constant_strings(c, p));
        let mut buf = Vec::new();
        write_constant(&mut buf, &pool, c);
        buf[0]
    }

    fn first_tag_proof_evidence(ev: &ProofEvidence) -> u8 {
        let pool = sealed_pool_at(CONTRACT_SURFACE_FORMAT_VERSION, |p| {
            collect_evidence_strings(ev, p)
        });
        let mut buf = Vec::new();
        write_proof_evidence(&mut buf, &pool, ev);
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
                Ty::Dialect(_) => 37,
                // v43 nominal opaque runtime handle.
                Ty::Handle(_) => 38,
                Ty::Storage(_) => 40,
                // v67 tensor region.
                Ty::Tensor(_, _) => 41,
                Ty::Ext(e) => e.unreachable(),
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
            Ty::Dialect(Box::new(crate::DialectTy::new("example", "value", 1))),
            Ty::handle("Nat", "trust_bignum::Nat"),
            Ty::Storage(crate::StorageLayout::new(80, 8)),
            Ty::Tensor(Box::new(Ty::I32), 2),
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
                // Crystal lane E3b (v49): an unwritten struct/tuple lane.
                Constant::Uninit => 15,
                // v50: the constant-size uniform array.
                Constant::Splat { .. } => 16,
                // v70 (PKG-U13e): a tensor named by its blob digest. 17 is
                // the extension tag (`CONSTANT_EXT_TAG`).
                Constant::TensorBlob { .. } => 18,
                Constant::Ext(e) => e.unreachable(),
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
            Constant::Uninit,
            Constant::Splat {
                elem: Box::new(Constant::Int(0)),
                len: 1 << 40,
            },
            Constant::TensorBlob {
                digest: crate::blob::BlobDigest::of(&[1, 2, 3, 4]),
                dims: vec![2, 2],
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
                external: None,
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
        let pool = sealed_pool(|p| collect_evidence_strings(&ev, p));
        let mut buf = Vec::new();
        write_proof_evidence(&mut buf, &pool, &ev);
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
                binding: None,
            }),
        };
        // The recheck directive interns strings, so the reader must carry the
        // pool back, and read at the version the pool selected (both mirror
        // the full-module reader at the header): an unbound directive below
        // v61 carries no binding presence byte.
        let pool = sealed_pool(|p| collect_evidence_strings(&ev, p));
        let mut buf = Vec::new();
        write_proof_evidence(&mut buf, &pool, &ev);
        let mut reader = Reader::new(&buf);
        reader.version = pool.minimum_version();
        reader.pool = Some(pool.into_reader_strings());
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
            // v41 payload-free kinds (`Custom` carries strings; its tag 15 is
            // pinned by the v41 round-trip tests instead).
            (ObligationKind::Termination, 13),
            (ObligationKind::Ownership, 14),
        ];
        // `write_obligation_kind` takes the string pool (v41 `Custom` interns
        // its namespace and name), so it cannot use the 2-argument `tag` helper.
        let kind_tag = |kind: &ObligationKind| {
            let mut buf = Vec::new();
            let pool = sealed_pool(|p| collect_obligation_kind_strings(kind, p));
            write_obligation_kind(&mut buf, &pool, kind);
            assert_eq!(
                buf.len(),
                1,
                "payload-free kind must encode to a single byte"
            );
            buf[0]
        };
        for (op, want) in &obligations {
            assert_eq!(kind_tag(op), *want, "ObligationKind tag drifted: {op:?}");
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
            // v45 conventions (read-gated `version >= 45`, WS3.12).
            (CallingConv::CUnwind, 5),
            (CallingConv::SysV64, 6),
            (CallingConv::Win64, 7),
            (CallingConv::Aapcs, 8),
            (CallingConv::EfiApi, 9),
            (CallingConv::VectorCall, 10),
            (CallingConv::RustCold, 11),
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
            // v41 linkages (read-gated `version >= 41`).
            (Linkage::AvailableExternally, 5),
            (Linkage::ExternalWeak, 6),
            (Linkage::WeakOdr, 7),
            (Linkage::LinkOnceOdr, 8),
        ];
        for (op, want) in &linkages {
            assert_eq!(tag(write_linkage, op), *want, "Linkage tag drifted: {op:?}");
        }

        let visibilities = [
            (Visibility::Default, 0u8),
            (Visibility::Hidden, 1),
            (Visibility::Protected, 2),
        ];
        for (op, want) in &visibilities {
            assert_eq!(
                tag(write_visibility, op),
                *want,
                "Visibility tag drifted: {op:?}"
            );
        }
    }

    #[test]
    fn subtag_wire_tags_frozen() {
        // FatPtrKind sub-tags (nested under Ty::FatPtr, tag 30).
        let pool = sealed_pool(|_| {});
        for (kind, want) in [
            (FatPtrKind::Slice(TyId::new(0)), 0u8),
            (FatPtrKind::Str, 1),
            (FatPtrKind::TraitObject { trait_id: 0 }, 2),
            (FatPtrKind::ContainerLen, 3),
            (FatPtrKind::ContainerVtable, 4),
        ] {
            let mut buf = Vec::new();
            write_fat_ptr_kind(&mut buf, &pool, &kind);
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
    fn forge_v32(buf: &mut impl BinarySink, mut v: u64) {
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

    /// The public varint pair is the module reader's own rule, not a copy
    /// (r11 item 7: the KIND 4 byte fixtures read and write through it). It
    /// pins the rule the fixtures share: truncated, overwide and overlong
    /// spellings are refused, and the canonical spelling round-trips.
    #[test]
    fn decode_varint_refuses_truncated_and_overlong_input() {
        // Truncated: the reader's pre-read bound refuses the missing byte.
        let truncated = Err(BinaryError::TooLarge {
            declared: 1,
            remaining: 0,
        });
        assert_eq!(decode_varint(&[0x80]), truncated);
        assert_eq!(decode_varint(&[]), truncated);
        assert_eq!(decode_varint(&[0xFF; 11]), Err(BinaryError::VintOverflow));
        assert!(matches!(
            decode_varint(&[0x80, 0x00]),
            Err(BinaryError::InvalidData(message)) if message.contains("non-canonical")
        ));
        for value in [0, 1, 0x7F, 0x80, 300, u64::from(u32::MAX), u64::MAX] {
            let bytes = encode_varint(value);
            let mut written = Vec::new();
            write_v64(&mut written, value);
            assert_eq!(bytes, written, "encode_varint is the writer's rule");
            let mut trailing = bytes.clone();
            trailing.push(0xAA);
            assert_eq!(decode_varint(&trailing), Ok((value, bytes.len())));
        }
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

    /// Stack-backed fixed-width reads retain the same fail-before-read bound
    /// and advance the cursor by exactly the admitted width.
    #[test]
    fn fixed_width_reads_preserve_bounds_and_cursor_contract() {
        let mut r = Reader::new(&[1, 2, 3, 4]);
        assert_eq!(r.read_array::<2>().unwrap(), [1, 2]);
        assert_eq!(r.cursor.position(), 2);
        assert!(matches!(
            r.read_array::<3>(),
            Err(BinaryError::TooLarge {
                declared: 3,
                remaining: 2
            })
        ));
        assert_eq!(
            r.cursor.position(),
            2,
            "rejected read must not consume input"
        );
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
            read_ty::<NoExt>(&mut r),
            Err(BinaryError::InvalidData(reason))
                if reason.contains("nesting exceeds limit")
        ));
        assert_eq!(r.nesting_depth, 0, "failed decode must unwind its budget");
    }

    /// Roadmap WS4.4, NEW-1: a canonical projection streams the SAME bytes as
    /// the materialized canonical module when `ClausePlace::Value` bindings
    /// are present — the summary clauses and the scoped obligation bindings
    /// are written through the owning function's plan, exactly the rewrite
    /// `format::into_canonical` performs — and the executable-content identity
    /// (which carries summaries, not obligations) is invariant under
    /// canonicalization, as it is for every module without provenance.
    #[cfg(feature = "fmt")]
    #[test]
    fn canonical_projection_remaps_value_bindings_like_into_canonical() {
        use crate::proof::{
            ClauseBinding, ClausePlace, ClauseSort, ObligationKind, ObligationSite, ProofFormula,
            ProofObligation, ProofStatus,
        };
        let bound = |value: u32| {
            let mut formula = ProofFormula::smtlib2("(= r 1)", "Bool");
            formula.bindings = vec![(
                "r".into(),
                ClauseBinding {
                    sort: ClauseSort::BitVec(64),
                    place: ClausePlace::Value(v(value)),
                },
            )];
            formula
        };
        let mut module = Module::new("new1");
        let signature = module
            .add_func_type(FuncTy {
                abi: None,
                params: vec![Ty::I64],
                returns: vec![Ty::I64],
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut function = Function::new(FuncId::new(0), "f", signature, b(0));
        let mut block = Block::new(b(0));
        block.params.push((v(5), Ty::I64));
        block.body.push(
            InstrNode::new(Inst::Copy {
                ty: Ty::I64,
                operand: v(5),
            })
            .with_result(v(9)),
        );
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![v(9)] }));
        function.blocks.push(block);
        function.summary = Some(
            FunctionSummary::new()
                .with_params(vec!["x".into()])
                .ensuring(bound(9))
                .requiring(bound(3)),
        );
        module
            .try_add_function(function)
            .expect("Module::try_add_function: test fixture");
        module.proof_obligations.push(
            ProofObligation::new(
                ProofId::new(0),
                ObligationKind::Postcondition,
                ProofStatus::Pending,
                "scoped",
            )
            .with_function(FuncId::new(0))
            .with_formula(bound(9)),
        );
        module.proof_obligations.push(
            ProofObligation::new(
                ProofId::new(1),
                ObligationKind::MemorySafety,
                ProofStatus::Pending,
                "sited",
            )
            .with_site(ObligationSite::new(FuncId::new(0), b(0), 0))
            .with_formula(bound(5)),
        );
        module.proof_obligations.push(
            ProofObligation::new(
                ProofId::new(2),
                ObligationKind::MemorySafety,
                ProofStatus::Pending,
                "unscoped",
            )
            .with_formula(bound(9)),
        );
        let canon = crate::format::canonicalize(&module);
        assert_ne!(canon, module, "the fixture must need a rewrite");
        // The adaptive `Canonical` body: `CanonicalV38` refuses the v41
        // contract surface a binding is part of (`ContractSurfaceRequiresV41`).
        let mut projected = ProjectedModuleBinaryPlan::try_new(
            &module,
            ModuleBinaryOptions {
                body: ModuleBinaryBody::Canonical,
                ..ModuleBinaryOptions::default()
            },
        )
        .expect("canonical projection");
        let streamed = projected.to_vec().expect("to_vec: test fixture");
        assert_eq!(
            streamed,
            serialize_module(&canon).expect("serialize_module: test fixture"),
            "streamed canonical image == image of into_canonical"
        );
        // Mutation control: the canonical body with the bindings AS STORED
        // (the pre-WS4.4 rewrite) is a different image, so the equality above
        // is decided by the binding remap and nothing else.
        let mut skip_remap = canon.clone();
        skip_remap.functions[0].summary = module.functions[0].summary.clone();
        skip_remap.proof_obligations = module.proof_obligations.clone();
        assert_ne!(
            streamed,
            serialize_module(&skip_remap).expect("serialize_module: test fixture")
        );
        assert_eq!(
            module.executable_content_digest_v1(),
            canon.executable_content_digest_v1(),
            "executable identity is invariant under canonicalization"
        );
    }
}

/// The wire-version reservation ledger (roadmap WS8.5, DG-14).
///
/// `crates/trust-ir/wire_versions.tsv` is the one place a binary version
/// number is claimed. This module binds it to the compiled constants, to the
/// reader's actual accept/refuse behaviour, and — through a source scan of this
/// file — to every `*VERSION*` constant or static declared here (any type,
/// visibility or line layout) and to every literal version comparison in its
/// code, so a new version constant without a ledger row, a `VERSION` bump
/// without a `shipped` row, a shipped version no writer constant selects, a
/// read gate spelling an unreserved number, a ledger row that contradicts
/// the reader, or an `AMBIGUOUS_LINEAGE_VERSIONS` range that is not exactly the
/// `refused` rows each fail by name. It lives in-crate
/// because `DIALECT_TYPE_FORMAT_VERSION` and `MIN_READ_VERSION` are private.
#[cfg(all(test, feature = "binary"))]
mod wire_version_ledger {
    use super::*;

    /// The ledger file as it is on disk: what the LIVE test binds to the code.
    const LIVE_LEDGER: &str = include_str!("../wire_versions.tsv");

    /// The ledger every MUTATION fixture extends: the live file with its open
    /// (`reserved`) rows cut out, at compile time.
    ///
    /// The fixtures below append rows numbered from `VERSION + 1` (`NEXT`) to
    /// model the NEXT reservation. Against the live file that stopped meaning
    /// anything the moment somebody made a REAL one. Measured 2026-09-18: one
    /// by-the-book `45 reserved` row in wire_versions.tsv turned 5 of this
    /// module's 12 tests red (a duplicate v45; a "gap" that was no longer one; a
    /// read gate the real reservation now admitted). The protocol this ledger
    /// asks for could not be followed without breaking the gate that enforces
    /// it. Cutting the open rows out of the fixture BASELINE fixes the class
    /// rather than the instances: every fixture, present and future, extends a
    /// ledger that ends at the highest settled row, whatever is reserved on
    /// disk. (The fixtures derive every number from `VERSION` — `NEXT` and
    /// `AFTER_NEXT` below — so they move when it does, with no edit.)
    const LEDGER: &str = match core::str::from_utf8(&SETTLED) {
        Ok(text) => text,
        Err(_) => panic!("wire_versions.tsv is not UTF-8"),
    };
    const SETTLED_LEN: usize = settled_len(LIVE_LEDGER.as_bytes());
    const SETTLED: [u8; SETTLED_LEN] = settled_bytes(LIVE_LEDGER.as_bytes());

    /// Is the line `src[start..end]` a `reserved` row (its second TAB-separated
    /// column is exactly that word)? Comment lines never are.
    const fn is_reserved_row(src: &[u8], start: usize, end: usize) -> bool {
        const WORD: &[u8] = b"reserved";
        if start >= end || src[start] == b'#' {
            return false;
        }
        let mut tab = start;
        while tab < end && src[tab] != b'\t' {
            tab += 1;
        }
        let column = tab + 1;
        if column + WORD.len() >= end || src[column + WORD.len()] != b'\t' {
            return false;
        }
        let mut k = 0;
        while k < WORD.len() {
            if src[column + k] != WORD[k] {
                return false;
            }
            k += 1;
        }
        true
    }

    /// Byte length of `src` without its `reserved` rows.
    const fn settled_len(src: &[u8]) -> usize {
        let (mut i, mut len) = (0, 0);
        while i < src.len() {
            let start = i;
            while i < src.len() && src[i] != b'\n' {
                i += 1;
            }
            let end = i;
            if i < src.len() {
                i += 1; // the newline belongs to the line
            }
            if !is_reserved_row(src, start, end) {
                len += i - start;
            }
        }
        len
    }

    /// `src` without its `reserved` rows; `N` is [`settled_len`] of it.
    const fn settled_bytes<const N: usize>(src: &[u8]) -> [u8; N] {
        let mut out = [0u8; N];
        let (mut i, mut at) = (0, 0);
        while i < src.len() {
            let start = i;
            while i < src.len() && src[i] != b'\n' {
                i += 1;
            }
            let end = i;
            if i < src.len() {
                i += 1;
            }
            if !is_reserved_row(src, start, end) {
                let mut k = start;
                while k < i {
                    out[at] = src[k];
                    at += 1;
                    k += 1;
                }
            }
        }
        out
    }

    const SOURCE: &str = include_str!("binary.rs");

    /// Rows at or below this version predate the ledger and may carry the
    /// `pre-ledger` commit marker; every later row names its reserving commit.
    const LEDGER_EPOCH: u32 = 43;

    /// Version constants that live in SEPARATE version spaces (their own
    /// headers and magics), excluded from the module wire ledger by name.
    const SEPARATE_VERSION_SPACES: &[&str] = &["NATIVE_BUNDLE_VERSION", "PROOF_LINEAGE_VERSION"];

    #[derive(Clone, Copy, Debug, PartialEq, Eq)]
    enum Status {
        Retired,
        Shipped,
        Refused,
        Reserved,
    }

    #[derive(Clone, Debug)]
    struct Row {
        line: usize,
        version: u32,
        status: Status,
        feature: String,
        commit: String,
        owner: String,
    }

    /// The compiled constants the ledger is checked against. Built from the
    /// real constants by [`compiled`]; the negative twins perturb a copy.
    #[derive(Clone, Debug)]
    struct Consts {
        version: u32,
        format_version: u32,
        min_read: u32,
        /// Every per-feature `*_FORMAT_VERSION` constant.
        features: Vec<(&'static str, u32)>,
        /// Version constants that are aliases, checked elsewhere.
        aliases: Vec<(&'static str, u32)>,
        /// `AMBIGUOUS_LINEAGE_VERSIONS`: the in-window versions the reader
        /// refuses. It must be exactly the set of `refused` rows.
        ambiguous_lineage: std::ops::RangeInclusive<u32>,
    }

    fn compiled() -> Consts {
        Consts {
            version: VERSION,
            format_version: FORMAT_VERSION,
            min_read: MIN_READ_VERSION,
            features: vec![
                ("BASE_FORMAT_VERSION", BASE_FORMAT_VERSION),
                ("DIALECT_TYPE_FORMAT_VERSION", DIALECT_TYPE_FORMAT_VERSION),
                (
                    "CONTAINER_VTABLE_FORMAT_VERSION",
                    CONTAINER_VTABLE_FORMAT_VERSION,
                ),
                (
                    "CONTRACT_SURFACE_FORMAT_VERSION",
                    CONTRACT_SURFACE_FORMAT_VERSION,
                ),
                ("TUPLE_LAYOUT_FORMAT_VERSION", TUPLE_LAYOUT_FORMAT_VERSION),
                ("HANDLE_TYPE_FORMAT_VERSION", HANDLE_TYPE_FORMAT_VERSION),
                ("IMPORT_SCHEME_FORMAT_VERSION", IMPORT_SCHEME_FORMAT_VERSION),
                ("ABI_SURFACE_FORMAT_VERSION", ABI_SURFACE_FORMAT_VERSION),
                ("SPEC_CARRIER_FORMAT_VERSION", SPEC_CARRIER_FORMAT_VERSION),
                ("DROP_INST_FORMAT_VERSION", DROP_INST_FORMAT_VERSION),
                ("WEAK_CMPXCHG_FORMAT_VERSION", WEAK_CMPXCHG_FORMAT_VERSION),
                ("UNINIT_LANE_FORMAT_VERSION", UNINIT_LANE_FORMAT_VERSION),
                ("ARRAY_SPLAT_FORMAT_VERSION", ARRAY_SPLAT_FORMAT_VERSION),
                (
                    "INST_WIRE_BATCH_FORMAT_VERSION",
                    INST_WIRE_BATCH_FORMAT_VERSION,
                ),
                ("ASSERT_KIND_FORMAT_VERSION", ASSERT_KIND_FORMAT_VERSION),
                (
                    "CALL_UNWIND_BOUNDARY_FORMAT_VERSION",
                    CALL_UNWIND_BOUNDARY_FORMAT_VERSION,
                ),
                ("PANIC_SITE_FORMAT_VERSION", PANIC_SITE_FORMAT_VERSION),
                ("DROP_GLUE_FORMAT_VERSION", DROP_GLUE_FORMAT_VERSION),
                ("UNWIND_TWINS_FORMAT_VERSION", UNWIND_TWINS_FORMAT_VERSION),
                ("TEMPLATE_FORMAT_VERSION", TEMPLATE_FORMAT_VERSION),
                (
                    "NOMINAL_IDENTITY_FORMAT_VERSION",
                    NOMINAL_IDENTITY_FORMAT_VERSION,
                ),
                (
                    "EFFECT_SUMMARY_FORMAT_VERSION",
                    EFFECT_SUMMARY_FORMAT_VERSION,
                ),
                ("SIGNATURE_ABI_FORMAT_VERSION", SIGNATURE_ABI_FORMAT_VERSION),
                (
                    "CERTIFICATE_BINDING_FORMAT_VERSION",
                    CERTIFICATE_BINDING_FORMAT_VERSION,
                ),
                (
                    "PARAM_POINTEE_PLACE_FORMAT_VERSION",
                    PARAM_POINTEE_PLACE_FORMAT_VERSION,
                ),
                ("MAKE_CLOSURE_FORMAT_VERSION", MAKE_CLOSURE_FORMAT_VERSION),
                (
                    "CLOSURE_ORIGIN_FORMAT_VERSION",
                    CLOSURE_ORIGIN_FORMAT_VERSION,
                ),
                (
                    "STORAGE_LAYOUT_FORMAT_VERSION",
                    STORAGE_LAYOUT_FORMAT_VERSION,
                ),
                (
                    "SINGLE_INHABITED_ENUM_FORMAT_VERSION",
                    SINGLE_INHABITED_ENUM_FORMAT_VERSION,
                ),
                ("TENSOR_FORMAT_VERSION", TENSOR_FORMAT_VERSION),
                (
                    "TENSOR_MAP_REDUCE_VIEW_FORMAT_VERSION",
                    TENSOR_MAP_REDUCE_VIEW_FORMAT_VERSION,
                ),
                (
                    "TENSOR_GATHER_SCATTER_FORMAT_VERSION",
                    TENSOR_GATHER_SCATTER_FORMAT_VERSION,
                ),
                ("TENSOR_BLOB_FORMAT_VERSION", TENSOR_BLOB_FORMAT_VERSION),
            ],
            aliases: vec![
                // Compile-time asserted equal to BASE_FORMAT_VERSION.
                (
                    "PROJECTED_MODULE_BINARY_VERSION",
                    PROJECTED_MODULE_BINARY_VERSION,
                ),
            ],
            ambiguous_lineage: AMBIGUOUS_LINEAGE_VERSIONS,
        }
    }

    /// The name of the refused-range constant, bound by [`check_ledger`].
    const AMBIGUOUS_LINEAGE: &str = "AMBIGUOUS_LINEAGE_VERSIONS";

    /// `a..=b` as written in a range initializer.
    fn parse_inclusive_range(rhs: &str) -> Option<(u32, u32)> {
        let (lo, hi) = rhs.split_once("..=")?;
        Some((lo.trim().parse().ok()?, hi.trim().parse().ok()?))
    }

    /// Whether the real reader refuses a header carrying `version` at the
    /// version check (as opposed to failing later on the empty body).
    fn reader_refuses(version: u32) -> bool {
        let mut bytes = MAGIC.to_vec();
        bytes.extend_from_slice(&version.to_le_bytes());
        matches!(
            deserialize_module(&bytes),
            Err(BinaryError::UnsupportedVersion)
        )
    }

    fn parse(tsv: &str) -> Result<Vec<Row>, Vec<String>> {
        let mut rows = Vec::new();
        let mut errors = Vec::new();
        for (index, raw) in tsv.lines().enumerate() {
            let line = index + 1;
            if raw.trim().is_empty() || raw.starts_with('#') {
                continue;
            }
            let cols: Vec<&str> = raw.split('\t').collect();
            if cols.len() != 5 || cols.iter().any(|c| c.trim().is_empty()) {
                errors.push(format!(
                    "line {line}: expected 5 non-empty tab-separated columns, got {:?}",
                    cols
                ));
                continue;
            }
            let Ok(version) = cols[0].parse::<u32>() else {
                errors.push(format!("line {line}: version {:?} is not a u32", cols[0]));
                continue;
            };
            let status = match cols[1] {
                "retired" => Status::Retired,
                "shipped" => Status::Shipped,
                "refused" => Status::Refused,
                "reserved" => Status::Reserved,
                other => {
                    errors.push(format!(
                        "line {line}: v{version} has unknown status {other:?}"
                    ));
                    continue;
                }
            };
            rows.push(Row {
                line,
                version,
                status,
                feature: cols[2].to_owned(),
                commit: cols[3].to_owned(),
                owner: cols[4].to_owned(),
            });
        }
        if errors.is_empty() {
            Ok(rows)
        } else {
            Err(errors)
        }
    }

    /// `source` with this ledger module itself cut out: its own fixtures
    /// spell forged constants and gates inside string literals, which are not
    /// wire code. The module is top-level, so it ends at the first line that
    /// is exactly `}` after its header; anything after that (the mutation
    /// tests append there) is scanned.
    fn wire_code(source: &str) -> String {
        const HEADER: &str = "mod wire_version_ledger {";
        let mut out = String::with_capacity(source.len());
        let mut inside = false;
        for line in source.lines() {
            if !inside && line == HEADER {
                inside = true;
                continue;
            }
            if inside {
                if line == "}" {
                    inside = false;
                }
                continue;
            }
            out.push_str(line);
            out.push('\n');
        }
        out
    }

    /// Every item declaration `[pub[(..)]] (const|static) <NAME>: <ty> = <rhs>;`
    /// that begins a line of `source` and whose SCREAMING_CASE name contains
    /// `VERSION`, as `(name, rhs)`. Deliberately type-, visibility- and
    /// layout-agnostic: a `u16` constant, a `pub(super)` one, a `static`, or a
    /// rustfmt-wrapped declaration is still a version number that needs a row.
    fn scan_version_consts(source: &str) -> Vec<(String, String)> {
        let source = wire_code(source);
        let lines: Vec<&str> = source.lines().collect();
        let mut found = Vec::new();
        for (index, raw) in lines.iter().enumerate() {
            let mut t = raw.trim_start();
            if let Some(rest) = t.strip_prefix("pub") {
                let rest = rest.trim_start();
                t = if let Some(scoped) = rest.strip_prefix('(') {
                    match scoped.split_once(')') {
                        Some((_, after)) => after.trim_start(),
                        None => continue,
                    }
                } else {
                    rest
                };
            }
            let Some(rest) = t
                .strip_prefix("const ")
                .or_else(|| t.strip_prefix("static mut "))
                .or_else(|| t.strip_prefix("static "))
            else {
                continue;
            };
            let Some((name, _)) = rest.split_once(':') else {
                continue;
            };
            let name = name.trim();
            if !name.contains("VERSION")
                || !name
                    .chars()
                    .all(|c| c.is_ascii_uppercase() || c.is_ascii_digit() || c == '_')
            {
                continue;
            }
            // The initializer runs to the first `;`, possibly on a later line.
            let mut decl = String::new();
            for line in &lines[index..] {
                decl.push_str(line.trim());
                decl.push(' ');
                if line.contains(';') {
                    break;
                }
            }
            let rhs = decl
                .split_once('=')
                .and_then(|(_, rhs)| rhs.split_once(';'))
                .map(|(rhs, _)| rhs.trim().to_owned())
                .unwrap_or_default();
            found.push((name.to_owned(), rhs));
        }
        found
    }

    /// Every integer literal compared against an identifier ending in
    /// `version` in the code (not the comments) of `source`, as
    /// `(line, literal)`: `r.version >= 45`, `version>=45`, `45 <= version`.
    /// These are the read gates and writer selections development spells.
    fn scan_version_gate_literals(source: &str) -> Vec<(usize, u32)> {
        #[derive(Debug)]
        enum Tok {
            Ident(String),
            Int(u32),
            Cmp,
            Other,
        }
        let mut found = Vec::new();
        for (index, raw) in wire_code(source).lines().enumerate() {
            let code = raw.split_once("//").map_or(raw, |(code, _)| code);
            let chars: Vec<char> = code.chars().collect();
            let mut toks = Vec::new();
            let mut i = 0;
            while i < chars.len() {
                let c = chars[i];
                if c.is_whitespace() {
                    i += 1;
                } else if c.is_ascii_alphabetic() || c == '_' {
                    let start = i;
                    while i < chars.len() && (chars[i].is_ascii_alphanumeric() || chars[i] == '_') {
                        i += 1;
                    }
                    toks.push(Tok::Ident(chars[start..i].iter().collect()));
                } else if c.is_ascii_digit() {
                    let start = i;
                    while i < chars.len() && (chars[i].is_ascii_alphanumeric() || chars[i] == '_') {
                        i += 1;
                    }
                    let digits: String = chars[start..i].iter().filter(|c| **c != '_').collect();
                    toks.push(digits.parse::<u32>().map_or(Tok::Other, Tok::Int));
                } else if matches!(c, '=' | '-') && chars.get(i + 1) == Some(&'>') {
                    // `=>` (an arm) and `->` (a return type) never compare.
                    i += 2;
                    toks.push(Tok::Other);
                } else if matches!(c, '<' | '>' | '=' | '!') {
                    let two = chars.get(i + 1) == Some(&'=');
                    i += if two { 2 } else { 1 };
                    // `=` alone is assignment and `!` negation.
                    toks.push(if !two && matches!(c, '=' | '!') {
                        Tok::Other
                    } else {
                        Tok::Cmp
                    });
                } else {
                    i += 1;
                    toks.push(Tok::Other);
                }
            }
            let is_version = |t: &Tok| matches!(t, Tok::Ident(s) if s.ends_with("version"));
            for w in toks.windows(3) {
                match (&w[0], &w[1], &w[2]) {
                    (a, Tok::Cmp, Tok::Int(n)) if is_version(a) => found.push((index + 1, *n)),
                    (Tok::Int(n), Tok::Cmp, b) if is_version(b) => found.push((index + 1, *n)),
                    _ => {}
                }
            }
        }
        found
    }

    /// Whether `feature` names `constant` as a whole identifier (so
    /// `TYPE_FORMAT_VERSION` is not named by `HANDLE_TYPE_FORMAT_VERSION`).
    fn names(feature: &str, constant: &str) -> bool {
        feature
            .split(|c: char| !(c.is_ascii_alphanumeric() || c == '_'))
            .any(|token| token == constant)
    }

    fn check_ledger(
        tsv: &str,
        consts: &Consts,
        source: &str,
        reader_refuses: &dyn Fn(u32) -> bool,
    ) -> Result<(), Vec<String>> {
        let rows = parse(tsv)?;
        let mut errors = Vec::new();

        // Shape: non-empty, strictly ascending, contiguous, no duplicates.
        if rows.is_empty() {
            errors.push("the ledger has no rows".to_owned());
            return Err(errors);
        }
        for pair in rows.windows(2) {
            let (a, b) = (&pair[0], &pair[1]);
            if b.version == a.version {
                errors.push(format!(
                    "duplicate ledger row for v{} (lines {} and {})",
                    b.version, a.line, b.line
                ));
            } else if b.version < a.version {
                errors.push(format!(
                    "ledger rows out of order: v{} (line {}) after v{}",
                    b.version, b.line, a.version
                ));
            } else if b.version != a.version + 1 {
                errors.push(format!(
                    "ledger gap: no row for v{}..=v{}",
                    a.version + 1,
                    b.version - 1
                ));
            }
        }

        // VERSION is the highest shipped row; FORMAT_VERSION aliases it.
        let max_shipped = rows
            .iter()
            .filter(|r| r.status == Status::Shipped)
            .map(|r| r.version)
            .max();
        if max_shipped != Some(consts.version) {
            let shipped_row = rows
                .iter()
                .any(|r| r.version == consts.version && r.status == Status::Shipped);
            errors.push(format!(
                "VERSION = {} {} (highest shipped row: {:?})",
                consts.version,
                if shipped_row {
                    "is not the highest shipped row"
                } else {
                    "has no shipped row"
                },
                max_shipped
            ));
        }
        if consts.format_version != consts.version {
            errors.push(format!(
                "FORMAT_VERSION = {} differs from VERSION = {}",
                consts.format_version, consts.version
            ));
        }

        // MIN_READ_VERSION is the lowest row that is neither retired nor refused.
        let min_readable = rows
            .iter()
            .filter(|r| !matches!(r.status, Status::Retired | Status::Refused))
            .map(|r| r.version)
            .min();
        if min_readable != Some(consts.min_read) {
            errors.push(format!(
                "MIN_READ_VERSION = {} but the lowest non-retired, non-refused row is {:?}",
                consts.min_read, min_readable
            ));
        }

        // Per-row status against the constants and the real reader.
        for row in &rows {
            let v = row.version;
            let refused = reader_refuses(v);
            match row.status {
                Status::Retired => {
                    if v >= consts.min_read {
                        errors.push(format!(
                            "v{v} is retired but not below MIN_READ_VERSION = {}",
                            consts.min_read
                        ));
                    }
                    if !refused {
                        errors.push(format!("v{v} is retired but the reader accepts it"));
                    }
                }
                Status::Shipped => {
                    if !(consts.min_read..=consts.version).contains(&v) {
                        errors.push(format!(
                            "v{v} is shipped but outside MIN_READ_VERSION..=VERSION ({}..={})",
                            consts.min_read, consts.version
                        ));
                    }
                    if refused {
                        errors.push(format!("v{v} is shipped but the reader refuses it"));
                    }
                }
                Status::Refused => {
                    if !(consts.min_read..=consts.version).contains(&v) {
                        errors.push(format!(
                            "v{v} is refused but outside MIN_READ_VERSION..=VERSION ({}..={}); \
                             use retired or reserved",
                            consts.min_read, consts.version
                        ));
                    }
                    if !refused {
                        errors.push(format!("v{v} is refused but the reader accepts it"));
                    }
                }
                Status::Reserved => {
                    if v <= consts.version {
                        errors.push(format!(
                            "reserved v{v} is not above VERSION = {}",
                            consts.version
                        ));
                    }
                    if !refused {
                        errors.push(format!("v{v} is reserved but the reader accepts it"));
                    }
                }
            }

            // Provenance columns.
            let hex = row.commit.len() >= 7
                && row.commit.len() <= 40
                && row.commit.chars().all(|c| c.is_ascii_hexdigit());
            if row.commit == "pre-ledger" {
                if v > LEDGER_EPOCH {
                    errors.push(format!(
                        "v{v} postdates the ledger (epoch v{LEDGER_EPOCH}) and must name its \
                         reserving commit, not pre-ledger"
                    ));
                }
                if row.owner != "-" {
                    errors.push(format!("pre-ledger v{v} names an owner increment"));
                }
            } else if row.commit == "self" || hex {
                if row.owner == "-" {
                    errors.push(format!("v{v} names no owner increment"));
                }
            } else {
                errors.push(format!(
                    "v{v} reserving-commit {:?} is not pre-ledger, self, or a commit hash",
                    row.commit
                ));
            }
        }

        // AMBIGUOUS_LINEAGE_VERSIONS (the reader's in-window refusal, also
        // reported by BUILD_IDENTITY) is exactly the set of refused rows: a
        // refused range that drifts from the ledger is a lineage claim nobody
        // recorded, whichever side moved.
        let refused_rows: Vec<u32> = rows
            .iter()
            .filter(|r| r.status == Status::Refused)
            .map(|r| r.version)
            .collect();
        let refused_range: Vec<u32> = consts.ambiguous_lineage.clone().collect();
        if refused_rows != refused_range {
            errors.push(format!(
                "{AMBIGUOUS_LINEAGE} = {:?} but the refused ledger rows are {refused_rows:?}",
                consts.ambiguous_lineage
            ));
        }

        // Each per-feature constant equals a shipped row that names it, and is
        // named by exactly one row.
        for (name, value) in &consts.features {
            let naming: Vec<&Row> = rows.iter().filter(|r| names(&r.feature, name)).collect();
            match naming.as_slice() {
                [row] if row.version == *value && row.status == Status::Shipped => {}
                [row] => errors.push(format!(
                    "{name} = {value} but the row naming it is v{} ({:?})",
                    row.version, row.status
                )),
                [] => errors.push(format!("{name} = {value} is named by no ledger row")),
                many => errors.push(format!(
                    "{name} is named by {} ledger rows; name it once",
                    many.len()
                )),
            }
        }

        // Every shipped version above the legacy baseline is one the writer
        // can SELECT: some `*_FORMAT_VERSION` constant carries it. A shipped
        // row no selection constant names is a reader-only version — a bump
        // that raised VERSION and flipped the row but skipped the writer leg.
        match consts
            .features
            .iter()
            .find(|(name, _)| *name == "BASE_FORMAT_VERSION")
        {
            Some((_, base)) => {
                for row in rows
                    .iter()
                    .filter(|r| r.status == Status::Shipped && r.version > *base)
                {
                    if !consts.features.iter().any(|(_, v)| *v == row.version) {
                        errors.push(format!(
                            "shipped v{} is carried by no *_FORMAT_VERSION constant, so no \
                             writer can ever select it",
                            row.version
                        ));
                    }
                }
            }
            None => errors.push("BASE_FORMAT_VERSION is not bound".to_owned()),
        }

        // Read gates and writer selections spelled as literals: a number
        // development writes into a comparison must already have a ledger row
        // (shipped, retired, refused, or RESERVED) — the v39/v42 collisions
        // were unreserved numbers written into gates before anyone claimed them.
        let highest_row = rows.last().map_or(0, |r| r.version);
        for (line, literal) in scan_version_gate_literals(source) {
            if literal > highest_row {
                errors.push(format!(
                    "read gate at binary.rs line {line} compares a version against \
                     v{literal}, which has no ledger row: reserve v{literal} first"
                ));
            }
        }

        // Source scan: every version constant declared in binary.rs is either
        // listed above or a separate version space; every listed constant is
        // declared exactly once with the compiled value.
        let declared = scan_version_consts(source);
        let listed: Vec<(&str, u32)> = [
            ("VERSION", consts.version),
            ("FORMAT_VERSION", consts.format_version),
            ("MIN_READ_VERSION", consts.min_read),
        ]
        .into_iter()
        .chain(consts.features.iter().copied())
        .chain(consts.aliases.iter().copied())
        .collect();
        for (name, _) in &declared {
            let known = listed.iter().any(|(l, _)| l == name)
                || name == AMBIGUOUS_LINEAGE
                || SEPARATE_VERSION_SPACES.contains(&name.as_str());
            if !known {
                errors.push(format!(
                    "binary.rs declares {name} with no ledger binding: name it in its \
                     version's row and bind it in wire_version_ledger::compiled"
                ));
            }
        }
        for (name, value) in &listed {
            let decls: Vec<&(String, String)> =
                declared.iter().filter(|(d, _)| d == name).collect();
            match decls.as_slice() {
                [(_, rhs)] => {
                    if let Ok(literal) = rhs.parse::<u32>()
                        && literal != *value
                    {
                        errors.push(format!(
                            "{name} is declared as {literal} but checked as {value}"
                        ));
                    }
                }
                [] => errors.push(format!("the source scan found no declaration of {name}")),
                _ => errors.push(format!("the source scan found {name} declared twice")),
            }
        }
        let lineage_decls: Vec<&(String, String)> = declared
            .iter()
            .filter(|(d, _)| d == AMBIGUOUS_LINEAGE)
            .collect();
        match lineage_decls.as_slice() {
            [(_, rhs)] => match parse_inclusive_range(rhs) {
                Some((lo, hi))
                    if lo == *consts.ambiguous_lineage.start()
                        && hi == *consts.ambiguous_lineage.end() => {}
                _ => errors.push(format!(
                    "{AMBIGUOUS_LINEAGE} is declared as {rhs:?} but checked as {:?}",
                    consts.ambiguous_lineage
                )),
            },
            [] => errors.push(format!(
                "the source scan found no declaration of {AMBIGUOUS_LINEAGE}"
            )),
            _ => errors.push(format!(
                "the source scan found {AMBIGUOUS_LINEAGE} declared twice"
            )),
        }

        if errors.is_empty() {
            Ok(())
        } else {
            Err(errors)
        }
    }

    fn check_real(tsv: &str, consts: &Consts, source: &str) -> Result<(), Vec<String>> {
        check_ledger(tsv, consts, source, &reader_refuses)
    }

    fn assert_refused_naming(result: Result<(), Vec<String>>, needles: &[&str]) {
        let errors = result.expect_err("the mutated ledger must be refused");
        assert!(
            errors
                .iter()
                .any(|e| needles.iter().all(|needle| e.contains(needle))),
            "expected an error containing all of {needles:?}, got {errors:#?}"
        );
    }

    /// Positive: the ledger as landed is coherent with the constants, the
    /// reader and the source, and carries the historical shape.
    #[test]
    fn ledger_as_landed_is_coherent() {
        // The LIVE file, open reservations included: this is the binding.
        check_real(LIVE_LEDGER, &compiled(), SOURCE).unwrap_or_else(|errors| {
            panic!("wire_versions.tsv disagrees with binary.rs: {errors:#?}")
        });
        let rows = parse(LIVE_LEDGER).expect("ledger parses");
        let status = |v: u32| {
            rows.iter()
                .find(|r| r.version == v)
                .map(|r| r.status)
                .unwrap_or_else(|| panic!("no row for v{v}"))
        };
        for v in 2..=22 {
            assert_eq!(status(v), Status::Retired, "v{v}");
        }
        for v in (23..=25).chain(29..=VERSION) {
            assert_eq!(status(v), Status::Shipped, "v{v}");
        }
        for v in 26..=28 {
            assert_eq!(status(v), Status::Refused, "v{v}");
        }
        assert_eq!(rows.first().map(|r| r.version), Some(2));
    }

    /// The source scan sees every constant it is supposed to bind; without
    /// this a scanner that matched nothing would pass vacuously.
    #[test]
    fn source_scan_finds_every_bound_constant() {
        // Every version constant binary.rs declares: the wire-ledger ones and
        // the separate version spaces alike. The closing census below is this
        // list's OWN length, never a spelled number — a literal total is a
        // second line every new constant has to edit, and adding
        // `SPEC_CARRIER_FORMAT_VERSION` here while the total stayed at the
        // pre-v46 count is exactly how this test broke.
        const BOUND: &[&str] = &[
            "VERSION",
            "FORMAT_VERSION",
            "MIN_READ_VERSION",
            "BASE_FORMAT_VERSION",
            "DIALECT_TYPE_FORMAT_VERSION",
            "CONTAINER_VTABLE_FORMAT_VERSION",
            "CONTRACT_SURFACE_FORMAT_VERSION",
            "TUPLE_LAYOUT_FORMAT_VERSION",
            "HANDLE_TYPE_FORMAT_VERSION",
            "IMPORT_SCHEME_FORMAT_VERSION",
            "ABI_SURFACE_FORMAT_VERSION",
            "SPEC_CARRIER_FORMAT_VERSION",
            "DROP_INST_FORMAT_VERSION",
            "WEAK_CMPXCHG_FORMAT_VERSION",
            "UNINIT_LANE_FORMAT_VERSION",
            "ARRAY_SPLAT_FORMAT_VERSION",
            "INST_WIRE_BATCH_FORMAT_VERSION",
            "ASSERT_KIND_FORMAT_VERSION",
            "CALL_UNWIND_BOUNDARY_FORMAT_VERSION",
            "PANIC_SITE_FORMAT_VERSION",
            "DROP_GLUE_FORMAT_VERSION",
            "UNWIND_TWINS_FORMAT_VERSION",
            "TEMPLATE_FORMAT_VERSION",
            "NOMINAL_IDENTITY_FORMAT_VERSION",
            "EFFECT_SUMMARY_FORMAT_VERSION",
            "SIGNATURE_ABI_FORMAT_VERSION",
            "CERTIFICATE_BINDING_FORMAT_VERSION",
            "PARAM_POINTEE_PLACE_FORMAT_VERSION",
            "MAKE_CLOSURE_FORMAT_VERSION",
            "CLOSURE_ORIGIN_FORMAT_VERSION",
            "STORAGE_LAYOUT_FORMAT_VERSION",
            "SINGLE_INHABITED_ENUM_FORMAT_VERSION",
            "TENSOR_FORMAT_VERSION",
            "TENSOR_MAP_REDUCE_VIEW_FORMAT_VERSION",
            "TENSOR_GATHER_SCATTER_FORMAT_VERSION",
            "TENSOR_BLOB_FORMAT_VERSION",
            "PROJECTED_MODULE_BINARY_VERSION",
            "AMBIGUOUS_LINEAGE_VERSIONS",
            "NATIVE_BUNDLE_VERSION",
            "PROOF_LINEAGE_VERSION",
        ];
        let declared = scan_version_consts(SOURCE);
        for &name in BOUND {
            assert_eq!(
                declared.iter().filter(|(d, _)| d == name).count(),
                1,
                "{name} in {declared:?}"
            );
        }
        // Closed set: the scan finds these and nothing else. A constant that
        // is not on the list is one `check_ledger` would have to bind.
        assert_eq!(declared.len(), BOUND.len(), "{declared:?}");

        // The gate scan is not vacuous either: it sees the real read gates
        // (e.g. `3 if r.version >= 38`, `let scope = if version >= 33`) and
        // never the comments that quote them, and the excised ledger module
        // is gone while the rest of the file is kept.
        let gates = scan_version_gate_literals(SOURCE);
        for n in [33, 34, 36, 37, 38, 39] {
            assert!(gates.iter().any(|(_, l)| *l == n), "v{n} gate in {gates:?}");
        }
        assert!(gates.len() >= 30, "{gates:?}");
        let code = wire_code(SOURCE);
        assert!(!code.contains("mod wire_version_ledger"));
        assert!(code.contains("pub const HANDLE_TYPE_FORMAT_VERSION: u32 = 43;"));
        assert!(
            code.len() * 10 > SOURCE.len() * 9,
            "excision removed too much"
        );
    }

    /// The fixture baseline carries no open reservation, whatever is on disk,
    /// and the cut removes `reserved` rows and nothing else.
    #[test]
    fn mutation_fixtures_extend_a_ledger_with_no_open_reservations() {
        const INPUT: &[u8] =
            b"# reserved\tin a comment\n43\tshipped\treserved is a word here\tpre-ledger\t-\n\
45\treserved\tgroup a\tself\tWS1.12\n46\treserved\tgroup b\tself\tWS3.9";
        const N: usize = settled_len(INPUT);
        const OUT: [u8; N] = settled_bytes(INPUT);
        assert_eq!(
            core::str::from_utf8(&OUT),
            Ok("# reserved\tin a comment\n43\tshipped\treserved is a word here\tpre-ledger\t-\n")
        );
        let settled = parse(LEDGER).expect("the settled ledger parses");
        assert!(settled.iter().all(|row| row.status != Status::Reserved));
        let live = parse(LIVE_LEDGER).expect("the live ledger parses");
        assert_eq!(
            settled.len(),
            live.iter()
                .filter(|row| row.status != Status::Reserved)
                .count(),
            "the cut removed something other than a reserved row"
        );
        // And it is what makes the fixtures mean what they say: the settled
        // ledger with a real-looking reservation appended is still coherent.
        let next = VERSION + 1; // derived, never spelled
        let reserved = format!("{LEDGER}{next}\treserved\ta real reservation\tself\tWS9.9\n");
        check_real(&reserved, &compiled(), SOURCE)
            .unwrap_or_else(|errors| panic!("a by-the-book reservation must pass: {errors:#?}"));
    }

    /// The number after `VERSION` — the one a by-the-book reservation takes.
    /// Every fixture below derives its numbers from `VERSION`, never spells
    /// them: a test that spells `44` is itself a line every version bump must
    /// edit (docs/wire-allocation.md), and WS4.10's v44 bump edited nine.
    const NEXT: u32 = VERSION + 1;
    const AFTER_NEXT: u32 = VERSION + 2;

    /// Negative twin: VERSION raised to the next number with no shipped row
    /// is refused, naming it.
    #[test]
    fn version_bump_without_shipped_row_is_refused() {
        let mut consts = compiled();
        consts.version = NEXT;
        consts.format_version = NEXT;
        // The reader a VERSION = NEXT build would have: it accepts NEXT too.
        let reader = |v: u32| v != NEXT && reader_refuses(v);
        assert_refused_naming(
            check_ledger(LEDGER, &consts, SOURCE, &reader),
            &[&format!("VERSION = {NEXT}"), "has no shipped row"],
        );
    }

    /// Mutation control: a second row for `VERSION` (a reservation colliding
    /// with a shipped number) is refused as a duplicate naming it.
    #[test]
    fn duplicate_reserved_row_is_refused() {
        let mutated = format!("{LEDGER}{VERSION}\treserved\tcolliding group\tself\tWS1.12\n");
        assert_refused_naming(
            check_real(&mutated, &compiled(), SOURCE),
            &[&format!("duplicate ledger row for v{VERSION}")],
        );
    }

    /// Mutation control: a new per-feature version constant with no row is
    /// refused by the source scan, naming the constant.
    #[test]
    fn unlisted_format_version_const_is_refused() {
        let mutated = format!("{SOURCE}\nconst FOO_FORMAT_VERSION: u32 = {NEXT};\n");
        assert_refused_naming(
            check_real(LEDGER, &compiled(), &mutated),
            &["FOO_FORMAT_VERSION", "no ledger binding"],
        );
    }

    /// Mutation control: flipping the ambiguous-lineage v27 to shipped
    /// contradicts the reader, which refuses it.
    #[test]
    fn refused_row_flipped_to_shipped_is_refused() {
        let mutated = LEDGER.replace("27\trefused\t", "27\tshipped\t");
        assert_ne!(mutated, LEDGER, "the mutation must apply");
        assert_refused_naming(
            check_real(&mutated, &compiled(), SOURCE),
            &["v27 is shipped but the reader refuses it"],
        );
    }

    /// Mutation control: `AMBIGUOUS_LINEAGE_VERSIONS` (the reader's refused
    /// window) is bound to the `refused` rows in both directions and to its
    /// own declaration. Narrowing the constant, widening the refused rows, or
    /// declaring a different range in the source is each refused by name.
    #[test]
    fn ambiguous_lineage_range_is_bound_to_refused_rows() {
        let mut narrowed = compiled();
        narrowed.ambiguous_lineage = 26..=27;
        assert_refused_naming(
            check_real(LEDGER, &narrowed, SOURCE),
            &["AMBIGUOUS_LINEAGE_VERSIONS = 26..=27", "[26, 27, 28]"],
        );

        let widened = LEDGER.replace("29\tshipped\t", "29\trefused\t");
        assert_ne!(widened, LEDGER, "the mutation must apply");
        // A reader that also refused v29, so only the range binding can fire.
        let reader = |v: u32| v == 29 || reader_refuses(v);
        assert_refused_naming(
            check_ledger(&widened, &compiled(), SOURCE, &reader),
            &["AMBIGUOUS_LINEAGE_VERSIONS = 26..=28", "[26, 27, 28, 29]"],
        );

        let declared = "std::ops::RangeInclusive<u32> = 26..=28;";
        assert!(SOURCE.contains(declared));
        let redeclared = SOURCE.replace(declared, "std::ops::RangeInclusive<u32> = 26..=29;");
        assert_refused_naming(
            check_real(LEDGER, &compiled(), &redeclared),
            &["AMBIGUOUS_LINEAGE_VERSIONS is declared as \"26..=29\""],
        );
    }

    /// A reservation at or below VERSION, or one reusing the pre-ledger
    /// marker, is refused: a number is claimed before it ships, never after.
    #[test]
    fn reservation_rules_are_enforced() {
        let above = format!("{LEDGER}{NEXT}\treserved\tproof-surface identity\tself\tWS1.12\n");
        check_real(&above, &compiled(), SOURCE)
            .unwrap_or_else(|errors| panic!("a well-formed reservation must pass: {errors:#?}"));

        let unowned = format!("{LEDGER}{NEXT}\treserved\tproof-surface identity\tpre-ledger\t-\n");
        assert_refused_naming(
            check_real(&unowned, &compiled(), SOURCE),
            &[&format!("v{NEXT} postdates the ledger")],
        );

        let gap = format!("{LEDGER}{AFTER_NEXT}\treserved\tskipped a number\tself\tWS1.12\n");
        assert_refused_naming(
            check_real(&gap, &compiled(), SOURCE),
            &[&format!("ledger gap: no row for v{NEXT}..=v{NEXT}")],
        );

        let shipped_early = format!("{LEDGER}{NEXT}\tshipped\tnot yet in VERSION\tself\tWS1.12\n");
        assert_refused_naming(
            check_real(&shipped_early, &compiled(), SOURCE),
            &[&format!(
                "VERSION = {VERSION} is not the highest shipped row"
            )],
        );
    }

    /// Adversarial: spellings of a new version constant that a
    /// single-line, `u32`-only, `pub`/`pub(crate)`-only scanner misses. Each
    /// is still a version constant with no ledger binding and must be refused
    /// by name — a rustfmt-wrapped declaration, a narrower integer type, a
    /// `pub(super)` / `pub(in ..)` visibility, a `static`, and a name that
    /// carries `VERSION` without ending in it.
    #[test]
    fn unlisted_version_const_is_refused_in_every_spelling() {
        for (name, decl) in [
            (
                "WRAPPED_FORMAT_VERSION",
                "pub const WRAPPED_FORMAT_VERSION: u32 =\n    HANDLE_TYPE_FORMAT_VERSION + 1;"
                    .to_string(),
            ),
            (
                "NARROW_FORMAT_VERSION",
                format!("const NARROW_FORMAT_VERSION: u16 = {NEXT};"),
            ),
            (
                "SUPER_FORMAT_VERSION",
                format!("pub(super) const SUPER_FORMAT_VERSION: u32 = {NEXT};"),
            ),
            (
                "PATH_FORMAT_VERSION",
                format!("pub(in crate::binary) const PATH_FORMAT_VERSION: u32 = {NEXT};"),
            ),
            (
                "STATIC_FORMAT_VERSION",
                format!("static STATIC_FORMAT_VERSION: u32 = {NEXT};"),
            ),
            (
                "FORMAT_VERSION_NEXT",
                format!("const FORMAT_VERSION_NEXT: u32 = {NEXT};"),
            ),
        ] {
            let mutated = format!("{SOURCE}\n{decl}\n");
            assert_refused_naming(
                check_real(LEDGER, &compiled(), &mutated),
                &[name, "no ledger binding"],
            );
        }
    }

    /// Adversarial: a read gate spelling a number the ledger has not
    /// reserved is exactly the development-time write that collided at v39
    /// and v42. It is refused naming the number; once the row is reserved the
    /// same gate is admitted (development may begin), and a gate on a shipped
    /// or retired number is untouched.
    #[test]
    fn read_gate_on_unreserved_version_is_refused() {
        let gate = format!("    let later = if r.version >= {NEXT} {{\n");
        let mutated = format!("{SOURCE}\n{gate}");
        assert_refused_naming(
            check_real(LEDGER, &compiled(), &mutated),
            &["read gate", &format!("v{NEXT}"), "no ledger row"],
        );

        let spaced = format!("{SOURCE}\n    if version>={AFTER_NEXT} {{\n");
        assert_refused_naming(
            check_real(LEDGER, &compiled(), &spaced),
            &["read gate", &format!("v{AFTER_NEXT}")],
        );

        let reserved = format!("{LEDGER}{NEXT}\treserved\tproof-surface identity\tself\tWS1.12\n");
        check_real(&reserved, &compiled(), &mutated).unwrap_or_else(|errors| {
            panic!("a gate on a reserved number must be admitted: {errors:#?}")
        });

        // Comments describing a future gate are prose, not a gate.
        let prose = format!("{SOURCE}\n// a later batch will gate `version >= 99`\n");
        check_real(LEDGER, &compiled(), &prose)
            .unwrap_or_else(|errors| panic!("a comment is not a read gate: {errors:#?}"));
    }

    /// Adversarial: VERSION raised, its row flipped to `shipped`, but no
    /// writer-selection constant names the new version. The reader then
    /// accepts a version no writer can ever select — a skipped leg — and it
    /// is refused naming the row.
    #[test]
    fn shipped_version_without_selection_constant_is_refused() {
        let mut consts = compiled();
        consts.version = NEXT;
        consts.format_version = NEXT;
        let ledger = format!("{LEDGER}{NEXT}\tshipped\tsome group\tself\tWS1.12\n");
        let reader = |v: u32| v != NEXT && reader_refuses(v);
        let source = SOURCE.replace(
            &format!("pub const VERSION: u32 = {VERSION};"),
            &format!("pub const VERSION: u32 = {NEXT};"),
        );
        assert_ne!(source, SOURCE, "the mutation must apply");
        assert_refused_naming(
            check_ledger(&ledger, &consts, &source, &reader),
            &[&format!("shipped v{NEXT}"), "no *_FORMAT_VERSION"],
        );

        // With the selection constant bound and named, the same bump passes.
        consts.features.push(("NEXT_GROUP_FORMAT_VERSION", NEXT));
        let ledger = format!(
            "{LEDGER}{NEXT}\tshipped\tnext group: NEXT_GROUP_FORMAT_VERSION\tself\tWS1.12\n"
        );
        let source = format!("{source}\nconst NEXT_GROUP_FORMAT_VERSION: u32 = {NEXT};\n");
        check_ledger(&ledger, &consts, &source, &reader)
            .unwrap_or_else(|errors| panic!("a complete v{NEXT} bump must pass: {errors:#?}"));
    }

    /// Adversarial: feature names are matched as whole identifiers, not
    /// substrings. A legitimate constant whose name is a suffix of another's
    /// is not refused as "named by several rows", and a row naming only a
    /// longer identifier does not count as naming the shorter one.
    #[test]
    fn feature_names_match_whole_identifiers() {
        let mut consts = compiled();
        consts.features.push(("TYPE_FORMAT_VERSION", NEXT));
        consts.version = NEXT;
        consts.format_version = NEXT;
        let ledger =
            format!("{LEDGER}{NEXT}\tshipped\tgeneric types: TYPE_FORMAT_VERSION\tself\tWS3.9\n");
        let source = format!(
            "{}\nconst TYPE_FORMAT_VERSION: u32 = {NEXT};\n",
            SOURCE.replace(
                &format!("pub const VERSION: u32 = {VERSION};"),
                &format!("pub const VERSION: u32 = {NEXT};")
            )
        );
        let reader = |v: u32| v != NEXT && reader_refuses(v);
        check_ledger(&ledger, &consts, &source, &reader).unwrap_or_else(|errors| {
            panic!("a suffix-named constant named once must pass: {errors:#?}")
        });

        let ledger =
            format!("{LEDGER}{NEXT}\tshipped\tgeneric types: XTYPE_FORMAT_VERSION\tself\tWS3.9\n");
        assert_refused_naming(
            check_ledger(&ledger, &consts, &source, &reader),
            &[&format!(
                "TYPE_FORMAT_VERSION = {NEXT} is named by no ledger row"
            )],
        );
    }
}

#[cfg(test)]
mod generic_nominal_codec_tests {
    use super::*;

    #[test]
    fn nominal_ground_codec_refuses_extension_payloads() {
        let pool = StringPoolBuilder::new().seal();
        let generic = TyG::Tuple(vec![
            TyG::U8,
            TyG::Ext(TemplateRef::Param(crate::ParamId::new(0))),
        ]);
        let mut checked = CheckSink::default();
        write_ground_nominal_ty(&mut checked, &pool, &generic);
        assert!(checked.first.into_iter().flatten().any(|r| matches!(
            r,
            BinaryProjectionError::ConstructAheadOfWireTag {
                construct: "extension in a ground nominal field",
                ..
            }
        )));
        // Spell the untrusted extension with the ordinary S type codec. The
        // nominal-field reader must still refuse it instead of granting a new
        // wire row shape through the generic in-memory carrier.
        let mut bytes = Vec::new();
        write_ty(&mut bytes, &pool, &generic);
        let mut reader = Reader::new(&bytes);
        reader.version = VERSION;
        assert!(matches!(
            read_ground_nominal_ty::<TemplateRef>(&mut reader),
            Err(BinaryError::InvalidData(_))
        ));
        let mut reader = Reader::new(&bytes);
        reader.version = VERSION;
        assert!(read_ground_nominal_ty::<NoExt>(&mut reader).is_err());
        let mut bytes = Vec::new();
        write_ground_nominal_ty(&mut bytes, &pool, &Ty::Tuple(vec![Ty::U8, Ty::U64]));
        let mut reader = Reader::new(&bytes);
        reader.version = VERSION;
        assert_eq!(
            read_ground_nominal_ty::<NoExt>(&mut reader).unwrap(),
            Ty::Tuple(vec![Ty::U8, Ty::U64])
        );
    }
}

#[cfg(test)]
#[path = "binary/semr_u64_addition_tests.rs"]
mod semr_u64_addition_tests;
