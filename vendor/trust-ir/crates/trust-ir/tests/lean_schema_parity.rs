// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0
//
// B3 schema-parity gate.
//
// The Rust IR is the canonical surface; the Lean operational semantics must
// keep up with it, or any module using an un-modelled construct falls outside
// the proven core. There is no Lean toolchain in CI here to *prove* parity, but
// we CAN mechanically detect *drift*: every Rust `Inst` / `CastOp` variant must
// either have a Lean constructor of the same name, or be on an explicit,
// documented allowlist of known-not-yet-modelled constructs.
//
// This makes the coordinated-triple rule enforceable: adding a new Rust variant
// without Lean semantics fails this test unless you also record it as known
// debt here (which docs/roadmap/B3-lean-ir-parity.md tracks). Removing the debt
// (adding the Lean constructor) requires deleting the allowlist entry, so the
// allowlist can never silently over-claim either.
//
// When a Lean toolchain is available, the real fix is to add the Lean
// constructors + semantics and shrink these allowlists to empty.

use std::collections::BTreeSet;
use std::path::PathBuf;

fn manifest() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
}

fn read_required(path: PathBuf) -> String {
    std::fs::read_to_string(&path).unwrap_or_else(|error| {
        panic!(
            "required checked-in Lean model {} could not be read: {error}",
            path.display()
        )
    })
}

/// Leading PascalCase identifier of a trimmed line, if it is a variant head
/// (`Name`, `Name {`, `Name(`, `Name,`) rather than a comment/attribute/field.
fn pascal_head(trimmed: &str) -> Option<String> {
    let mut chars = trimmed.char_indices();
    let (_, first) = chars.next()?;
    if !first.is_ascii_uppercase() {
        return None;
    }
    let end = trimmed
        .char_indices()
        .find(|(_, c)| !(c.is_ascii_alphanumeric() || *c == '_'))
        .map(|(i, _)| i)
        .unwrap_or(trimmed.len());
    let name = &trimmed[..end];
    // Must be followed by a variant delimiter (or end-of-line for the last one).
    let rest = trimmed[end..].trim_start();
    // Rust: `Name {` / `Name(` / `Name,`. Lean no-arg ctor: `Name : Inst`.
    if rest.is_empty()
        || rest.starts_with('{')
        || rest.starts_with('(')
        || rest.starts_with(',')
        || rest.starts_with(':')
    {
        Some(name.to_string())
    } else {
        None
    }
}

/// Top-level variant names of a Rust `pub enum NAME { ... }`.
fn rust_enum_variants(src: &str, enum_name: &str) -> BTreeSet<String> {
    let mut out = BTreeSet::new();
    let needle = format!("pub enum {enum_name} {{");
    let Some(start) = src.find(&needle) else {
        return out;
    };
    let body = &src[start + needle.len()..];
    let mut depth: i32 = 0;
    for line in body.lines() {
        let trimmed = line.trim_start();
        if depth == 0
            && !trimmed.starts_with("///")
            && !trimmed.starts_with("//")
            && !trimmed.starts_with("#[")
            && let Some(name) = pascal_head(trimmed)
        {
            out.insert(name);
        }
        depth += line.matches('{').count() as i32;
        depth -= line.matches('}').count() as i32;
        if depth < 0 {
            break; // closed the enum itself
        }
    }
    out
}

/// Constructor names of a Lean `inductive NAME where | A ... | B ... deriving`.
fn lean_constructors(src: &str, inductive_name: &str) -> BTreeSet<String> {
    let mut out = BTreeSet::new();
    let needle = format!("inductive {inductive_name} where");
    let Some(start) = src.find(&needle) else {
        return out;
    };
    for line in src[start + needle.len()..].lines() {
        let trimmed = line.trim_start();
        if trimmed.starts_with("deriving") || trimmed.starts_with("inductive ") {
            break;
        }
        if let Some(rest) = trimmed.strip_prefix("| ")
            && let Some(name) = pascal_head(rest.trim_start())
        {
            out.insert(name);
        }
    }
    out
}

fn lean_dir() -> PathBuf {
    manifest().join("../../lean/trust_ir-semantics/TrustIr")
}

/// Assert: (Rust variants − Lean constructors) == the documented allowlist.
fn assert_parity(axis: &str, rust: &BTreeSet<String>, lean: &BTreeSet<String>, allowlist: &[&str]) {
    assert!(
        !rust.is_empty(),
        "{axis}: failed to parse any Rust variants"
    );
    assert!(
        !lean.is_empty(),
        "{axis}: failed to parse any Lean constructors"
    );
    let allow: BTreeSet<String> = allowlist.iter().map(|s| s.to_string()).collect();
    let drift: BTreeSet<String> = rust.difference(lean).cloned().collect();

    let new_drift: Vec<&String> = drift.difference(&allow).collect();
    assert!(
        new_drift.is_empty(),
        "{axis}: these Rust variants have NO Lean constructor and are NOT on the \
         B3 allowlist — add Lean semantics (coordinated-triple) or record them in \
         the allowlist in this test + docs/roadmap/B3-lean-ir-parity.md: {new_drift:?}"
    );
    let stale_allow: Vec<&String> = allow.difference(&drift).collect();
    assert!(
        stale_allow.is_empty(),
        "{axis}: these allowlist entries are no longer drifting (Lean now has them, \
         or they were renamed/removed) — delete them from the allowlist so the gate \
         keeps enforcing parity: {stale_allow:?}"
    );
}

#[test]
fn inst_and_castop_track_the_lean_model() {
    let inst_rs = std::fs::read_to_string(manifest().join("src/inst.rs")).expect("inst.rs");
    let lean_inst = read_required(lean_dir().join("Inst.lean"));
    let lean_castop = read_required(lean_dir().join("CastOp.lean"));

    // --- Inst ---
    let rust_inst = rust_enum_variants(&inst_rs, "Inst");
    let lean_inst_ctors = lean_constructors(&lean_inst, "Inst");
    // Known debt: Rust Inst variants not yet in the Lean operational model.
    // Shrink to empty as Lean semantics are added (needs a Lean toolchain).
    // GlobalAddr: Lean semGlobalAddr landed (cached, aliasing-faithful partial;
    // size/contents need module context — documented follow-up).
    // HeapAlloc / PtrData / PtrMetadata / PtrFromParts: landed earlier.
    // EMPTY — every Rust Inst variant now has a Lean constructor + semantics.
    // The 2026-07-01 drift was discharged 2026-07-02:
    //  * SeqMapAddK / SeqMapNot — semSeqMapAddK / semSeqMapNot
    //    (Semantics/Aggregate.lean) with the operational round-trip laws
    //    seqMapAddKList_roundTrip / seqMapNotList_involutive
    //    (Proofs/AggregateProps.lean); element op definitionally `BinOp Add` /
    //    `Bool.not` (seqElemAddK_eq_semIntBinOp_add).
    //  * CoroSuspend — semCoroSuspend (Semantics/Coroutine.lean), defined as
    //    the documented GEP+Store+Return macro-expansion
    //    (semCoroSuspend_is_macro_expansion).
    //  * Invoke / LandingPad / Resume — the NON-THROWING executable model
    //    mirroring interpret.rs (panic=abort): StepResult.InvokeReq runs the
    //    call and takes the normal edge binding the invoke's results
    //    (Eval.lean); a directly-executed LandingPad binds (null, 0); Resume
    //    is a structured `unsupported.host_unwind`. Full host-unwinding
    //    (taken unwind edges) remains a documented model refinement — see
    //    docs/roadmap/B3-lean-ir-parity.md "Depth gaps".
    // All six carry native_decide interpreter-agreement fixtures
    // (Semantics/ExecutableFixtures.lean).
    const INST_ALLOWLIST: &[&str] = &[];
    assert_parity("Inst", &rust_inst, &lean_inst_ctors, INST_ALLOWLIST);

    // --- CastOp ---
    let rust_castop = rust_enum_variants(&inst_rs, "CastOp");
    let lean_castop_ctors = lean_constructors(&lean_castop, "CastOp");
    // EMPTY — every Rust CastOp variant now has a Lean constructor + semCast
    // case. Transmute (scalar-only partial) and ReifyFnPointer (fn-item
    // partial) landed earlier; the saturating float→int drift (FPToSISat /
    // FPToUISat — Rust `f as iN`/`uN`, LLVM fptosi.sat/fptoui.sat) was
    // discharged 2026-07-10: EXACT saturating semantics mirroring the
    // reference interpreter (interpret.rs) — NaN → 0, out-of-range clamps to
    // MIN/MAX, in-range truncates toward zero via the exact frExp mantissa
    // decomposition (Semantics/Cast.lean fpToSISatRaw / fpToUISatRaw) — with
    // interpreter-agreement native_decide fixtures at two widths per op
    // (Semantics/ExecutableFixtures.lean fptosisat_* / fptouisat_*).
    // Note: cast_op_excluded (bridge.rs) still conservatively excludes the
    // pair from the cross-IR bridge subset (as it does the Transmute /
    // ReifyFnPointer partials); that subset gate is a separate, stricter
    // decision from the name+semantics parity this test enforces.
    const CASTOP_ALLOWLIST: &[&str] = &[];
    assert_parity("CastOp", &rust_castop, &lean_castop_ctors, CASTOP_ALLOWLIST);

    // --- Ty ---
    // The Rust `Ty` enum is the canonical type surface; the Lean `Ty`
    // (TrustIr/Basic.lean) must track it or record the gap. This axis closes
    // the audit finding that `Ty::F16` existed in Rust with no Lean semantics
    // and *nothing watching the drift*: now a new Rust `Ty` variant without a
    // Lean constructor fails this test unless it is recorded below.
    let ty_rs = std::fs::read_to_string(manifest().join("src/ty.rs")).expect("ty.rs");
    let lean_basic = read_required(lean_dir().join("Basic.lean"));
    let rust_ty = rust_enum_variants(&ty_rs, "Ty");
    let lean_ty_ctors = lean_constructors(&lean_basic, "Ty");
    // EMPTY — every Rust `Ty` variant now has a Lean constructor. F16 and the
    // FatPtr/FatPtrKind were added to TrustIr/Basic.lean (F16 remains a
    // type-level float; FatPtr now has first-class value, trio, and 16-byte
    // memory semantics on the pinned 64-bit executable target). v30's
    // `Refine` landed as a coordinated triple: `Ty.Refine : TyId -> PredId ->
    // Ty` plus `Ty.isRefine`/`refineBase`/`refinePred` in Basic.lean. It needs
    // no new operational rule because it is REPRESENTATION-PRESERVING — its
    // meaning is definitionally its base type's, so every existing semantic
    // rule already covers it through the base.
    const TY_ALLOWLIST: &[&str] = &[];
    assert_parity("Ty", &rust_ty, &lean_ty_ctors, TY_ALLOWLIST);
}

/// The v30 PREDICATE LATTICE axis: `Pred` / `Space` / `Universe`.
///
/// `Ty::Refine` landed with a Lean constructor, but the lattice it points at
/// (`crates/trust-ir/src/pred.rs`) was unmodelled — so the consumption rule in
/// `trust-ir-build/src/validate.rs` rested on an unverified claim about
/// `implies`. `lean/trust_ir-semantics/TrustIr/Pred.lean` now models it and
/// `TrustIr/Proofs/PredLatticeProps.lean` proves `implies` sound against a
/// denotation. This gate is what keeps the two from drifting: a new Rust
/// predicate shape with no Lean constructor fails here, and so does a stale
/// allowlist entry.
///
/// Same limitation as the axis above, stated plainly: this matches
/// constructor NAMES mechanically (there is no Lean toolchain in CI, or on the
/// authoring box). It cannot see whether the Lean semantics is *right*; the
/// denotation and the proofs are what carry that, and the last block below at
/// least keeps them from being deleted silently.
#[test]
fn pred_lattice_tracks_the_lean_model() {
    let pred_rs = std::fs::read_to_string(manifest().join("src/pred.rs")).expect("pred.rs");
    let lean_pred = read_required(lean_dir().join("Pred.lean"));

    // --- Pred ---
    // The Lean `Pred` is the TREE form (children inline) and `PredEntry` is
    // the id-spelled table form Rust stores; both carry these same nine
    // constructor names, and `PredTable.resolve` unfolds one into the other.
    let rust_pred = rust_enum_variants(&pred_rs, "Pred");
    let lean_pred_ctors = lean_constructors(&lean_pred, "Pred");
    // EMPTY — every Rust `Pred` variant has a Lean constructor, a denotation
    // arm (`Pred.denote`) and an `implies` arm. Keep it empty: a predicate
    // shape with no Lean meaning is a hole in exactly the mechanism the typed
    // value model exists to close.
    const PRED_ALLOWLIST: &[&str] = &[];
    assert_parity("Pred", &rust_pred, &lean_pred_ctors, PRED_ALLOWLIST);

    // --- Space ---
    // The index-vs-member distinction IS the miscompile class. If a third
    // convention is ever added to Rust without a Lean constructor, the
    // soundness proof stops covering it — fail here instead.
    let rust_space = rust_enum_variants(&pred_rs, "Space");
    let lean_space_ctors = lean_constructors(&lean_pred, "Space");
    const SPACE_ALLOWLIST: &[&str] = &[];
    assert_parity("Space", &rust_space, &lean_space_ctors, SPACE_ALLOWLIST);

    // --- Universe ---
    let rust_universe = rust_enum_variants(&pred_rs, "Universe");
    let lean_universe_ctors = lean_constructors(&lean_pred, "Universe");
    const UNIVERSE_ALLOWLIST: &[&str] = &[];
    assert_parity(
        "Universe",
        &rust_universe,
        &lean_universe_ctors,
        UNIVERSE_ALLOWLIST,
    );

    // --- The model is more than a name list ---
    // Names alone would pass on a file that declared the constructors and
    // nothing else. These check that the pieces the soundness argument needs
    // are still present: a denotation, the decision procedure, the join, and
    // the theorems stated against them. (Presence, not correctness — only a
    // Lean toolchain can give correctness, and there is none here.)
    for needle in [
        "def Pred.denote",
        "def Pred.impliesFuel",
        "def Pred.join",
        "def constDenote",
        "def Universe.contains",
    ] {
        assert!(
            lean_pred.contains(needle),
            "Pred lattice: `{needle}` vanished from TrustIr/Pred.lean — the parity gate \
             cannot certify constructor names against a model that no longer has a \
             denotation or a decision procedure"
        );
    }
    let lean_props = read_required(lean_dir().join("Proofs/PredLatticeProps.lean"));
    for needle in [
        "theorem impliesFuel_sound",
        "theorem implies_sound",
        "theorem join_upper_bound_left",
        "theorem join_upper_bound_right",
        "theorem denote_Top",
        "theorem index_never_implies_member",
    ] {
        assert!(
            lean_props.contains(needle),
            "Pred lattice: `{needle}` is missing from \
             TrustIr/Proofs/PredLatticeProps.lean — the consumption rule's soundness \
             claim has no statement backing it"
        );
    }
    // No `sorry` may creep into the lattice proofs: a `sorry` would satisfy
    // every `contains` check above while proving nothing, and would surface in
    // the Lean build only as a `sorryAx` in the axiom audit.
    for (name, src) in [
        ("Pred.lean", &lean_pred),
        ("PredLatticeProps.lean", &lean_props),
    ] {
        assert!(
            !src.contains("sorry"),
            "{name} contains `sorry` — the lattice soundness proof must not be stubbed"
        );
    }
}
