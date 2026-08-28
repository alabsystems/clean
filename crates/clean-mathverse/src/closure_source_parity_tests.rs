// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//
//! R1-LAZY — the lazy [`ShardConstantSource`] eager-parity invariant,
//! mechanized (env-bypass census item 12, `data/env_bypass_census.json`
//! row `lazy-constant-source`; docs/analysis/spine-lattice-recon-2026-08-22.md
//! §3; designs/2026-08-22-spine-and-lattice-program.md §5 Ring R1).
//!
//! `Environment::set_constant_source` installs a door: constants become
//! resolvable through the `get_const` fallback with NO registration. The two
//! stated contracts that keep that door sound are:
//!
//! 1. **Eager parity** — a lazily-served closure must be indistinguishable
//!    from the same closure loaded eagerly into `Environment::constants`:
//!    the SAME name set (no extra, no dropped), field-identical
//!    `ConstantInfo` per name, and byte-identical kernel VERDICTS for any
//!    declaration replayed against it.
//! 2. **fresh()-invariance** — [`clean_kernel::env::ConstantSource::fresh`]
//!    is a pure memory hook: swapping views can never change what any name
//!    resolves to (and in particular can never WIDEN resolution past the
//!    per-shard serve gate).
//!
//! The pre-existing probe (`closure_source::tests::
//! lazy_closure_verdict_matches_eager`) is opt-in (`CLEAN_TEST_SHARD`) and
//! samples real shards. THIS battery is what upgrades the probe to a
//! mechanized invariant: it is hermetic (synthetic in-memory shards, no
//! downloads, runs on every `cargo test -p clean-mathverse --lib`), TOTAL
//! over the served name set, FAIL-CLOSED on any name it cannot compare, and
//! FALSIFIABLE — every adversarial arm below plants one mutation (tampered
//! type, tampered value, extra name, dropped name, unverified shard) and
//! asserts the checker detects it. The remaining P-half of the census
//! disposition — a spec-side theorem about `get_const`'s fallback — stays
//! owed under R1-LAZY.

use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;
use std::sync::Arc;

use clean_kernel::env::{ConstantInfo, ConstantSource, Environment, Reducibility, TrustedEnvExt};
use clean_kernel::expr::{Expr, ExprKind};
use clean_kernel::flat::{FlatExpr, FlatLevel};
use clean_kernel::level::Level;
use clean_kernel::{ConstantKind, Declaration, Name};

use crate::closure_source::ShardConstantSource;
use crate::shard::{ShardMmapReader, ShardWriter};
use crate::types::{
    AxiomProfile, ContentDomain, DeclKind, ImportConfidence, MathverseConstantHeader, SourceSystem,
    NO_VALUE,
};

// ---------------------------------------------------------------------------
// A tiny kernel-checkable world, specified ONCE and rendered two ways:
// (a) into `.mathverse` shard bytes (what the lazy source serves) and
// (b) into hand-built `ConstantInfo` (the INDEPENDENT eager reference).
// The reference is deliberately NOT derived through the code under test
// (`materialize_constant_from_reader` / `kind_and_reducibility`): if the
// implementation's kind→reducibility mapping drifts from the eager olean
// path's (`decl_to_constant_info` parity), the hard-coded expectation here
// catches it instead of drifting with it.
// ---------------------------------------------------------------------------

#[derive(Clone, Copy)]
enum ExprSpec {
    /// `Sort 0` (Prop).
    Sort0,
    /// `Sort 1` (Type).
    Sort1,
    /// `Const(name, [])`.
    Cnst(&'static str),
}

#[derive(Clone, Copy)]
struct SpecConst {
    name: &'static str,
    kind: DeclKind,
    ty: ExprSpec,
    value: Option<ExprSpec>,
}

/// Shard 1 (`Inv.Base`): a dependency chain plus one kernel-REJECTED body, so
/// the verdict-parity leg exercises BOTH verdict polarities.
const HONEST_BASE: [SpecConst; 4] = [
    // `def Inv.A : Sort 1 := Sort 0` — kernel-accepted.
    SpecConst {
        name: "Inv.A",
        kind: DeclKind::Definition,
        ty: ExprSpec::Sort1,
        value: Some(ExprSpec::Sort0),
    },
    // `def Inv.B : Sort 1 := Inv.A` — accepted, and its check RESOLVES the
    // dep `Inv.A` through whichever leg (eager map vs lazy source) is live.
    SpecConst {
        name: "Inv.B",
        kind: DeclKind::Definition,
        ty: ExprSpec::Sort1,
        value: Some(ExprSpec::Cnst("Inv.A")),
    },
    // `axiom Inv.P : Prop` — value-less; covered by resolution parity only.
    SpecConst {
        name: "Inv.P",
        kind: DeclKind::Axiom,
        ty: ExprSpec::Sort0,
        value: None,
    },
    // `def Inv.Bad : Sort 0 := Sort 0` — kernel-REJECTED in BOTH legs
    // (`Sort 0 : Sort 1 ≠ Sort 0`): parity on the reject polarity.
    SpecConst {
        name: "Inv.Bad",
        kind: DeclKind::Definition,
        ty: ExprSpec::Sort0,
        value: Some(ExprSpec::Sort0),
    },
];

/// Shard 2 (`Inv.Thm`): a theorem whose deps (`Inv.P` in shard 1, `Inv.p`
/// here) span shards, so verdict parity crosses the multi-shard index.
const HONEST_THM: [SpecConst; 2] = [
    // `axiom Inv.p : Inv.P`.
    SpecConst {
        name: "Inv.p",
        kind: DeclKind::Axiom,
        ty: ExprSpec::Cnst("Inv.P"),
        value: None,
    },
    // `theorem Inv.T : Inv.P := Inv.p` — accepted; pins Theorem→`Opaque`
    // reducibility parity at resolution level too.
    SpecConst {
        name: "Inv.T",
        kind: DeclKind::Theorem,
        ty: ExprSpec::Cnst("Inv.P"),
        value: Some(ExprSpec::Cnst("Inv.p")),
    },
];

fn kernel_expr(spec: ExprSpec) -> Expr {
    match spec {
        ExprSpec::Sort0 => Expr::from_kind(ExprKind::Sort(Level::zero())),
        ExprSpec::Sort1 => Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero()))),
        ExprSpec::Cnst(n) => {
            Expr::from_kind(ExprKind::Const(Name::from_string(n), Default::default()))
        }
    }
}

fn flat_expr_idx(w: &mut ShardWriter, l0: u32, l1: u32, spec: ExprSpec) -> u32 {
    match spec {
        ExprSpec::Sort0 => w.add_expr(FlatExpr::sort(l0)),
        ExprSpec::Sort1 => w.add_expr(FlatExpr::sort(l1)),
        ExprSpec::Cnst(n) => {
            let s = w.add_string(n);
            // `u32::MAX` levels-list index == empty level list.
            w.add_expr(FlatExpr::const_ref(s, u32::MAX))
        }
    }
}

/// Serialize `consts` into one `<module>.mathverse` file under `dir` and
/// mmap-open it demand-paged — the exact byte path the production lazy source
/// serves from.
fn write_shard_reader(dir: &Path, module: &str, consts: &[SpecConst]) -> ShardMmapReader {
    let mut w = ShardWriter::new();
    let l0 = w.add_level(FlatLevel::zero());
    let l1 = w.add_level(FlatLevel::succ(l0));
    for c in consts {
        let type_idx = flat_expr_idx(&mut w, l0, l1, c.ty);
        let value_idx = match c.value {
            Some(v) => flat_expr_idx(&mut w, l0, l1, v),
            None => NO_VALUE,
        };
        let name_idx = w.add_string(c.name);
        w.add_constant(MathverseConstantHeader {
            name_idx,
            type_idx,
            value_idx,
            source_system: SourceSystem::Lean4 as u8,
            import_confidence: ImportConfidence::Unverified as u8,
            content_domain: ContentDomain::PureMath as u8,
            decl_kind: c.kind as u8,
            axiom_profile: AxiomProfile::NONE,
            sidecar_digest: 0,
            provenance_idx: 0,
            level_params_start: 0,
            level_params_count: 0,
            _pad2: [0u8; 26],
        });
    }
    let mut buf = Vec::new();
    w.write(&mut buf).expect("serialize shard");
    let path = dir.join(format!("{module}.mathverse"));
    std::fs::write(&path, &buf).expect("write shard file");
    ShardMmapReader::open_lazy(&path).expect("mmap-open shard")
}

/// The INDEPENDENT eager expectation for one spec constant. The
/// kind→reducibility mapping is hard-coded here on purpose (see module doc):
/// it mirrors the eager olean path (`decl_to_constant_info`) — Definition is
/// `Regular(0)` (none of the spec bodies is a projection-fn lambda), Theorem
/// is `Opaque` (the verdict-relevant category — see `kind_and_reducibility`'s
/// doc), Opaque/Axiom are `Irreducible`.
fn expected_info(c: &SpecConst) -> ConstantInfo {
    let (kind, reducibility) = match c.kind {
        DeclKind::Definition => (ConstantKind::Definition, Reducibility::Regular(0)),
        DeclKind::Theorem => (ConstantKind::Theorem, Reducibility::Opaque),
        DeclKind::Opaque => (ConstantKind::Opaque, Reducibility::Irreducible),
        DeclKind::Axiom => (ConstantKind::Axiom, Reducibility::Irreducible),
        other => panic!("non-servable kind in spec: {other:?}"),
    };
    ConstantInfo::new_with_reducibility(
        Name::from_string(c.name),
        Vec::new(),
        kernel_expr(c.ty),
        c.value.map(kernel_expr),
        reducibility,
        kind,
    )
}

fn reference_of(specs: &[SpecConst]) -> BTreeMap<Name, ConstantInfo> {
    specs
        .iter()
        .map(|c| (Name::from_string(c.name), expected_info(c)))
        .collect()
}

/// The honest world: both shards served lazily (marked load-time verified,
/// as production does after the olean content-binding check) plus the
/// independent eager reference for all six constants.
fn honest_world(dir: &Path) -> (ShardConstantSource, BTreeMap<Name, ConstantInfo>) {
    let r1 = write_shard_reader(dir, "Inv.Base", &HONEST_BASE);
    let r2 = write_shard_reader(dir, "Inv.Thm", &HONEST_THM);
    let mut src = ShardConstantSource::from_readers(vec![r1, r2]);
    src.mark_all_verified();
    let mut reference = reference_of(&HONEST_BASE);
    reference.extend(reference_of(&HONEST_THM));
    (src, reference)
}

/// Copy an honest spec array with one named entry mutated.
fn mutate<const N: usize>(
    mut specs: [SpecConst; N],
    name: &str,
    f: impl FnOnce(&mut SpecConst),
) -> [SpecConst; N] {
    let i = specs
        .iter()
        .position(|c| c.name == name)
        .expect("mutated name must exist in the spec");
    f(&mut specs[i]);
    specs
}

// ---------------------------------------------------------------------------
// The mechanized invariant checker.
// ---------------------------------------------------------------------------

/// One way the lazy source diverged from the eager reference. ANY entry is an
/// invariant violation; the honest arm asserts the list is empty and every
/// adversarial arm asserts its planted mutation appears here.
#[derive(Debug)]
enum ParityDivergence {
    /// The source serves a name the eager reference does not contain — a
    /// phantom constant resolvable with no registration.
    Extra(Name),
    /// The eager reference contains a name the source does not serve.
    Dropped(Name),
    /// A served name the checker could NOT compare (`get()` refused).
    /// FAIL-CLOSED: an incomparable name is a divergence, never a skip.
    Unresolvable(Name),
    /// A served `ConstantInfo` differs from the eager reference in `field`.
    Field { name: Name, field: &'static str },
    /// Replaying the same declaration produced different kernel verdicts with
    /// deps served eagerly vs lazily.
    Verdict { name: Name, eager: bool, lazy: bool },
}

impl ParityDivergence {
    fn is_verdict(&self) -> bool {
        matches!(self, ParityDivergence::Verdict { .. })
    }
}

/// Totality accounting for one checker run — asserted by the arms so a check
/// that silently compared nothing can never read as a pass.
#[derive(Debug, Default)]
struct ParityStats {
    resolution_compared: usize,
    verdicts_compared: usize,
    verdict_accepts: usize,
    verdict_rejects: usize,
}

fn info_field_mismatch(got: &ConstantInfo, want: &ConstantInfo) -> Option<&'static str> {
    if got.name != want.name {
        return Some("name");
    }
    if got.level_params != want.level_params {
        return Some("level_params");
    }
    if got.type_ != want.type_ {
        return Some("type_");
    }
    if got.value != want.value {
        return Some("value");
    }
    if got.reducibility != want.reducibility {
        return Some("reducibility");
    }
    if got.kind != want.kind {
        return Some("kind");
    }
    if got.is_reducible != want.is_reducible {
        return Some("is_reducible");
    }
    None
}

/// The kernel replay declaration for a value-bearing reference constant
/// (`None` for axioms / value-less entries — those are covered by the
/// resolution-parity leg, which is total over ALL kinds).
fn replay_decl(info: &ConstantInfo) -> Option<Declaration> {
    let value = info.value.clone()?;
    Some(match info.kind {
        ConstantKind::Theorem => Declaration::Theorem {
            name: info.name.clone(),
            level_params: info.level_params.clone(),
            type_: info.type_.clone(),
            value,
        },
        ConstantKind::Definition => Declaration::Definition {
            name: info.name.clone(),
            level_params: info.level_params.clone(),
            type_: info.type_.clone(),
            value,
            is_reducible: false,
        },
        ConstantKind::Opaque => Declaration::Opaque {
            name: info.name.clone(),
            level_params: info.level_params.clone(),
            type_: info.type_.clone(),
            value,
        },
        ConstantKind::Axiom => return None,
    })
}

/// THE mechanized eager-parity check: TOTAL over the union of the served name
/// set and the eager reference, fail-closed on anything it cannot compare.
///
/// Three legs, all total:
/// 1. **Name-set equality** — every served name must be in the reference
///    (else `Extra`) and every reference name must be served (else
///    `Dropped`).
/// 2. **Resolution parity** — for EVERY name in the intersection, `get()`
///    must succeed (else `Unresolvable`, the fail-closed arm) and the
///    materialized `ConstantInfo` must be field-identical to the reference.
/// 3. **Verdict parity** — for EVERY value-bearing constant, replaying its
///    declaration must yield the identical kernel verdict with deps loaded
///    eagerly (reference in `Environment::constants`) vs served lazily
///    (`set_constant_source`). This is the semantic channel: it catches a
///    divergence even where field comparison is impossible.
fn eager_parity_check(
    source: &ShardConstantSource,
    reference: &BTreeMap<Name, ConstantInfo>,
) -> (Vec<ParityDivergence>, ParityStats) {
    let mut divs = Vec::new();
    let mut stats = ParityStats::default();

    // Leg 1: name-set equality.
    let served: BTreeSet<Name> = source.servable_names().into_iter().collect();
    for name in &served {
        if !reference.contains_key(name) {
            divs.push(ParityDivergence::Extra(name.clone()));
        }
    }
    for name in reference.keys() {
        if !served.contains(name) {
            divs.push(ParityDivergence::Dropped(name.clone()));
        }
    }

    // Leg 2: TOTAL resolution parity over the intersection.
    for (name, want) in reference {
        if !served.contains(name) {
            continue; // already reported as Dropped
        }
        match ConstantSource::get(source, name) {
            None => divs.push(ParityDivergence::Unresolvable(name.clone())),
            Some(got) => {
                stats.resolution_compared += 1;
                if let Some(field) = info_field_mismatch(got, want) {
                    divs.push(ParityDivergence::Field {
                        name: name.clone(),
                        field,
                    });
                }
            }
        }
    }

    // Leg 3: TOTAL verdict parity for every value-bearing reference constant.
    // The prelude env is built ONCE and cloned per leg: `with_prelude()`
    // re-checks the whole prelude each call (~seconds in debug), which turned
    // this battery into minutes when built per target; a clone is
    // state-identical by construction.
    let prelude_env = Environment::with_prelude();
    for (name, info) in reference {
        let Some(decl) = replay_decl(info) else {
            continue;
        };

        // EAGER leg: the whole reference closure (minus the target) lives in
        // `Environment::constants`.
        let mut eager = prelude_env.clone();
        eager.extend_constants_unchecked(reference.values().filter(|c| c.name != *name).cloned());
        let v_eager = eager.add_decl(decl.clone()).is_ok();

        // LAZY leg: nothing eager — every dep resolves through the installed
        // source via the `get_const` fallback (a fresh view, so one target's
        // materializations cannot leak into the next comparison).
        let mut lazy = prelude_env.clone();
        lazy.set_constant_source(Arc::new(source.fresh_view()));
        let v_lazy = lazy.add_decl(decl).is_ok();

        stats.verdicts_compared += 1;
        if v_eager == v_lazy {
            if v_eager {
                stats.verdict_accepts += 1;
            } else {
                stats.verdict_rejects += 1;
            }
        } else {
            divs.push(ParityDivergence::Verdict {
                name: name.clone(),
                eager: v_eager,
                lazy: v_lazy,
            });
        }
    }

    (divs, stats)
}

// ---------------------------------------------------------------------------
// The honest arm: the invariant HOLDS, totally, on a multi-shard world.
// ---------------------------------------------------------------------------

/// Eager parity holds — zero divergences — and the accounting proves the
/// check was TOTAL: all 6 servable constants resolution-compared, all 4
/// value-bearing ones verdict-replayed, with BOTH verdict polarities
/// exercised (`Inv.Bad` is kernel-rejected in both legs).
#[test]
fn test_r1_lazy_parity_honest_world_total_and_clean() {
    let dir = tempfile::tempdir().expect("tempdir");
    let (src, reference) = honest_world(dir.path());
    assert_eq!(src.servable_len(), 6, "spec world serves all 6 constants");

    let (divs, stats) = eager_parity_check(&src, &reference);
    assert!(
        divs.is_empty(),
        "eager-parity invariant violated on the honest world: {divs:?}"
    );
    assert_eq!(
        stats.resolution_compared, 6,
        "resolution parity must be TOTAL over the served set"
    );
    assert_eq!(
        stats.verdicts_compared, 4,
        "verdict parity must cover every value-bearing constant"
    );
    assert_eq!(stats.verdict_accepts, 3, "Inv.A, Inv.B, Inv.T accepted");
    assert_eq!(
        stats.verdict_rejects, 1,
        "Inv.Bad rejected in BOTH legs (reject-polarity parity)"
    );
}

// ---------------------------------------------------------------------------
// Adversarial arms: each plants ONE mutation and asserts detection.
// ---------------------------------------------------------------------------

/// A lazy source serving a constant whose TYPE differs from eager is
/// detected — on the field channel for the tampered constant itself AND on
/// the semantic channel for its dependent (`Inv.B`'s verdict flips because
/// `infer(Const Inv.A)` now reads the tampered type).
#[test]
fn test_r1_lazy_parity_detects_tampered_type() {
    let dir = tempfile::tempdir().expect("tempdir");
    let tampered = mutate(HONEST_BASE, "Inv.A", |c| c.ty = ExprSpec::Sort0);
    let r1 = write_shard_reader(dir.path(), "Inv.Base", &tampered);
    let r2 = write_shard_reader(dir.path(), "Inv.Thm", &HONEST_THM);
    let mut src = ShardConstantSource::from_readers(vec![r1, r2]);
    src.mark_all_verified();
    let mut reference = reference_of(&HONEST_BASE);
    reference.extend(reference_of(&HONEST_THM));

    let (divs, _stats) = eager_parity_check(&src, &reference);
    let a = Name::from_string("Inv.A");
    let b = Name::from_string("Inv.B");
    assert!(
        divs.iter().any(|d| matches!(
            d,
            ParityDivergence::Field { name, field: "type_" } if *name == a
        )),
        "tampered TYPE of Inv.A must be detected as a field divergence, got: {divs:?}"
    );
    assert!(
        divs.iter().any(|d| matches!(
            d,
            ParityDivergence::Verdict { name, eager: true, lazy: false } if *name == b
        )),
        "the dependent Inv.B's kernel verdict must flip (eager accept, lazy reject), got: {divs:?}"
    );
}

/// A lazy source serving a constant whose VALUE differs from eager is
/// detected by the field channel — even though BOTH values typecheck here, so
/// the verdict channel alone would MISS this mutation. This is exactly why
/// resolution parity must be total, not verdict-sampled.
#[test]
fn test_r1_lazy_parity_detects_tampered_value() {
    let dir = tempfile::tempdir().expect("tempdir");
    // Honest `Inv.B := Inv.A`; tampered `Inv.B := Sort 0`. Both are of type
    // `Sort 1`, so every kernel verdict stays identical.
    let tampered = mutate(HONEST_BASE, "Inv.B", |c| c.value = Some(ExprSpec::Sort0));
    let r1 = write_shard_reader(dir.path(), "Inv.Base", &tampered);
    let r2 = write_shard_reader(dir.path(), "Inv.Thm", &HONEST_THM);
    let mut src = ShardConstantSource::from_readers(vec![r1, r2]);
    src.mark_all_verified();
    let mut reference = reference_of(&HONEST_BASE);
    reference.extend(reference_of(&HONEST_THM));

    let (divs, _stats) = eager_parity_check(&src, &reference);
    let b = Name::from_string("Inv.B");
    assert!(
        divs.iter().any(|d| matches!(
            d,
            ParityDivergence::Field { name, field: "value" } if *name == b
        )),
        "tampered VALUE of Inv.B must be detected as a field divergence, got: {divs:?}"
    );
    assert!(
        !divs.iter().any(ParityDivergence::is_verdict),
        "control: this mutation is verdict-invisible — the verdict channel alone would miss it: {divs:?}"
    );
}

/// A lazy source serving an EXTRA name absent from eager is detected: a
/// phantom constant would be resolvable through `get_const` with no
/// registration anywhere.
#[test]
fn test_r1_lazy_parity_detects_extra_name() {
    let dir = tempfile::tempdir().expect("tempdir");
    let mut with_extra = HONEST_BASE.to_vec();
    with_extra.push(SpecConst {
        name: "Inv.Phantom",
        kind: DeclKind::Definition,
        ty: ExprSpec::Sort1,
        value: Some(ExprSpec::Sort0),
    });
    let r1 = write_shard_reader(dir.path(), "Inv.Base", &with_extra);
    let r2 = write_shard_reader(dir.path(), "Inv.Thm", &HONEST_THM);
    let mut src = ShardConstantSource::from_readers(vec![r1, r2]);
    src.mark_all_verified();
    let mut reference = reference_of(&HONEST_BASE);
    reference.extend(reference_of(&HONEST_THM));

    let (divs, _stats) = eager_parity_check(&src, &reference);
    let phantom = Name::from_string("Inv.Phantom");
    assert!(
        divs.iter()
            .any(|d| matches!(d, ParityDivergence::Extra(name) if *name == phantom)),
        "an extra served name must be detected, got: {divs:?}"
    );
}

/// A lazy source DROPPING a name the eager closure contains is detected.
#[test]
fn test_r1_lazy_parity_detects_dropped_name() {
    let dir = tempfile::tempdir().expect("tempdir");
    let without_b: Vec<SpecConst> = HONEST_BASE
        .iter()
        .copied()
        .filter(|c| c.name != "Inv.B")
        .collect();
    let r1 = write_shard_reader(dir.path(), "Inv.Base", &without_b);
    let r2 = write_shard_reader(dir.path(), "Inv.Thm", &HONEST_THM);
    let mut src = ShardConstantSource::from_readers(vec![r1, r2]);
    src.mark_all_verified();
    let mut reference = reference_of(&HONEST_BASE);
    reference.extend(reference_of(&HONEST_THM));

    let (divs, _stats) = eager_parity_check(&src, &reference);
    let b = Name::from_string("Inv.B");
    assert!(
        divs.iter()
            .any(|d| matches!(d, ParityDivergence::Dropped(name) if *name == b)),
        "a dropped name must be detected, got: {divs:?}"
    );
}

/// FAIL-CLOSED: a served name the checker cannot compare (here: the per-entry
/// serve gate refusing an unverified shard) is a DIVERGENCE, never a silent
/// skip — the parity check can only pass by comparing everything.
#[test]
fn test_r1_lazy_parity_fails_closed_on_unresolvable_names() {
    let dir = tempfile::tempdir().expect("tempdir");
    let r1 = write_shard_reader(dir.path(), "Inv.Base", &HONEST_BASE);
    let r2 = write_shard_reader(dir.path(), "Inv.Thm", &HONEST_THM);
    let mut src = ShardConstantSource::from_readers(vec![r1, r2]);
    // Only shard 1 (`Inv.Thm`) passes load-time verification; shard 0's four
    // names stay indexed (the index is verification-agnostic) but `get()`
    // refuses to serve them.
    src.mark_shard_verified(1);
    let mut reference = reference_of(&HONEST_BASE);
    reference.extend(reference_of(&HONEST_THM));

    let (divs, stats) = eager_parity_check(&src, &reference);
    let unresolvable: BTreeSet<String> = divs
        .iter()
        .filter_map(|d| match d {
            ParityDivergence::Unresolvable(name) => Some(name.to_string()),
            _ => None,
        })
        .collect();
    let expected: BTreeSet<String> = ["Inv.A", "Inv.B", "Inv.Bad", "Inv.P"]
        .into_iter()
        .map(str::to_string)
        .collect();
    assert_eq!(
        unresolvable, expected,
        "every gate-refused name must surface as Unresolvable (fail-closed), got: {divs:?}"
    );
    assert_eq!(
        stats.resolution_compared, 2,
        "only the verified shard's 2 names were comparable"
    );
}

// ---------------------------------------------------------------------------
// The fresh()-invariance contract, as its own arm.
// ---------------------------------------------------------------------------

/// `fresh()` cannot change resolution: over the FULL served set, every name
/// resolves field-identically before and after the swap — both through the
/// `ConstantSource` trait (what `ShardConstantSource` promises) and through
/// the kernel seam (`Environment::refresh_constant_source_cache`, what
/// `get_const` consumers observe).
#[test]
fn test_r1_lazy_fresh_resolution_invariance_total() {
    let dir = tempfile::tempdir().expect("tempdir");
    let (src, _reference) = honest_world(dir.path());

    // Warm PART of the memo, so the swap demonstrably discards a non-trivial
    // cache (the memo must be an output of materialization, never an input).
    let a = Name::from_string("Inv.A");
    let _ = ConstantSource::get(&src, &a).expect("warm Inv.A");

    // Snapshot resolution over the FULL served set.
    let mut names = src.servable_names();
    names.sort();
    let before: Vec<(Name, ConstantInfo)> = names
        .iter()
        .map(|n| {
            let ci = ConstantSource::get(&src, n).expect("original serves every servable name");
            (n.clone(), ci.clone())
        })
        .collect();
    assert_eq!(before.len(), 6, "invariance quantifies over the full set");

    // Trait-level: the fresh view resolves every name identically.
    let fresh = ConstantSource::fresh(&src).expect("ShardConstantSource always has a fresh view");
    let mut fresh_names = fresh.names();
    fresh_names.sort();
    assert_eq!(
        fresh_names, names,
        "fresh() must preserve the served name set"
    );
    for (name, want) in &before {
        let got = fresh
            .get(name)
            .expect("fresh() must keep serving every previously-served name");
        if let Some(field) = info_field_mismatch(got, want) {
            panic!("fresh() changed resolution of {name:?} in field {field}");
        }
    }

    // Kernel seam: `refresh_constant_source_cache` swaps the view in place;
    // `get_const` must resolve every lazy name identically across the swap.
    let mut env = Environment::with_prelude();
    env.set_constant_source(Arc::new(src.fresh_view()));
    let mut env_names = env.lazy_source_names();
    env_names.sort();
    assert_eq!(env_names, names, "the env serves the same lazy name set");
    let env_before: Vec<(Name, ConstantInfo)> = env_names
        .iter()
        .map(|n| {
            let ci = env
                .get_const(n)
                .expect("get_const resolves every lazy name");
            (n.clone(), ci.clone())
        })
        .collect();
    env.refresh_constant_source_cache();
    assert!(
        env.has_constant_source(),
        "refresh must not drop the source"
    );
    let mut env_names_after = env.lazy_source_names();
    env_names_after.sort();
    assert_eq!(
        env_names_after, env_names,
        "refresh must preserve the lazy name set"
    );
    for (name, want) in &env_before {
        let got = env
            .get_const(name)
            .expect("refresh_constant_source_cache must not drop any resolution");
        if let Some(field) = info_field_mismatch(got, want) {
            panic!("refresh_constant_source_cache changed resolution of {name:?} in field {field}");
        }
    }
}

/// `fresh()` cannot WIDEN resolution either: a name refused by the per-entry
/// serve gate (unverified shard) before the swap stays refused after it, while
/// verified names keep resolving identically. A fresh view that started
/// serving gate-refused names would be a soundness hole, not a memory hook.
#[test]
fn test_r1_lazy_fresh_cannot_widen_past_serve_gate() {
    let dir = tempfile::tempdir().expect("tempdir");
    let r1 = write_shard_reader(dir.path(), "Inv.Base", &HONEST_BASE);
    let r2 = write_shard_reader(dir.path(), "Inv.Thm", &HONEST_THM);
    let mut src = ShardConstantSource::from_readers(vec![r1, r2]);
    src.mark_shard_verified(1); // `Inv.Thm` only

    let served = Name::from_string("Inv.p"); // verified shard
    let refused = Name::from_string("Inv.A"); // unverified shard
    let want = ConstantSource::get(&src, &served)
        .expect("verified shard serves")
        .clone();
    assert!(
        ConstantSource::get(&src, &refused).is_none(),
        "unverified shard must refuse before the swap"
    );

    let fresh = ConstantSource::fresh(&src).expect("fresh view");
    assert!(
        fresh.get(&refused).is_none(),
        "fresh() must NOT widen resolution past the per-entry serve gate"
    );
    let got = fresh
        .get(&served)
        .expect("fresh view keeps serving verified names");
    if let Some(field) = info_field_mismatch(got, &want) {
        panic!("fresh() changed resolution of {served:?} in field {field}");
    }
}
