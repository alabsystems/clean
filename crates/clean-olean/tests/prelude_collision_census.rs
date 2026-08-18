// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **Prelude/`.olean` collision census + ratchet.**
//!
//! Clean seeds a full hand-rolled prelude and then imports a real Lean
//! environment on top of it. `.olean` import is *first-registered-wins* —
//! "Duplicate constants (already in `env`) are skipped, not overwritten"
//! (`crates/clean-olean/src/import/load.rs:43`, enforced at
//! `import/load_register.rs:1309-1331`). So wherever a prelude name collides
//! with a Lean name, **Lean's declaration is discarded and Clean's survives**.
//!
//! When the two disagree structurally, everything downstream sees Clean's
//! spelling while the user writes Lean's. The measured example is
//! `List.append_nil`: the prelude states it over the bare function
//! (`List.append α as (List.nil α)`) while Lean states it in notation
//! (`as ++ [] = as`, i.e. `HAppend.hAppend …`), so `rw [List.append_nil]` on
//! `l ++ []` finds nothing to match. Full evidence, controls and survey:
//! `docs/plans/CLASS_PROJECTION_SURFACE_2026-07-29.md`.
//!
//! **That class of defect was invisible: nothing counted it.** This census makes
//! it countable and ratchets it shut.
//!
//! ## Lanes
//!
//! | test | needs `.olean`? | what it enforces |
//! |---|---|---|
//! | [`census_artifact_is_self_consistent_and_ratcheted`] | no | artifact totals match its own rows; every ratcheted count is flat-or-down |
//! | [`census_prelude_side_is_current`] | no | every recorded prelude spelling still matches the live prelude — a prelude edit that changes a shadowing statement fails until the census is regenerated |
//! | [`census_matches_real_lean_olean`] | yes (release only) | the recorded Lean spellings and the collision set still match a real toolchain |
//!
//! ## Regenerating
//!
//! ```sh
//! CLEAN_PRELUDE_CENSUS_UPDATE=1 \
//!   cargo test --offline --release -p clean-olean --test prelude_collision_census
//! ```
//!
//! The heavy lane is release-only on purpose: it imports all of `Init`
//! (~93k constants), which is ~2 min in release and far worse in debug. In debug
//! it reports as skipped and the two cheap lanes still gate.

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

use clean_kernel::env::Environment;
use clean_kernel::name::Name;
use clean_kernel::{Expr, Level};

/// Root module whose transitive closure is censused.
const IMPORT_ROOT: &str = "Init";

const CENSUS_REL: &str = "data/prelude_collision_census.json";
const RATCHET_REL: &str = "data/prelude_collision_ratchet.json";
const UPDATE_ENV_VAR: &str = "CLEAN_PRELUDE_CENSUS_UPDATE";

/// Heterogeneous binary-operator class projections — the notation surface Lean
/// states its class-op lemmas over. A collision is classified `bare_spelled`
/// when Lean's statement goes through one of these and Clean's does not.
///
/// Mirrors `clean-elab/src/tactic/op_projection.rs::HETERO_OP_PROJECTIONS`,
/// duplicated because `clean-olean` does not (and should not) depend on the
/// elaborator. [`census_bare_spelled_marker_list_is_current`] is not possible
/// across that crate boundary, so the list is deliberately conservative: adding
/// a projection here can only ever move a row INTO the ratcheted class.
const OP_PROJECTIONS: &[&str] = &[
    "HAdd.hAdd",
    "HSub.hSub",
    "HMul.hMul",
    "HDiv.hDiv",
    "HMod.hMod",
    "HPow.hPow",
    "HAnd.hAnd",
    "HOr.hOr",
    "HXor.hXor",
    "HShiftLeft.hShiftLeft",
    "HShiftRight.hShiftRight",
    "HAppend.hAppend",
    "Neg.neg",
    "LE.le",
    "LT.lt",
    "Membership.mem",
    "GetElem.getElem",
    "OfNat.ofNat",
];

// ---------------------------------------------------------------------------
// Artifact model
// ---------------------------------------------------------------------------

#[derive(serde::Serialize, serde::Deserialize, PartialEq, Eq, Clone, Debug)]
struct Collision {
    name: String,
    /// Kind as the prelude declares it (`Theorem`, `Definition`, …).
    prelude_kind: String,
    /// Kind as the discarded Lean declaration declares it.
    lean_kind: String,
    /// The type Clean's prelude registers — the one that stays in scope.
    prelude_type: String,
    /// The type Lean's `.olean` carries — the one the import discards.
    lean_type: String,
    /// Whether the prelude has a value (a proof/definition body) for this name.
    prelude_has_value: bool,
    /// Lean's statement goes through a class projection and Clean's does not:
    /// the `List.append_nil` shape.
    bare_spelled: bool,
}

#[derive(serde::Serialize, serde::Deserialize, PartialEq, Eq, Debug)]
struct Totals {
    prelude_constants: usize,
    olean_constants: usize,
    /// Names present in BOTH the prelude and the import.
    colliding_names: usize,
    /// Collisions where the two types are not syntactically equal (modulo
    /// universe-parameter renaming). These are the ones that can change what a
    /// tactic sees.
    type_differing: usize,
    /// Of those, the ones where Lean's spelling uses a class projection and
    /// Clean's does not — the `List.append_nil` family.
    bare_spelled: usize,
}

/// One bare-spelled row in the per-family breakdown: the colliding name and
/// the kind of the DISCARDED Lean declaration (`Theorem`/`Definition`/…) —
/// i.e. what a fix must re-register in Lean's exact spelling.
#[derive(serde::Serialize, serde::Deserialize, PartialEq, Eq, Clone, Debug)]
struct BareSpelledEntry {
    name: String,
    lean_kind: String,
}

/// All bare-spelled rows sharing one head namespace family.
/// `count` always equals `entries.len()` (asserted in lane 1).
#[derive(serde::Serialize, serde::Deserialize, PartialEq, Eq, Clone, Debug)]
struct FamilyBreakdown {
    count: usize,
    entries: Vec<BareSpelledEntry>,
}

#[derive(serde::Serialize, serde::Deserialize, PartialEq, Eq, Debug)]
struct Census {
    generated_by: String,
    import_root: String,
    totals: Totals,
    /// Per-head-namespace-family breakdown of the `bare_spelled` rows (family
    /// = first `.`-component: `Nat.add_comm` → `Nat`, `List.Perm.mem_iff` →
    /// `List`), so the roadmap's `Nat.*`/`Int.*` sub-counts are reproducible
    /// from the artifact. Derived from `collisions` at regeneration time —
    /// never hand-edited. `#[serde(default)]` so pre-breakdown artifacts still
    /// PARSE (the ratchet checker must not hard-fail on old files), but lane 1
    /// asserts consistency with the listed rows, which forces the field to be
    /// present and correct in the checked-in artifact.
    #[serde(default)]
    bare_spelled_by_family: BTreeMap<String, FamilyBreakdown>,
    /// Every type-differing collision, both spellings printed. Type-EQUAL
    /// collisions are counted in `totals` but not listed: they are harmless
    /// (the discarded declaration says the same thing).
    collisions: Vec<Collision>,
}

#[derive(serde::Serialize, serde::Deserialize, Debug)]
struct Ratchet {
    note: String,
    /// Flat-or-down. Raising a baseline to green a build is the one thing this
    /// file exists to prevent.
    baseline_type_differing: usize,
    baseline_bare_spelled: usize,
    /// Names that MUST appear in the census `bare_spelled` set. Recorded from
    /// the 2026-07-29 investigation (§2.1); a name may leave this list only by
    /// being fixed, which the counts above already force.
    known_bare_spelled: Vec<String>,
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn repo_root() -> PathBuf {
    // CARGO_MANIFEST_DIR = <root>/crates/clean-olean
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .expect("crate manifest dir has a two-level ancestor")
        .to_path_buf()
}

fn read_json<T: serde::de::DeserializeOwned>(rel: &str) -> T {
    let path = repo_root().join(rel);
    let bytes = std::fs::read(&path)
        .unwrap_or_else(|e| panic!("fail-closed: cannot read {}: {e}", path.display()));
    serde_json::from_slice(&bytes)
        .unwrap_or_else(|e| panic!("fail-closed: cannot parse {}: {e}", path.display()))
}

/// Rename a declaration's universe parameters to positional canonical names so
/// two structurally identical statements are not reported as differing merely
/// because Clean writes `u_0` where Lean writes `u`.
fn canonicalize_levels(ty: &Expr, level_params: &[Name]) -> Expr {
    if level_params.is_empty() {
        return ty.clone();
    }
    let subst: Vec<(Name, Level)> = level_params
        .iter()
        .enumerate()
        .map(|(i, p)| {
            (
                p.clone(),
                Level::param(Name::from_string(&format!("_c{i}"))),
            )
        })
        .collect();
    ty.instantiate_level_params(&subst)
}

/// Whether `printed` mentions any class projection from [`OP_PROJECTIONS`] as an
/// applied head. The census compares printed forms rather than walking `Expr`
/// twice; the printed form is the same one the `rw` diagnostic shows.
fn uses_op_projection(printed: &str) -> bool {
    OP_PROJECTIONS.iter().any(|p| printed.contains(p))
}

/// Head namespace family of a colliding name: the first `.`-component
/// (`Nat.add_comm` → `Nat`, `List.Perm.mem_iff` → `List`).
fn head_family(name: &str) -> &str {
    name.split('.').next().unwrap_or(name)
}

/// Group the bare-spelled collisions by head namespace family. Pure derivation
/// from the rows — this is what makes the roadmap's `Nat.*`/`Int.*` sub-counts
/// reproducible from the artifact alone.
fn bare_spelled_breakdown(collisions: &[Collision]) -> BTreeMap<String, FamilyBreakdown> {
    let mut families: BTreeMap<String, FamilyBreakdown> = BTreeMap::new();
    for c in collisions.iter().filter(|c| c.bare_spelled) {
        let fam = families
            .entry(head_family(&c.name).to_owned())
            .or_insert_with(|| FamilyBreakdown {
                count: 0,
                entries: Vec::new(),
            });
        fam.count += 1;
        fam.entries.push(BareSpelledEntry {
            name: c.name.clone(),
            lean_kind: c.lean_kind.clone(),
        });
    }
    families
}

/// Locate a Lean toolchain `lib/lean` directory, or `None` when this machine has
/// no toolchain provisioned.
fn olean_search_paths() -> Option<Vec<PathBuf>> {
    let paths = clean_olean::default_search_paths();
    let usable: Vec<PathBuf> = paths
        .into_iter()
        .filter(|p| p.join("Init.olean").is_file())
        .collect();
    (!usable.is_empty()).then_some(usable)
}

/// Compute the census from a live prelude and a live `.olean` import.
fn compute_census(search_paths: &[PathBuf]) -> Census {
    let prelude = Environment::with_prelude();
    let prelude_side: BTreeMap<String, (Expr, String, bool)> = prelude
        .constants()
        .map(|c| {
            (
                c.name.to_string(),
                (
                    canonicalize_levels(&c.type_, &c.level_params),
                    format!("{:?}", c.kind),
                    c.value.is_some(),
                ),
            )
        })
        .collect();

    // Import into a BARE environment: with no prelude to collide with, nothing
    // is discarded, so this is exactly "what Lean would have contributed".
    let mut lean_env = Environment::new();
    clean_olean::load_module_with_deps(&mut lean_env, IMPORT_ROOT, search_paths)
        .unwrap_or_else(|e| panic!("importing {IMPORT_ROOT} must succeed: {e}"));

    let mut collisions = Vec::new();
    let mut colliding_names = 0usize;
    let olean_constants = lean_env.num_constants();

    for lean in lean_env.constants() {
        let name = lean.name.to_string();
        let Some((prelude_type, prelude_kind, prelude_has_value)) = prelude_side.get(&name) else {
            continue;
        };
        colliding_names += 1;
        let lean_type = canonicalize_levels(&lean.type_, &lean.level_params);
        if &lean_type == prelude_type {
            continue;
        }
        let prelude_printed = prelude_type.to_string();
        let lean_printed = lean_type.to_string();
        collisions.push(Collision {
            name,
            prelude_kind: prelude_kind.clone(),
            lean_kind: format!("{:?}", lean.kind),
            bare_spelled: uses_op_projection(&lean_printed)
                && !uses_op_projection(&prelude_printed),
            prelude_type: prelude_printed,
            lean_type: lean_printed,
            prelude_has_value: *prelude_has_value,
        });
    }
    collisions.sort_by(|a, b| a.name.cmp(&b.name));

    let bare_spelled = collisions.iter().filter(|c| c.bare_spelled).count();
    Census {
        generated_by: format!(
            "{UPDATE_ENV_VAR}=1 cargo test --offline --release -p clean-olean \
             --test prelude_collision_census"
        ),
        import_root: IMPORT_ROOT.to_owned(),
        totals: Totals {
            prelude_constants: prelude_side.len(),
            olean_constants,
            colliding_names,
            type_differing: collisions.len(),
            bare_spelled,
        },
        bare_spelled_by_family: bare_spelled_breakdown(&collisions),
        collisions,
    }
}

// ---------------------------------------------------------------------------
// Lane 1 — artifact self-consistency + ratchet (no toolchain)
// ---------------------------------------------------------------------------

#[test]
fn census_artifact_is_self_consistent_and_ratcheted() {
    let census: Census = read_json(CENSUS_REL);
    let ratchet: Ratchet = read_json(RATCHET_REL);

    assert_eq!(
        census.totals.type_differing,
        census.collisions.len(),
        "{CENSUS_REL}: totals.type_differing must equal the number of listed rows"
    );
    assert_eq!(
        census.totals.bare_spelled,
        census.collisions.iter().filter(|c| c.bare_spelled).count(),
        "{CENSUS_REL}: totals.bare_spelled must equal the number of bare_spelled rows"
    );

    assert!(
        census.totals.type_differing <= ratchet.baseline_type_differing,
        "prelude/.olean collision ratchet BROKEN: type-differing collisions rose to {} \
         (baseline {}). Every one of these silently discards Lean's declaration and keeps \
         Clean's — do NOT raise the baseline to green the build; make the prelude agree with \
         Lean, or stop seeding the stub. See {RATCHET_REL}.",
        census.totals.type_differing,
        ratchet.baseline_type_differing
    );
    assert!(
        census.totals.bare_spelled <= ratchet.baseline_bare_spelled,
        "prelude/.olean collision ratchet BROKEN: bare-spelled shadowing rose to {} \
         (baseline {}). These are statements the user writes in notation and Clean stores \
         over the bare function — `rw`/`simp` will not match them. See {RATCHET_REL}.",
        census.totals.bare_spelled,
        ratchet.baseline_bare_spelled
    );

    let bare: BTreeSet<&str> = census
        .collisions
        .iter()
        .filter(|c| c.bare_spelled)
        .map(|c| c.name.as_str())
        .collect();

    // The per-family breakdown must be exactly the derivation of the listed
    // rows — the artifact carries it only so the sub-counts are readable and
    // diffable; the rows stay the single source of truth.
    let expected_breakdown = bare_spelled_breakdown(&census.collisions);
    assert_eq!(
        census.bare_spelled_by_family, expected_breakdown,
        "{CENSUS_REL}: bare_spelled_by_family must be exactly the per-family \
         derivation of the listed bare_spelled rows (family = head namespace, \
         entries = name + discarded Lean kind). Regenerate the artifact; never \
         hand-edit it."
    );
    let breakdown_total: usize = census
        .bare_spelled_by_family
        .values()
        .map(|f| f.count)
        .sum();
    assert_eq!(
        breakdown_total, census.totals.bare_spelled,
        "{CENSUS_REL}: per-family counts must sum to totals.bare_spelled"
    );

    let missing: Vec<&String> = ratchet
        .known_bare_spelled
        .iter()
        .filter(|n| !bare.contains(n.as_str()))
        .collect();
    assert!(
        missing.is_empty(),
        "{CENSUS_REL} no longer records these known bare-spelled shadowings: {missing:?}. \
         If they were genuinely fixed, drop them from {RATCHET_REL} in the same commit and \
         lower the baselines; a silent disappearance means the census stopped measuring."
    );
}

// ---------------------------------------------------------------------------
// Lane 2 — the prelude side is still what the artifact says (no toolchain)
// ---------------------------------------------------------------------------

#[test]
fn census_prelude_side_is_current() {
    let census: Census = read_json(CENSUS_REL);
    let prelude = Environment::with_prelude();

    let mut stale = Vec::new();
    for row in &census.collisions {
        let name = Name::from_string(&row.name);
        let Some(info) = prelude.get_const(&name) else {
            stale.push(format!("{}: no longer in the prelude", row.name));
            continue;
        };
        let printed = canonicalize_levels(&info.type_, &info.level_params).to_string();
        if printed != row.prelude_type {
            stale.push(format!(
                "{}: prelude now states\n    {printed}\n  census recorded\n    {}",
                row.name, row.prelude_type
            ));
        }
    }
    assert!(
        stale.is_empty(),
        "{CENSUS_REL} is stale against the live prelude — regenerate it \
         (see `generated_by` in the artifact):\n{}",
        stale.join("\n")
    );
}

// ---------------------------------------------------------------------------
// Lane 3 — the recorded Lean side still matches a real toolchain (release only)
// ---------------------------------------------------------------------------

#[test]
fn census_matches_real_lean_olean() {
    if cfg!(debug_assertions) {
        eprintln!(
            "SKIP census_matches_real_lean_olean: release-only lane \
             (importing {IMPORT_ROOT} in debug is prohibitively slow). \
             Run: cargo test --offline --release -p clean-olean --test prelude_collision_census"
        );
        return;
    }
    let Some(search_paths) = olean_search_paths() else {
        eprintln!(
            "SKIP census_matches_real_lean_olean: no Lean toolchain with {IMPORT_ROOT}.olean \
             on the default search paths."
        );
        return;
    };

    let fresh = compute_census(&search_paths);

    if std::env::var(UPDATE_ENV_VAR).is_ok() {
        let path = repo_root().join(CENSUS_REL);
        let json = serde_json::to_string_pretty(&fresh).expect("census must serialize");
        std::fs::write(&path, json + "\n")
            .unwrap_or_else(|e| panic!("cannot write {}: {e}", path.display()));
        eprintln!(
            "WROTE {CENSUS_REL}: {} colliding names, {} type-differing, {} bare-spelled",
            fresh.totals.colliding_names, fresh.totals.type_differing, fresh.totals.bare_spelled
        );
        return;
    }

    let recorded: Census = read_json(CENSUS_REL);
    assert_eq!(
        recorded.totals, fresh.totals,
        "{CENSUS_REL} totals no longer match a live import — regenerate with \
         {UPDATE_ENV_VAR}=1"
    );
    assert_eq!(
        recorded.bare_spelled_by_family, fresh.bare_spelled_by_family,
        "{CENSUS_REL} per-family breakdown no longer matches a live import — \
         regenerate with {UPDATE_ENV_VAR}=1"
    );
    let recorded_names: Vec<&str> = recorded
        .collisions
        .iter()
        .map(|c| c.name.as_str())
        .collect();
    let fresh_names: Vec<&str> = fresh.collisions.iter().map(|c| c.name.as_str()).collect();
    assert_eq!(
        recorded_names, fresh_names,
        "{CENSUS_REL} collision set no longer matches a live import — regenerate with \
         {UPDATE_ENV_VAR}=1"
    );
    assert_eq!(
        recorded.collisions, fresh.collisions,
        "{CENSUS_REL} recorded spellings no longer match a live import — regenerate with \
         {UPDATE_ENV_VAR}=1"
    );
}

// ---------------------------------------------------------------------------
// Breakdown derivation — pure-function regression (no toolchain)
// ---------------------------------------------------------------------------

/// `bare_spelled_breakdown` groups by the FIRST name component only, keeps row
/// order (rows are name-sorted), records the discarded LEAN kind, and ignores
/// rows that are type-differing but not bare-spelled.
#[test]
fn test_bare_spelled_breakdown_groups_by_head_namespace() {
    let row = |name: &str, lean_kind: &str, bare: bool| Collision {
        name: name.to_owned(),
        prelude_kind: "Definition".to_owned(),
        lean_kind: lean_kind.to_owned(),
        prelude_type: "P".to_owned(),
        lean_type: "L".to_owned(),
        prelude_has_value: true,
        bare_spelled: bare,
    };
    let rows = vec![
        row("Int.add_comm", "Theorem", true),
        row("List.Perm.mem_iff", "Theorem", true),
        row("Nat.add_comm", "Theorem", true),
        row("Nat.decLe", "Definition", true),
        row("NotBare.thing", "Theorem", false),
    ];
    let breakdown = bare_spelled_breakdown(&rows);

    let families: Vec<&str> = breakdown.keys().map(String::as_str).collect();
    assert_eq!(
        families,
        vec!["Int", "List", "Nat"],
        "families are the head components, sorted, non-bare rows excluded"
    );
    assert_eq!(breakdown["Nat"].count, 2, "Nat family counts both rows");
    assert_eq!(
        breakdown["Nat"].entries,
        vec![
            BareSpelledEntry {
                name: "Nat.add_comm".to_owned(),
                lean_kind: "Theorem".to_owned(),
            },
            BareSpelledEntry {
                name: "Nat.decLe".to_owned(),
                lean_kind: "Definition".to_owned(),
            },
        ],
        "entries keep row order and record the DISCARDED Lean kind"
    );
    assert_eq!(
        breakdown["List"].entries[0].name, "List.Perm.mem_iff",
        "nested namespaces fold into the head family (List, not List.Perm)"
    );
    let total: usize = breakdown.values().map(|f| f.count).sum();
    assert_eq!(total, 4, "family counts sum to the bare_spelled total");
}
