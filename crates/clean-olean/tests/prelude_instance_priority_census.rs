// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **Prelude instance-priority census + ratchet.**
//!
//! Clean's hand-rolled prelude registers typeclass instances with a priority it
//! *guesses*; real Lean serializes the true priority into every `.olean`
//! (`Lean.Meta.instanceExtension`, an `InstanceEntry` per registration). Because
//! `.olean` import is first-registered-wins, a guessed priority that disagrees
//! with Lean's used to survive the import forever — and instance priority
//! decides which candidate `synthInstance` reaches first, i.e. **the shape of
//! every elaborated term**.
//!
//! That defect was fixed one-off three times before anyone counted it:
//!
//! | commit | instance | Clean guessed | Lean's `.olean` |
//! |---|---|---|---|
//! | `8d80c9d98` | `instOfNatNat` | 100 | 1000 |
//! | `066a1173f` | `instLTNat`    | 100 | 1000 |
//! | `28e7834a1` | B101 hetero bridges | 50, seeded pre-import | — |
//!
//! The `instOfNatNat` mistake is the one to learn from: Lean's source reads
//! `@[default_instance 100] instance instOfNatNat …`, and Clean read the `100`
//! off `@[default_instance]` — a **different table** (literal-type defaulting,
//! not `synthInstance` candidate ordering). The `instance` itself is
//! unannotated, so its real priority is Lean's default 1000. **This census
//! therefore never reads a priority off a Lean SOURCE attribute.** It reads the
//! `u64` that Lean serialized into the shipped `.olean`, decoded by Clean's own
//! `InstanceEntry` reader.
//!
//! ## Lanes
//!
//! | test | needs `.olean`? | what it enforces |
//! |---|---|---|
//! | [`priority_census_artifact_is_self_consistent_and_ratcheted`] | no | totals match rows; mismatches flat-or-down; **denominator never shrinks** |
//! | [`priority_census_clean_side_is_current`] | no | every recorded Clean priority still matches the live prelude |
//! | [`priority_census_matches_real_lean_olean`] | yes (release only) | the recorded Lean priorities still match a real toolchain |
//! | [`import_adopts_lean_priority_for_hand_registered_instances`] | yes (release only) | the STRUCTURAL fix: after `import Init`, no hand-registered instance keeps a priority Lean disagrees with |
//!
//! ## Regenerating
//!
//! ```sh
//! CLEAN_PRIORITY_CENSUS_UPDATE=1 \
//!   cargo test --offline --release -p clean-olean --test prelude_instance_priority_census
//! ```

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

use clean_kernel::env::Environment;
use clean_olean::{parse_imports_only, ParsedExtensionEntry};

/// Root module whose transitive closure supplies the real Lean priorities.
const IMPORT_ROOT: &str = "Init";

/// The persisted name of Lean 4's typeclass-instance extension
/// (`Lean/Meta/Instances.lean`). Spelled out because `clean-olean`'s own
/// constant is `pub(crate)` and this is an integration test.
const LEAN_INSTANCE_EXTENSION: &str = "Lean.Meta.instanceExtension";

const CENSUS_REL: &str = "data/prelude_instance_priority_census.json";
const RATCHET_REL: &str = "data/prelude_instance_priority_ratchet.json";
const UPDATE_ENV_VAR: &str = "CLEAN_PRIORITY_CENSUS_UPDATE";

// ---------------------------------------------------------------------------
// Artifact model
// ---------------------------------------------------------------------------

#[derive(serde::Serialize, serde::Deserialize, PartialEq, Eq, Clone, Debug)]
struct Row {
    /// Instance constant name, identical on both sides (that is what makes it
    /// a collision: the import will not re-register it).
    name: String,
    /// The class Clean files it under.
    class: String,
    /// The priority Clean's hand-rolled prelude registers.
    clean_priority: u32,
    /// The priority Lean serialized into the shipped `.olean` — NOT read off a
    /// source attribute.
    lean_priority: u32,
    /// `clean_priority != lean_priority`: the defect.
    mismatch: bool,
}

#[derive(serde::Serialize, serde::Deserialize, PartialEq, Eq, Debug)]
struct Totals {
    /// Every instance the hand-rolled prelude registers.
    prelude_instances: usize,
    /// Every `InstanceEntry` decoded from the `Init` closure's `.olean`s.
    lean_instance_entries: usize,
    /// Prelude instances that Lean also registers under the same name — the
    /// **denominator**. These are the only ones whose priority can be wrong in
    /// the way this census measures; the rest are Clean-only names Lean never
    /// registers, so no guess can contradict anything.
    colliding: usize,
    /// Of those, the ones whose priorities disagree. The number to drive to 0.
    mismatched: usize,
    /// Modules of the `Init` closure whose `.olean` was walked.
    modules_walked: usize,
    /// `InstanceEntry` slots a typed decoder recognized but could not decode.
    /// Nonzero would mean the Lean side is under-measured.
    undecoded_instance_entries: usize,
}

#[derive(serde::Serialize, serde::Deserialize, PartialEq, Eq, Debug)]
struct Census {
    generated_by: String,
    import_root: String,
    totals: Totals,
    /// Every colliding instance, both priorities. Agreeing rows are listed too:
    /// they are what pins the denominator against being shrunk.
    rows: Vec<Row>,
}

#[derive(serde::Serialize, serde::Deserialize, Debug)]
struct Ratchet {
    note: String,
    /// Flat-or-DOWN. A new mismatched hand-registration fails the gate.
    baseline_mismatched: usize,
    /// Flat-or-UP. **The denominator may never shrink**: the class must not be
    /// "fixed" by deleting hand-registrations until nothing is measured.
    baseline_colliding: usize,
    /// Same, for the whole hand-registered surface.
    baseline_prelude_instances: usize,
    /// Every name that MUST still be measured. A name may leave this list only
    /// together with a deliberate, explained baseline edit.
    known_colliding: Vec<String>,
    /// Every name allowed to be mismatched today. A mismatch NOT on this list
    /// fails even when the count stays flat (one fixed, one introduced).
    known_mismatched: Vec<String>,
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn repo_root() -> PathBuf {
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

fn olean_search_paths() -> Option<Vec<PathBuf>> {
    let usable: Vec<PathBuf> = clean_olean::default_search_paths()
        .into_iter()
        .filter(|p| p.join("Init.olean").is_file())
        .collect();
    (!usable.is_empty()).then_some(usable)
}

/// The instances Clean's hand-rolled prelude registers: name → (class, priority).
fn clean_side() -> BTreeMap<String, (String, u32)> {
    Environment::with_prelude()
        .instances()
        .map(|i| (i.name.to_string(), (i.class_name.to_string(), i.priority)))
        .collect()
}

/// `IMPORT_ROOT`'s transitive import closure in dependency-first order, so a
/// later module's re-registration of the same instance name overwrites an
/// earlier one exactly as Lean's environment replay would.
fn closure_modules(search_paths: &[PathBuf]) -> Vec<PathBuf> {
    let mut out = Vec::new();
    let mut visited: BTreeSet<String> = BTreeSet::new();
    let mut stack: Vec<(String, bool)> = vec![(IMPORT_ROOT.to_owned(), false)];
    while let Some((module, expanded)) = stack.pop() {
        if expanded {
            if let Some(path) = clean_olean::find_module_olean(&module, search_paths) {
                out.push(path);
            }
            continue;
        }
        if !visited.insert(module.clone()) {
            continue;
        }
        stack.push((module.clone(), true));
        let Some(path) = clean_olean::find_module_olean(&module, search_paths) else {
            continue;
        };
        let Ok(bytes) = std::fs::read(&path) else {
            continue;
        };
        let Ok(imports) = parse_imports_only(&bytes) else {
            continue;
        };
        for import in imports {
            stack.push((import.module_name, false));
        }
    }
    out
}

/// The REAL priorities, read from the shipped `.olean`s' serialized
/// `InstanceEntry` records — never from a Lean source attribute.
///
/// Returns (name → priority, total entries seen, undecoded entry count).
fn lean_side(search_paths: &[PathBuf]) -> (BTreeMap<String, u32>, usize, usize, usize) {
    let modules = closure_modules(search_paths);
    let modules_walked = modules.len();
    let mut priorities: BTreeMap<String, u32> = BTreeMap::new();
    let mut entries = 0usize;
    let mut undecoded = 0usize;
    for path in modules {
        let Ok(bytes) = std::fs::read(&path) else {
            continue;
        };
        // Types-only: the priorities live in the extension array, so the
        // (expensive) value reconstruction is pure cost here.
        let Ok(module) = clean_olean::parse_module_types_only(&bytes) else {
            continue;
        };
        for ext in &module.entries {
            // Key on the extension NAME, not on "did we decode an Instance
            // here": an instance extension whose entries ALL failed to decode
            // has an empty `entries` and a nonzero `undecoded_entries`, and
            // that is exactly the case that must not be silently skipped.
            if ext.extension_name != LEAN_INSTANCE_EXTENSION {
                continue;
            }
            undecoded += ext.undecoded_entries;
            for entry in &ext.entries {
                if let ParsedExtensionEntry::Instance(inst) = entry {
                    entries += 1;
                    priorities.insert(
                        inst.instance_name.clone(),
                        u32::try_from(inst.priority).unwrap_or(u32::MAX),
                    );
                }
            }
        }
    }
    (priorities, entries, undecoded, modules_walked)
}

fn compute_census(search_paths: &[PathBuf]) -> Census {
    let clean = clean_side();
    let (lean, lean_entries, undecoded, modules_walked) = lean_side(search_paths);

    let mut rows: Vec<Row> = clean
        .iter()
        .filter_map(|(name, (class, clean_priority))| {
            let lean_priority = *lean.get(name)?;
            Some(Row {
                name: name.clone(),
                class: class.clone(),
                clean_priority: *clean_priority,
                lean_priority,
                mismatch: *clean_priority != lean_priority,
            })
        })
        .collect();
    rows.sort_by(|a, b| a.name.cmp(&b.name));

    let mismatched = rows.iter().filter(|r| r.mismatch).count();
    Census {
        generated_by: format!(
            "{UPDATE_ENV_VAR}=1 cargo test --offline --release -p clean-olean \
             --test prelude_instance_priority_census"
        ),
        import_root: IMPORT_ROOT.to_owned(),
        totals: Totals {
            prelude_instances: clean.len(),
            lean_instance_entries: lean_entries,
            colliding: rows.len(),
            mismatched,
            modules_walked,
            undecoded_instance_entries: undecoded,
        },
        rows,
    }
}

// ---------------------------------------------------------------------------
// Lane 1 — artifact self-consistency + ratchet (no toolchain)
// ---------------------------------------------------------------------------

#[test]
fn priority_census_artifact_is_self_consistent_and_ratcheted() {
    let census: Census = read_json(CENSUS_REL);
    let ratchet: Ratchet = read_json(RATCHET_REL);

    assert_eq!(
        census.totals.colliding,
        census.rows.len(),
        "{CENSUS_REL}: totals.colliding must equal the number of listed rows"
    );
    assert_eq!(
        census.totals.mismatched,
        census.rows.iter().filter(|r| r.mismatch).count(),
        "{CENSUS_REL}: totals.mismatched must equal the number of mismatch rows"
    );
    for row in &census.rows {
        assert_eq!(
            row.mismatch,
            row.clean_priority != row.lean_priority,
            "{CENSUS_REL}: row {} flags mismatch={} but {} vs {}",
            row.name,
            row.mismatch,
            row.clean_priority,
            row.lean_priority
        );
    }

    // (1) Mismatches are flat-or-down.
    assert!(
        census.totals.mismatched <= ratchet.baseline_mismatched,
        "instance-priority ratchet BROKEN: mismatched hand-registrations rose to {} \
         (baseline {}). A guessed priority that disagrees with Lean's `.olean` survives \
         the import forever and reorders `synthInstance` candidates — i.e. changes the \
         shape of elaborated terms. Do NOT raise the baseline: register Lean's priority.",
        census.totals.mismatched,
        ratchet.baseline_mismatched
    );

    // (2) THE DENOMINATOR MAY NOT SHRINK. Without this the class could be
    //     "fixed" by deleting hand-registrations until nothing is measured.
    assert!(
        census.totals.colliding >= ratchet.baseline_colliding,
        "instance-priority ratchet BROKEN: the measured denominator SHRANK, {} -> {}. \
         Fewer hand-registered instances collide with Lean than before, so the census \
         covers less than it did. Deleting rows is not a fix — if a registration was \
         genuinely retired, lower baseline_colliding in the SAME commit and say why.",
        ratchet.baseline_colliding,
        census.totals.colliding
    );
    assert!(
        census.totals.prelude_instances >= ratchet.baseline_prelude_instances,
        "instance-priority ratchet BROKEN: the hand-registered instance surface SHRANK, \
         {} -> {}. See baseline_colliding above.",
        ratchet.baseline_prelude_instances,
        census.totals.prelude_instances
    );

    // (3) Every pinned name is still measured.
    let live: BTreeSet<&str> = census.rows.iter().map(|r| r.name.as_str()).collect();
    let vanished: Vec<&str> = ratchet
        .known_colliding
        .iter()
        .map(String::as_str)
        .filter(|n| !live.contains(n))
        .collect();
    assert!(
        vanished.is_empty(),
        "instance-priority ratchet BROKEN: pinned names are no longer measured: {vanished:?}. \
         They must keep appearing in {CENSUS_REL} so their priority stays checked."
    );

    // (4) A NEW mismatch fails even at a flat count (one fixed, one introduced).
    let allowed: BTreeSet<&str> = ratchet
        .known_mismatched
        .iter()
        .map(String::as_str)
        .collect();
    let unexpected: Vec<&str> = census
        .rows
        .iter()
        .filter(|r| r.mismatch)
        .map(|r| r.name.as_str())
        .filter(|n| !allowed.contains(n))
        .collect();
    assert!(
        unexpected.is_empty(),
        "instance-priority ratchet BROKEN: NEW mismatched hand-registrations {unexpected:?}. \
         Read the priority off the shipped `.olean` (never off a Lean source attribute — \
         `@[default_instance 100]` is a DIFFERENT table) and register that value."
    );
}

// ---------------------------------------------------------------------------
// Lane 2 — the Clean side of the artifact is current (no toolchain)
// ---------------------------------------------------------------------------

#[test]
fn priority_census_clean_side_is_current() {
    let census: Census = read_json(CENSUS_REL);
    let clean = clean_side();

    let mut drifted = Vec::new();
    for row in &census.rows {
        match clean.get(&row.name) {
            None => drifted.push(format!("{}: no longer registered by the prelude", row.name)),
            Some((class, priority)) => {
                if *priority != row.clean_priority {
                    drifted.push(format!(
                        "{}: prelude now registers priority {} (census says {})",
                        row.name, priority, row.clean_priority
                    ));
                }
                if class != &row.class {
                    drifted.push(format!(
                        "{}: prelude now files it under {class} (census says {})",
                        row.name, row.class
                    ));
                }
            }
        }
    }
    assert!(
        drifted.is_empty(),
        "{CENSUS_REL} is stale against the live prelude:\n  {}\nRegenerate with \
         {UPDATE_ENV_VAR}=1 (needs a Lean toolchain).",
        drifted.join("\n  ")
    );
    assert_eq!(
        clean.len(),
        census.totals.prelude_instances,
        "{CENSUS_REL}: totals.prelude_instances is stale ({} live)",
        clean.len()
    );
}

// ---------------------------------------------------------------------------
// Lane 3 — the Lean side still matches a real toolchain (release only)
// ---------------------------------------------------------------------------

#[test]
fn priority_census_matches_real_lean_olean() {
    if cfg!(debug_assertions) && std::env::var(UPDATE_ENV_VAR).is_err() {
        eprintln!("Skipping: release-only lane (walks the whole `Init` closure).");
        return;
    }
    let Some(search_paths) = olean_search_paths() else {
        eprintln!("Skipping: no Lean toolchain with Init.olean on this machine.");
        return;
    };

    let fresh = compute_census(&search_paths);

    if std::env::var(UPDATE_ENV_VAR).is_ok() {
        let path = repo_root().join(CENSUS_REL);
        std::fs::write(
            &path,
            serde_json::to_string_pretty(&fresh).expect("census serializes") + "\n",
        )
        .unwrap_or_else(|e| panic!("cannot write {}: {e}", path.display()));
        eprintln!(
            "UPDATED {CENSUS_REL}: colliding={} mismatched={} (of {} prelude instances, \
             {} Lean entries over {} modules)",
            fresh.totals.colliding,
            fresh.totals.mismatched,
            fresh.totals.prelude_instances,
            fresh.totals.lean_instance_entries,
            fresh.totals.modules_walked
        );
        for row in fresh.rows.iter().filter(|r| r.mismatch) {
            eprintln!(
                "  MISMATCH {:<44} clean={:<6} lean={}",
                row.name, row.clean_priority, row.lean_priority
            );
        }
        return;
    }

    let recorded: Census = read_json(CENSUS_REL);
    assert_eq!(
        recorded.totals.undecoded_instance_entries, 0,
        "{CENSUS_REL}: {} InstanceEntry slots failed to decode — the Lean side is \
         UNDER-measured and a mismatch could hide in the gap",
        recorded.totals.undecoded_instance_entries
    );

    let fresh_by_name: BTreeMap<&str, &Row> =
        fresh.rows.iter().map(|r| (r.name.as_str(), r)).collect();
    let mut drifted = Vec::new();
    for row in &recorded.rows {
        match fresh_by_name.get(row.name.as_str()) {
            None => drifted.push(format!("{}: no longer a collision", row.name)),
            Some(live) if live.lean_priority != row.lean_priority => drifted.push(format!(
                "{}: `.olean` now serializes priority {} (census says {})",
                row.name, live.lean_priority, row.lean_priority
            )),
            Some(_) => {}
        }
    }
    let new_rows: Vec<&str> = fresh
        .rows
        .iter()
        .map(|r| r.name.as_str())
        .filter(|n| !recorded.rows.iter().any(|r| r.name == *n))
        .collect();
    assert!(
        drifted.is_empty() && new_rows.is_empty(),
        "{CENSUS_REL} is stale against the real toolchain:\n  {}\n  new collisions: \
         {new_rows:?}\nRegenerate with {UPDATE_ENV_VAR}=1.",
        drifted.join("\n  ")
    );
}

// ---------------------------------------------------------------------------
// Lane 4 — the STRUCTURAL fix (release only)
// ---------------------------------------------------------------------------

/// After importing a real Lean environment on top of the prelude, **no**
/// hand-registered instance may keep a priority that Lean's `.olean`
/// contradicts.
///
/// This is the structural retirement of the whole defect class: import adopts
/// Lean's serialized priority for an already-registered instance instead of
/// letting first-writer-wins freeze Clean's guess. Row-by-row corrections to
/// the prelude (which lane 1 ratchets) then only matter for environments that
/// never import — but this lane is what makes a future wrong guess harmless.
#[test]
fn import_adopts_lean_priority_for_hand_registered_instances() {
    if cfg!(debug_assertions) {
        eprintln!("Skipping: release-only lane (imports the whole `Init` closure).");
        return;
    }
    let Some(search_paths) = olean_search_paths() else {
        eprintln!("Skipping: no Lean toolchain with Init.olean on this machine.");
        return;
    };

    let before = clean_side();
    let mut env = Environment::with_prelude();
    clean_olean::load_module_with_deps(&mut env, IMPORT_ROOT, &search_paths)
        .unwrap_or_else(|e| panic!("importing {IMPORT_ROOT} must succeed: {e}"));

    let (lean, _, _, _) = lean_side(&search_paths);
    let after: BTreeMap<String, u32> = env
        .instances()
        .map(|i| (i.name.to_string(), i.priority))
        .collect();

    let mut residual = Vec::new();
    for (name, (_, guessed)) in &before {
        let Some(real) = lean.get(name) else {
            continue; // Clean-only name: nothing to contradict it.
        };
        let live = after.get(name).copied().unwrap_or(*guessed);
        if live != *real {
            residual.push(format!(
                "{name}: guessed {guessed}, Lean serializes {real}, environment kept {live}"
            ));
        }
    }
    residual.sort();
    assert!(
        residual.is_empty(),
        "import did NOT adopt Lean's serialized instance priorities:\n  {}\nThe adoption \
         path is `register_real_instance_entries` in \
         crates/clean-olean/src/import/load_register.rs.",
        residual.join("\n  ")
    );
}
