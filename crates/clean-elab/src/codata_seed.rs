// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Lazy `Codata.*` seed library for the codata command (R3.1 of
//! `designs/2026-08-06-indexed-m-codata.md`, per the binding verifier
//! amendments in `designs/2026-07-29-rocq-features-into-clean.md` §A).
//!
//! The seed is the GENERIC indexed M-type core — approximation tower,
//! destructor (head + coherent child), constructor, corecursor, and the
//! `rfl` computation laws — taken VERBATIM from the gate-checked
//! graduation source, now crate-local at `crates/clean-elab/data/MTypeIndexedPoly2.lean`
//! (moved from `data/graduation/clean-mtype/proof/` so the compile-time seed ships
//! with the crate; the rest of the graduation tree stays private)
//! (the `.{u, v}` TWO-UNIVERSE sibling's generic section, before the
//! capstone demos: index `Type v`, families `Type u`, carriers at
//! `Type (max u v)` — the seed shape indexed codata needs. Monomorphic
//! codata instantiates it at `u := v := 0`, the plain `.{u}` lane at
//! `v := u`, both through fresh level metas with the solver's max
//! normalization collapsing `max u u`/`max u 0`) and wrapped in
//! `namespace Codata`. Sourcing the text from the graduation file at
//! compile time means the seed can never drift from what
//! `scripts/mtype_green.sh` certifies.
//!
//! Binding rules honored here:
//! - **Lazy, on first use only**: nothing calls [`ensure_codata_seeds`] on
//!   the default elaboration path — the default env gains zero constants
//!   (`test_codata_seed_default_env_untouched`). The caller is the codata
//!   elaboration arm, never the entry point.
//! - **Full `add_decl` only**: every seed declaration goes through
//!   [`crate::elaborate_decl_and_register`], i.e. the ordinary
//!   parse → elaborate → kernel-check pipeline. No `add_decl_structural`,
//!   no `add_decl_unchecked`, so the unchecked-decl ratchet mechanically
//!   holds.
//! - **Transactional**: seeds elaborate into a candidate clone of the env;
//!   the swap happens only after every declaration lands. A mid-seed
//!   failure leaves the caller's env byte-identical.
//! - **Collision-loud**: the `Codata.` namespace is reserved. A foreign
//!   `Codata.*` constant (seed witnesses absent) is refused by an explicit
//!   pre-scan — registration's metadata-only tolerance for existing names
//!   means the kernel's duplicate rejection alone cannot be relied on.
//!   Idempotence is keyed on ALL of [`SEED_WITNESSES`]: keying it on the
//!   sentinel alone let a single squatted `def Codata.IMIntl` short-circuit
//!   the pre-scan and leave the namespace open.

use crate::ElabError;
use clean_kernel::Environment;

/// The graduation proof source this seed is cut from (compile-time embed;
/// workspace-internal path, resolved relative to this crate's manifest).
const MTYPE_INDEXED_SRC: &str = include_str!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/data/MTypeIndexedPoly2.lean"
));

/// Marker separating the generic M-type core from the capstone demos in
/// the graduation source. Everything BEFORE the marker is the seed.
const CAPSTONE_MARKER: &str = "-- ── R2 capstone A";

/// Sentinel constant: named in diagnostics as the marker of an injected seed.
const SEED_SENTINEL: &str = "Codata.IMIntl";

/// Constants that must ALL be present for an environment to count as seeded.
///
/// The sentinel alone is not sufficient evidence, and treating it as such was a
/// real hole: `Codata.IMIntl` is an ordinary name a user can define, and the
/// idempotence check short-circuited on it BEFORE the namespace pre-scan ran.
/// A single squatted `def Codata.IMIntl` therefore turned seeding into a silent
/// no-op and left the whole reserved namespace open.
///
/// Requiring several witnesses closes that: a partial occupation now falls
/// through to the pre-scan below, which refuses loudly. It is cheap
/// defence-in-depth rather than a proof of authenticity — the load-bearing gate
/// for recognition is carrier provenance (`Environment::is_codata_carrier`),
/// which only the `codata` command sets.
const SEED_WITNESSES: &[&str] = &[SEED_SENTINEL, "Codata.ucorec", "Codata.IMcorec"];

/// Start marker of the COINDUCTION section (see [`ensure_codata_coind_seeds`]).
///
/// The section is a mid-file SLICE, not a prefix, and that is the whole point:
/// a prefix cut extended to cover `iM_coind` would drag the capstone demo layer
/// along with it, taking seed injection from 0.75 s to 141.4 s (MEASURED —
/// `ibind_tau_child` and `ibind_vis_child` alone are 138 s of that). The slice
/// costs +2.15 s because the coinduction block references NOTHING from the demo
/// layer. Both markers below are unique in the source and sit on blank-line
/// declaration boundaries, so slicing needs no edit to the gate-pinned corpus.
const COIND_START_MARKER: &str = "-- ── R4: bisimilarity IS equality in the tower model ──";

/// End marker of the coinduction section (exclusive).
const COIND_END_MARKER: &str = "-- ── generic-index corecursor observation laws";

/// Witnesses for the coinduction section's fast idempotence path.
const COIND_WITNESSES: &[&str] = &["Codata.iM_coind", "Codata.iM_ext", "Codata.icastM"];

/// Every constant the coinduction section defines, unqualified.
///
/// Hardcoded rather than derived because it is the section's collision pre-scan
/// (the base section's whole-namespace scan cannot be reused: once the base is
/// injected, `Codata.*` is populated by construction, so a namespace-wide scan
/// would make the second section an unconditional refusal). Drift in either
/// direction is caught by `test_coind_section_names_are_exactly_the_section`,
/// which pins the constant delta to this list's length.
const COIND_NAMES: &[&str] = &[
    "isubtype_ext",
    "iM_ext",
    "iM_bisim_of_eq",
    "icastM",
    "icastM_val",
    "isigma_ext",
    "iunit_eq",
    "ival_zero_eq",
    "icoind_b2",
    "icoind_b1",
    "icoind_elab",
    "icoind_pos2",
    "icoind_pos1",
    "icoind_q2",
    "icoind_p1",
    "icoind_ih_eq",
    "icoind_s1",
    "icoind_s2",
    "icoind_s3",
    "icoind_s4",
    "icoind_s5a",
    "icoind_s5b",
    "icoind_s6",
    "icoind_s7",
    "icoind_s8",
    "snd12",
    "snd34",
    "snd678",
    "icoind_snd",
    "iM_coind_val",
    "iM_coind",
];

/// The `Codata.*`-namespaced seed source (generic core only).
fn seed_source() -> Result<String, ElabError> {
    let cut = MTYPE_INDEXED_SRC
        .find(CAPSTONE_MARKER)
        .ok_or_else(|| ElabError::Unsupported {
            feature: "codata seed: capstone marker missing from MTypeIndexed.lean — \
                      the graduation source layout changed; update codata_seed.rs"
                .to_string(),
        })?;
    let core = MTYPE_INDEXED_SRC[..cut].trim_end();
    Ok(format!("namespace Codata\n\n{core}\n\nend Codata\n"))
}

/// The `Codata.*`-namespaced coinduction section source (mid-file slice).
fn coind_source() -> Result<String, ElabError> {
    let start =
        MTYPE_INDEXED_SRC
            .find(COIND_START_MARKER)
            .ok_or_else(|| ElabError::Unsupported {
                feature: "codata seed: coinduction start marker missing from \
                          MTypeIndexedPoly2.lean — the graduation source layout \
                          changed; update codata_seed.rs"
                    .to_string(),
            })?;
    let end = MTYPE_INDEXED_SRC
        .find(COIND_END_MARKER)
        .ok_or_else(|| ElabError::Unsupported {
            feature: "codata seed: coinduction end marker missing from \
                      MTypeIndexedPoly2.lean — the graduation source layout \
                      changed; update codata_seed.rs"
                .to_string(),
        })?;
    if end <= start {
        return Err(ElabError::Unsupported {
            feature: "codata seed: coinduction markers are out of order in \
                      MTypeIndexedPoly2.lean — the graduation source layout changed"
                .to_string(),
        });
    }
    let body = MTYPE_INDEXED_SRC[start..end].trim_end();
    Ok(format!("namespace Codata\n\n{body}\n\nend Codata\n"))
}

/// Parse `src` and register every declaration into `env`, transactionally.
///
/// Shared by both sections: elaboration goes through the ordinary
/// [`crate::elaborate_decl_and_register`] pipeline (full `add_decl`, so the
/// unchecked-decl ratchet holds), into a candidate clone that is swapped in only
/// after the LAST declaration lands. `what` names the section in diagnostics.
fn inject_section(env: &mut Environment, src: &str, what: &str) -> Result<(), ElabError> {
    let decls = clean_parser::parse_file(src).map_err(|e| ElabError::Unsupported {
        feature: format!(
            "codata seed ({what}): embedded source failed to parse: {}",
            e
        ),
    })?;
    let mut candidate = env.clone();
    for (i, decl) in decls.iter().enumerate() {
        let result = crate::elaborate_decl_and_register(&mut candidate, decl).map_err(|e| {
            ElabError::Unsupported {
                feature: format!(
                    "codata seed ({what}): declaration {i} failed to elaborate/kernel-check \
                     (env left untouched): {}",
                    e
                ),
            }
        })?;
        fn first_failure(result: &crate::ElabResult) -> Option<&ElabError> {
            match result {
                crate::ElabResult::Failed { error, .. } => Some(error),
                crate::ElabResult::Diagnosed { diagnostics, .. } => {
                    diagnostics.first().map(|d| &d.error)
                }
                crate::ElabResult::Multiple(results) => results.iter().find_map(first_failure),
                _ => None,
            }
        }
        if let Some(error) = first_failure(&result) {
            return Err(ElabError::Unsupported {
                feature: format!(
                    "codata seed ({what}): declaration {i} contains a failed declaration \
                     (env left untouched): {error}"
                ),
            });
        }
    }
    *env = candidate;
    Ok(())
}

/// Inject the `Codata.*` M-type seed library into `env` if absent.
///
/// Idempotent (keyed on ALL of [`SEED_WITNESSES`], not the sentinel alone —
/// see that constant for why), transactional (candidate-clone
/// swap), fail-closed (first failing declaration aborts with its error and
/// leaves `env` untouched). Call this ONLY from codata elaboration paths —
/// never from the default entry point.
fn in_seed_namespace(name: &clean_kernel::Name) -> bool {
    let prefix = clean_kernel::Name::anon().str("Codata");
    let mut current = name;
    loop {
        current = match current.inner() {
            clean_kernel::name::NameInner::Anon => return false,
            clean_kernel::name::NameInner::Str(parent, _)
            | clean_kernel::name::NameInner::Num(parent, _) => parent,
        };
        if current == &prefix {
            return true;
        }
    }
}

pub(crate) fn ensure_codata_seeds(env: &mut Environment) -> Result<(), ElabError> {
    // Already seeded iff EVERY witness is present. A partial occupation (some
    // witnesses, or a squatted sentinel alone) deliberately falls through to
    // the pre-scan, which refuses.
    if SEED_WITNESSES
        .iter()
        .all(|n| env.get_const(&clean_kernel::Name::from_string(n)).is_some())
    {
        return Ok(());
    }
    // Collision pre-scan: the `Codata.` namespace is reserved for this seed
    // library. A foreign/partial `Codata.*` constant with the sentinel absent
    // means a collision or a half-seeded env — refuse loudly rather than let
    // registration's metadata-only tolerance for existing names silently
    // shadow either side.
    if let Some(occupied) = env
        .constants()
        .map(|c| c.name.clone())
        .find(in_seed_namespace)
    {
        return Err(ElabError::Unsupported {
            feature: format!(
                "codata seed: the Codata namespace is reserved for the seed \
                 library, but `{occupied}` already exists (and the seed \
                 sentinel `{SEED_SENTINEL}` does not) — refusing to seed"
            ),
        });
    }
    inject_section(env, &seed_source()?, "core")
}

/// Inject the `Codata.*` COINDUCTION section (tower extensionality, `icastM`,
/// and the `iM_coind` principle) on top of the core seed.
///
/// Call this only from paths that actually need coinduction — the coinductive
/// companion tier of the variant-codata surface. Plain codata declaration must
/// keep calling [`ensure_codata_seeds`] alone, so the +31 declarations / +2.15 s
/// are paid on demand and never by a user who only wants constructors and
/// destructors.
///
/// Ensures the core section first (the slice depends on it), then layers the
/// coinduction slice with the same idempotence / transactional / fail-closed
/// discipline.
pub(crate) fn ensure_codata_coind_seeds(env: &mut Environment) -> Result<(), ElabError> {
    ensure_codata_seeds(env)?;
    if COIND_WITNESSES
        .iter()
        .all(|n| env.get_const(&clean_kernel::Name::from_string(n)).is_some())
    {
        return Ok(());
    }
    // Collision pre-scan over THIS SECTION'S OWN names only. The base section's
    // whole-namespace scan is deliberately not reused here: the base seed is
    // present by the time this runs, so `Codata.*` is populated by construction
    // and a namespace-wide scan would refuse unconditionally. Scanning the
    // section's own names still gives the load-bearing guarantee — nothing
    // shadows, and is not shadowed by, a seed constant.
    if let Some(occupied) = COIND_NAMES
        .iter()
        .map(|n| format!("Codata.{n}"))
        .find(|n| env.get_const(&clean_kernel::Name::from_string(n)).is_some())
    {
        return Err(ElabError::Unsupported {
            feature: format!(
                "codata seed: the coinduction section's name `{occupied}` is already \
                 taken (and its witnesses are absent) — refusing to seed"
            ),
        });
    }
    inject_section(env, &coind_source()?, "coinduction")
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::Name;

    #[test]
    fn nested_seed_failure_rolls_back_successful_siblings() {
        let mut env = Environment::with_prelude();
        let before = env.num_constants();
        let result = inject_section(
            &mut env,
            "namespace Codata\ndef sibling : Nat := 0\ndef bad : Nat := true\nend Codata",
            "failure-control",
        );
        assert!(result.is_err(), "nested failed leaf must abort injection");
        assert_eq!(env.num_constants(), before);
        assert!(env
            .get_const(&Name::from_string("Codata.sibling"))
            .is_none());
    }

    /// The default elaboration path must not grow the env: seeds are lazy.
    #[test]
    fn test_codata_seed_default_env_untouched() {
        let mut env = Environment::with_prelude();
        let decls =
            clean_parser::parse_file("def seedProbe : Nat := Nat.zero").expect("should parse");
        crate::elaborate_decl_and_register(&mut env, &decls[0]).expect("plain def must elaborate");
        assert!(
            env.get_const(&Name::from_string(SEED_SENTINEL)).is_none(),
            "no Codata.* constant may appear without an explicit codata use"
        );
        let codata_consts = env
            .constants()
            .filter(|c| in_seed_namespace(&c.name))
            .count();
        assert_eq!(
            codata_consts, 0,
            "default env must carry zero Codata.* constants"
        );
    }

    /// First use injects the full library through the checked pipeline.
    #[test]
    fn test_codata_seed_injects_on_demand() {
        let mut env = Environment::with_prelude();
        let before = env.num_constants();
        ensure_codata_seeds(&mut env).expect("seed injection must succeed");
        for name in [
            "Codata.isigmaStep",
            "Codata.iapprox",
            "Codata.IMIntl",
            "Codata.IMhead",
            "Codata.IMchild",
            "Codata.IMdest",
            "Codata.IMmk",
            "Codata.IMcorec",
            "Codata.iIMhead_corec",
            "Codata.iIMdest_corec",
        ] {
            assert!(
                env.get_const(&Name::from_string(name)).is_some(),
                "seed constant {name} must register"
            );
        }
        assert!(
            env.num_constants() > before,
            "seed injection must add constants"
        );
    }

    /// Second call is a no-op (sentinel-keyed idempotence).
    #[test]
    fn test_codata_seed_idempotent() {
        let mut env = Environment::with_prelude();
        ensure_codata_seeds(&mut env).expect("first injection must succeed");
        let after_first = env.num_constants();
        ensure_codata_seeds(&mut env).expect("second call must be a no-op");
        assert_eq!(
            env.num_constants(),
            after_first,
            "idempotent re-entry must not change the env"
        );
    }

    /// Squatting the SENTINEL is refused, not silently honored.
    ///
    /// This is an adversarial review's finding, as its own test. The
    /// idempotence check used to short-circuit on the sentinel alone, BEFORE
    /// the namespace pre-scan — and `Codata.IMIntl` is an ordinary
    /// user-definable name. So a single squatted definition made seeding a
    /// silent no-op and left the entire reserved namespace open, while every
    /// existing test stayed green because they all squat a NON-sentinel name.
    ///
    /// The idempotence check now requires several witnesses, so a lone sentinel
    /// falls through to the pre-scan and is refused like any other collision.
    #[test]
    fn test_squatting_the_sentinel_alone_is_refused() {
        let mut env = Environment::with_prelude();
        let src = format!("def {SEED_SENTINEL} : Nat := Nat.zero");
        let decls = clean_parser::parse_file(&src).expect("should parse");
        crate::elaborate_decl_and_register(&mut env, &decls[0]).expect("user def must elaborate");
        let before = env.num_constants();
        assert!(
            ensure_codata_seeds(&mut env).is_err(),
            "a squatted sentinel must NOT be mistaken for an injected seed"
        );
        assert_eq!(
            env.num_constants(),
            before,
            "failed seeding must leave the env byte-identical (transactional)"
        );
    }

    /// The coinduction section is NOT injected by the plain core seed.
    ///
    /// This is the cost guarantee as a test: a user who declares codata without
    /// asking for a coinductive companion must not pay the +31 declarations.
    #[test]
    fn test_coind_section_is_not_in_the_core_seed() {
        let mut env = Environment::with_prelude();
        ensure_codata_seeds(&mut env).expect("core seed must inject");
        for name in COIND_WITNESSES {
            assert!(
                env.get_const(&Name::from_string(name)).is_none(),
                "{name} must NOT be present after a core-only seed"
            );
        }
    }

    /// The coinduction slice injects on demand, and `COIND_NAMES` is EXACTLY
    /// the set it defines.
    ///
    /// Pinning the delta to the list length catches drift in both directions:
    /// a declaration added to the slice upstream (delta > len) and one removed
    /// or renamed (a missing name). The list is the section's collision
    /// pre-scan, so a silent divergence would silently weaken that scan.
    #[test]
    fn test_coind_section_names_are_exactly_the_section() {
        let mut env = Environment::with_prelude();
        ensure_codata_seeds(&mut env).expect("core seed must inject");
        let before = env.num_constants();
        ensure_codata_coind_seeds(&mut env).expect("coinduction section must inject");
        for n in COIND_NAMES {
            assert!(
                env.get_const(&Name::from_string(&format!("Codata.{n}")))
                    .is_some(),
                "coinduction constant Codata.{n} must register"
            );
        }
        assert_eq!(
            env.num_constants() - before,
            COIND_NAMES.len(),
            "COIND_NAMES must list exactly the constants the slice defines — \
             a mismatch means the graduation source drifted and the section's \
             collision pre-scan is now incomplete"
        );
    }

    /// Second call to the coinduction section is a no-op.
    #[test]
    fn test_coind_section_idempotent() {
        let mut env = Environment::with_prelude();
        ensure_codata_coind_seeds(&mut env).expect("first injection must succeed");
        let after_first = env.num_constants();
        ensure_codata_coind_seeds(&mut env).expect("second call must be a no-op");
        assert_eq!(
            env.num_constants(),
            after_first,
            "idempotent re-entry must not change the env"
        );
    }

    /// Squatting a coinduction-section name is refused, transactionally —
    /// and the refusal must survive the base seed already being present.
    #[test]
    fn test_coind_section_collision_is_loud_and_transactional() {
        let mut env = Environment::with_prelude();
        ensure_codata_seeds(&mut env).expect("core seed must inject");
        let decls = clean_parser::parse_file("def Codata.iM_bisim_of_eq : Nat := Nat.zero")
            .expect("should parse");
        crate::elaborate_decl_and_register(&mut env, &decls[0]).expect("user def must elaborate");
        let before = env.num_constants();
        assert!(
            ensure_codata_coind_seeds(&mut env).is_err(),
            "a squatted coinduction name must make seeding fail loudly"
        );
        assert_eq!(
            env.num_constants(),
            before,
            "failed seeding must leave the env byte-identical (transactional)"
        );
    }

    /// A pre-existing colliding `Codata.*` name fails LOUD and leaves the
    /// env untouched (transactional candidate swap).
    #[test]
    fn test_codata_seed_collision_is_loud_and_transactional() {
        let mut env = Environment::with_prelude();
        // Occupy a non-sentinel seed name with a user def.
        let decls =
            clean_parser::parse_file("def Codata.IMhead : Nat := Nat.zero").expect("should parse");
        crate::elaborate_decl_and_register(&mut env, &decls[0]).expect("user def must elaborate");
        let before = env.num_constants();
        let err = ensure_codata_seeds(&mut env);
        assert!(
            err.is_err(),
            "colliding Codata.IMhead must make seeding fail loudly"
        );
        assert_eq!(
            env.num_constants(),
            before,
            "failed seeding must leave the env byte-identical (transactional)"
        );
    }
}
