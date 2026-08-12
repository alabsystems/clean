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
//!   `Codata.*` constant (sentinel absent) is refused by an explicit
//!   pre-scan — registration's metadata-only tolerance for existing names
//!   means the kernel's duplicate rejection alone cannot be relied on.

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

/// Sentinel constant: present iff the seed library has been injected.
const SEED_SENTINEL: &str = "Codata.IMIntl";

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

/// Inject the `Codata.*` M-type seed library into `env` if absent.
///
/// Idempotent (keyed on [`SEED_SENTINEL`]), transactional (candidate-clone
/// swap), fail-closed (first failing declaration aborts with its error and
/// leaves `env` untouched). Call this ONLY from codata elaboration paths —
/// never from the default entry point.
pub fn ensure_codata_seeds(env: &mut Environment) -> Result<(), ElabError> {
    if env
        .get_const(&clean_kernel::Name::from_string(SEED_SENTINEL))
        .is_some()
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
        .map(|c| c.name.to_string())
        .find(|n| n.starts_with("Codata."))
    {
        return Err(ElabError::Unsupported {
            feature: format!(
                "codata seed: the Codata namespace is reserved for the seed \
                 library, but `{occupied}` already exists (and the seed \
                 sentinel `{SEED_SENTINEL}` does not) — refusing to seed"
            ),
        });
    }
    let src = seed_source()?;
    let decls = clean_parser::parse_file(&src).map_err(|e| ElabError::Unsupported {
        feature: format!("codata seed: embedded source failed to parse: {e:?}"),
    })?;
    let mut candidate = env.clone();
    for (i, decl) in decls.iter().enumerate() {
        crate::elaborate_decl_and_register(&mut candidate, decl).map_err(|e| {
            ElabError::Unsupported {
                feature: format!(
                    "codata seed: declaration {i} failed to elaborate/kernel-check \
                     (env left untouched): {e:?}"
                ),
            }
        })?;
    }
    *env = candidate;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::Name;

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
            .filter(|c| c.name.to_string().starts_with("Codata."))
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
