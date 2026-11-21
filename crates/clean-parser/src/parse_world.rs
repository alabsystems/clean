// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Legacy release-order grammar models and the deliberate migration tripwire.
//!
//! Production parses select the shared `clean_kernel::LeanWorld`; old public
//! APIs default to its unchanged Oracle. Olean's source decision and the CLI
//! bind that grammar to the selected import library. The admitted 4.36 worlds
//! enable variable visibility after an exact release selection.
//!
//! Test-only synthetic tags still exercise the prefix-reader boundary. The
//! forall-row guard below requires an exact source decision for every registry
//! row, so an unqualified later release cannot inherit rc2's semantics.

/// The unchanged default world of the public parser APIs.
pub(crate) const ORACLE_WORLD: &str = clean_kernel::lean_world::LeanWorld::ORACLE.tag();

/// The first world whose `variable` command takes `public` / `private`
/// (lean4#15518).
pub(crate) const VARIABLE_VISIBILITY_SINCE: &str = "v4.36.0-rc1";

/// Whether `world` is `since` or a later release. A name either side does not
/// parse as `vMAJOR.MINOR.PATCH` with an optional `-rcN` answers `false`.
#[must_use]
pub(crate) fn world_at_least(world: &str, since: &str) -> bool {
    match (release_order(world), release_order(since)) {
        (Some(world), Some(since)) => world >= since,
        _ => false,
    }
}

/// `vMAJOR.MINOR.PATCH[-rcN]` as a tuple that orders releases: an `-rcN`
/// precedes its release, and `rc1` precedes `rc2`.
fn release_order(world: &str) -> Option<(u64, u64, u64, u64)> {
    let rest = world.strip_prefix('v')?;
    let (version, candidate) = match rest.split_once('-') {
        Some((version, pre)) => (version, Some(number(pre.strip_prefix("rc")?)?)),
        None => (rest, None),
    };
    let mut parts = version.split('.');
    let major = number(parts.next()?)?;
    let minor = number(parts.next()?)?;
    let patch = number(parts.next()?)?;
    if parts.next().is_some() {
        return None;
    }
    Some((major, minor, patch, candidate.unwrap_or(u64::MAX)))
}

/// A non-empty run of ASCII digits.
fn number(text: &str) -> Option<u64> {
    if text.is_empty() || !text.bytes().all(|b| b.is_ascii_digit()) {
        return None;
    }
    text.parse().ok()
}

#[cfg(test)]
mod tests {
    use super::*;

    const LEAN_TOOLCHAIN: &str = include_str!("../../../lean-toolchain");
    const LEAN_WORLDS: &str = include_str!("../../clean-olean/lean_worlds.tsv");

    /// `(world, state)` for every row of `lean_worlds.tsv`.
    fn world_rows() -> Vec<(&'static str, &'static str)> {
        LEAN_WORLDS
            .lines()
            .filter(|line| !line.starts_with('#') && !line.trim().is_empty())
            .map(|line| {
                let mut cols = line.split('\t');
                let world = cols.next().expect("a world column");
                let state = cols.next().expect("a state column");
                (world, state)
            })
            .collect()
    }

    #[test]
    fn test_world_at_least_orders_releases_and_candidates() {
        for (world, since, expected) in [
            ("v4.36.0-rc1", "v4.36.0-rc1", true),
            ("v4.36.0-rc2", "v4.36.0-rc1", true),
            ("v4.36.0", "v4.36.0-rc1", true),
            ("v4.37.0-rc1", "v4.36.0-rc1", true),
            ("v5.0.0", "v4.36.0-rc1", true),
            ("v4.35.0", "v4.36.0-rc1", false),
            ("v4.30.0-rc2", "v4.36.0-rc1", false),
            ("v4.30.0", "v4.36.0-rc1", false),
            ("v4.8.0", "v4.36.0-rc1", false),
            ("v4.36.0-rc1", "v4.36.0", false),
            // Names this module cannot order are never admitted.
            ("v4.36.0-nightly-2026-10-01", "v4.36.0-rc1", false),
            ("4.36.0", "v4.36.0-rc1", false),
            ("v4.36", "v4.36.0-rc1", false),
            ("v4.36.0.1", "v4.36.0-rc1", false),
            ("v4.+36.0", "v4.36.0-rc1", false),
            ("", "v4.36.0-rc1", false),
            ("v4.36.0", "", false),
        ] {
            assert_eq!(
                world_at_least(world, since),
                expected,
                "world_at_least({world:?}, {since:?})"
            );
        }
    }

    #[test]
    fn test_oracle_world_is_the_lean_toolchain_pin_and_the_oracle_row() {
        let pin = LEAN_TOOLCHAIN
            .trim()
            .strip_prefix("leanprover/lean4:")
            .expect("lean-toolchain names a leanprover/lean4 release");
        assert_eq!(ORACLE_WORLD, pin, "the parser's world is not the pin");
        let oracles: Vec<&str> = world_rows()
            .into_iter()
            .filter(|(_, state)| *state == "oracle")
            .map(|(world, _)| world)
            .collect();
        assert_eq!(
            oracles,
            vec![ORACLE_WORLD],
            "lean_worlds.tsv's oracle row is not the parser's world"
        );
    }

    /// Every registry row needs a closed source decision. The exact 4.36rc2
    /// world has native and genuine-Init source controls: its modifier has no
    /// effect. Earlier worlds keep refusing it. A new or unknown row trips
    /// here rather than inheriting rc2's semantics: lean4#15540 in a later
    /// release restricts private variables in public declarations.
    #[test]
    fn test_every_registered_world_has_an_explicit_variable_visibility_decision() {
        let rows = world_rows();
        assert!(!rows.is_empty(), "lean_worlds.tsv has no rows");
        for (world, state) in rows {
            let selected = world
                .parse::<clean_kernel::LeanWorld>()
                .unwrap_or_else(|error| {
                    panic!("{world} ({state}) needs a qualified source decision: {error}")
                });
            assert_eq!(
                selected.variable_visibility(),
                world_at_least(world, VARIABLE_VISIBILITY_SINCE),
                "{world} ({state}) has no matching `variable` visibility decision"
            );
        }
    }
}
