// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! R142 (`docs/DECISIONS.md`) through the mathverse re-check lanes: a
//! declaration an artifact's authoritative part states with a value that the
//! load did not make resident with it (`replay_forged` README, pinned
//! `leanchecker` v4.30.0-rc2):
//!
//! - `ReplayStubMv` / `ReplayStubFv`: a private value Clean's converter cannot
//!   read (a metavariable, a free variable). rc 1 in both modes. Before R142
//!   the sharded worker counted the stub `axiom_accepted` and verified its user.
//! - `ReplayShadowStub`: a stub whose name and type an import holds as an
//!   axiom, over a private value the kernel refuses. rc 1 in both modes. Before
//!   R142 the sharded worker verified its user over the import's axiom, and
//!   every eager re-check load admitted `ReplayShadowStubUser` (default rc 0,
//!   `--fresh` rc 1).
//! - An eliding `stamp-verified` run dropped an import's completion value before
//!   the checked upgrade, and so stamped `ReplayStubRefusedDepUser`'s `srd_use`.

use super::*;

/// What a lane's refusal says of a value the load did not make resident.
fn needle(artifact: &str, name: &str) -> String {
    format!("`{artifact}` states `{name}` with a value the environment does not hold")
}

#[test]
fn test_sharded_verify_module_refuses_a_value_the_load_did_not_make_resident() {
    for (module, name, user) in [
        ("ReplayStubMv", "smv_f", "smv_u"),
        ("ReplayStubFv", "sfv_f", "sfv_u"),
        ("ReplayShadowStub", "sha_n", "sh_u"),
    ] {
        let r = sharded(module, 64);
        assert_eq!(
            (
                r.counts.kernel_verified,
                r.counts.axiom_accepted,
                r.counts.failed
            ),
            (0, 0, 2),
            "{module}: `{name}` is refused, never an accepted axiom, and `{user}` with it: {:?}",
            r.failures
        );
        let reason = |n: &str| {
            r.failures
                .iter()
                .find(|(f, _)| f == n)
                .map(|(_, m)| m.clone())
                .unwrap_or_else(|| {
                    panic!("{module}: `{n}` must be a named failure: {:?}", r.failures)
                })
        };
        assert!(
            reason(name).contains("did not make resident"),
            "{module}: `{name}`: {}",
            reason(name)
        );
        assert!(
            reason(user).contains(&format!("depends on `{name}`")),
            "{module}: `{user}`: {}",
            reason(user)
        );
    }
}

#[test]
fn test_lanes_refuse_an_import_whose_value_the_load_did_not_make_resident() {
    let mut search = vec![fixtures()];
    search.extend(clean_olean::default_search_paths());
    let user = "ReplayShadowStubUser";
    let expected = needle("ReplayShadowStub", "sha_n");
    let mut problems: Vec<String> = refusal_problem(
        "sharded",
        user,
        crate::verify::sharded::verify_module(user, &search, 64).map(|r| r.kernel_verified_names),
        &expected,
    )
    .into_iter()
    .collect();
    for mode in STAMP_MODES {
        let lane = format!("stamp-verified {}", mode.unwrap_or("(default)"));
        problems.extend(refusal_problem(
            &lane,
            user,
            try_stamp(&[user], mode),
            &expected,
        ));
        // The module's own unreadable value: refused by name, or left unstamped.
        for (module, names) in [
            ("ReplayStubMv", ["smv_f", "smv_u"]),
            ("ReplayShadowStub", ["sha_n", "sh_u"]),
        ] {
            match try_stamp(&[module], mode) {
                Ok(stamped) => {
                    if names.iter().any(|n| stamped.contains(*n)) {
                        problems.push(format!("{lane} stamped {names:?} of {module}: {stamped:?}"));
                    }
                }
                Err(e) => {
                    let message = e.to_string();
                    if !names.iter().any(|n| message.contains(&format!("`{n}`"))) {
                        problems.push(format!(
                            "{lane} refused {module} without naming it: {message}"
                        ));
                    }
                }
            }
        }
    }
    // An eliding run checks an import's completion before it drops the value.
    problems.extend(refusal_problem(
        "stamp-verified --closure-elide=opaque-and-theorem",
        "ReplayStubRefusedDepUser",
        try_stamp(
            &["ReplayStubRefusedDepUser"],
            Some("--closure-elide=opaque-and-theorem"),
        ),
        "completes the value-free `srd_t` with a value the kernel refuses",
    ));
    assert_no_problems(&problems);
}
