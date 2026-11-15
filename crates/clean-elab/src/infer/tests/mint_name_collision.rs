// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! U2 stage-3 deferral 1 — a user-written universe name that COLLIDES with a
//! minted `u_N` must still be a rigid parameter of its declaration.
//!
//! (`docs/analysis/u2-implementation-plan-2026-08-24.md` §3 stage 3, delta 3c,
//! first bullet. Stage 3 deferred a total `is_rigid_level_param` because there
//! was "no measured failure behind it today. Schedule it when one appears."
//! One appeared, 2026-08-26; these tests are it.)
//!
//! # The failure, measured before the fix (release binary at `9cd4f68f6`)
//!
//! ```text
//! def badAutoNamed  (β : Sort _) : Sort w   := Nat   FAIL  (correct)
//! def badAutoCollide(β : Sort _) : Sort u_0 := Nat   PASS  (the defect)
//! ```
//!
//! Same declaration, universe renamed `w` -> `u_0`. `ElabCtx::universe_params`
//! is the UNION of the rigid names and the MINTED ones, and the auto-bind path
//! tested membership in it to decide "already a parameter". The `Sort _` hole
//! minted `u_0` first, so the WRITTEN `u_0` took the not-a-parameter branch,
//! never reached the rigid set, and solved to `1` — the parameter vanished
//! (`@badAutoCollide.{0}` reported `expected: 0, actual: 1`), which is p30's
//! silent-monomorphization tell verbatim.
//!
//! `ElabCtx::level_param_role` replaces that membership test with the total
//! [`crate::level_role::LevelParamRole`] classification (Rigid / Minted /
//! Foreign, where `Minted = universe_params \ rigid`).
//!
//! # AMENDED 2026-08-26b — the collision is now UNCONSTRUCTIBLE
//!
//! Classification alone could not make the two levels DISTINCT (level identity
//! is `Level::Param(Name)`), so it resolved the clash by making both
//! occurrences one RIGID level. That closed the silent half and cost a
//! refusal Lean does not make, pinned as p49.
//!
//! Universe METAVARIABLES are now minted into a reserved namespace the surface
//! grammar cannot produce — `?u_0`, `?u_1`, …
//! ([`crate::level_mint::MINT_PREFIX`]) — so a written name and a minted one
//! are never the same string. p49 is a POSITIVE fixture as of that day, and
//! `test_mint_name_collision_overconstrains_independent_universes` below is
//! now `test_hole_and_written_universe_are_independent`.
//!
//! The role classification stays and stays tested: it is what makes the
//! auto-bind path correct for ANY name that is already a parameter, rather
//! than correct only while the two namespaces happen to be disjoint.
//!
//! # What is pinned here, and in what weight
//!
//! The refusal (p47) and — in equal weight, per the p21/p46 precedent — its
//! BOUNDARY (p48). A MUST_FAIL probe cannot tell a precise refusal from an
//! over-broad one: an elaborator that rejected every `u_N`-spelled universe,
//! or that made every level hole rigid, would satisfy p47 too. The same pairing
//! covers the reservation: p51 refuses a written mint name (reachable only
//! through a guillemet identifier) and p48's `guillemetUniverse` is the control
//! that keeps that refusal about the `?`-leading space rather than about
//! guillemets.
//!
//! The role classifier itself is pinned directly against a live `ElabCtx`, so
//! a future change that reintroduces the union as a rigidity proxy fails here
//! rather than only at a fixture.

use crate::{
    elaborate_decl_and_register_with_context, preprocess_decl_with_context, ElabResult, FileContext,
};
use clean_kernel::Environment;
use clean_parser::parse_file;

const FIXTURE_DIR: &str = "../../tests/fixtures/universes";

fn read_fixture(file: &str) -> String {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join(FIXTURE_DIR)
        .join(file);
    std::fs::read_to_string(&path)
        .unwrap_or_else(|e| panic!("fixture must exist at {}: {e}", path.display()))
}

/// Elaborate every declaration of `src` through the same
/// `preprocess` → `elaborate_with_context` pair `clean check` uses (the file
/// context is what carries `universe` commands). Returns
/// `(declaration name, verdict)` per leaf in source order.
fn elab_source(label: &str, src: &str) -> Vec<(String, Result<(), String>)> {
    let decls = parse_file(src).unwrap_or_else(|e| panic!("{label} must parse: {e}"));
    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();
    let mut verdicts = Vec::new();
    for decl in &decls {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        match elaborate_decl_and_register_with_context(&mut env, &processed, &mut file_ctx) {
            Ok(result) => {
                let mut leaves = Vec::new();
                result.leaf_decls(&mut leaves);
                for leaf in leaves {
                    match leaf {
                        ElabResult::Failed { name, error, .. } => {
                            verdicts.push((name.to_string(), Err(format!("{error:?}"))));
                        }
                        ElabResult::Theorem { name, .. } | ElabResult::Definition { name, .. } => {
                            verdicts.push((name.to_string(), Ok(())));
                        }
                        ElabResult::Skipped => {}
                        other => panic!("{label}: unexpected leaf {other:?}"),
                    }
                }
            }
            Err(error) => {
                let name = crate::preprocess_ext::decl_name(decl)
                    .map_or_else(|| format!("<decl {}>", verdicts.len()), ToString::to_string);
                verdicts.push((name, Err(format!("{error:?}"))));
            }
        }
    }
    verdicts
}

fn elab_fixture(file: &str) -> Vec<(String, Result<(), String>)> {
    elab_source(file, &read_fixture(file))
}

/// The exact fragment `scripts/u2_battery.sh` pins for p47.
const PINNED_FRAGMENT: &str = r#"TypeMismatch { expected: "Sort u_0", actual: "Type" }"#;

/// THE REGRESSION PIN. `def badAutoCollide (β : Sort _) : Sort u_0 := Nat`
/// monomorphizes a universe the source declares, so it must be refused —
/// identically to its `Sort w` rename, which is in the same fixture as the
/// control that makes the pair legible.
#[test]
fn test_written_universe_colliding_with_a_mint_is_still_rigid() {
    let verdicts = elab_fixture("p47_autobound_mint_name_collision_MUST_FAIL.lean");
    let names: Vec<&str> = verdicts.iter().map(|(n, _)| n.as_str()).collect();
    assert_eq!(
        names,
        ["badAutoNamed", "badAutoCollide"],
        "p47: declaration set moved — update the expected list deliberately"
    );
    assert!(
        verdicts[0].1.is_err(),
        "p47: the `Sort w` rename control must fail; it always did, and if it \
         stopped the collision line below proves nothing"
    );
    let err = verdicts[1]
        .1
        .as_ref()
        .expect_err("p47: `badAutoCollide` must be REFUSED — a written universe is a parameter whatever else shares its spelling");
    assert!(
        err.contains(PINNED_FRAGMENT),
        "p47: refusal lost its pinned fragment `{PINNED_FRAGMENT}`; got: {err}"
    );
}

/// THE BOUNDARY PIN. Every legitimate way a `u_N` spelling reaches a
/// declaration must still elaborate. Without this, "reject everything spelled
/// `u_N`" would satisfy the test above.
///
/// `useIdCollide` and `guillemetUniverse` joined the fixture on 2026-08-26b
/// and are not decoration: the first is the ARITY witness for `idCollide` (it
/// instantiates two DIFFERENT levels, which only typechecks if the hole and
/// the written `u_0` reached registration as independent parameters), and the
/// second keeps p51's reserved-name refusal scoped to the `?`-LEADING space
/// rather than to guillemets or to a `?` anywhere in a name.
#[test]
fn test_mint_name_collision_refusal_is_precise() {
    let verdicts = elab_fixture("p48_mint_name_collision_precision.lean");
    let names: Vec<&str> = verdicts.iter().map(|(n, _)| n.as_str()).collect();
    assert_eq!(
        names,
        [
            "idCollide",
            "useIdCollide",
            "holeOnly",
            "noMintCollision",
            "declaredCollision",
            "guillemetUniverse",
            "nonCollidingForcedHole"
        ],
        "p48: declaration set moved — update the expected list deliberately"
    );
    for (name, verdict) in &verdicts {
        assert!(
            verdict.is_ok(),
            "p48: `{name}` must still elaborate — the role classifier narrows a \
             decision and the mint-namespace reservation removes a collision; \
             neither may widen a refusal. Got: {verdict:?}"
        );
    }
}

/// THE FLIP (2026-08-26b), and what used to stand here.
///
/// This test was `test_mint_name_collision_overconstrains_independent_universes`
/// and asserted a REFUSAL: closing p47 by classification left the hole's mint
/// and the written `u_N` as ONE level, now rigid, so a declaration whose two
/// universes must be independent was rejected with
/// `cannot assign rigid universe parameter u_0 := u_1 + 1` — where the same
/// declaration spelled `Sort w` passed, and where Lean accepts both.
///
/// Metavariables are now minted into a reserved namespace no surface
/// identifier can reach, so the two levels are never the same `Name` and the
/// refusal has nothing to fire on. Elaborating is only half the claim: a
/// conflated declaration elaborates too, and registers ONE parameter. The
/// fixture's use sites instantiate each declaration at two DIFFERENT levels,
/// so they typecheck only at arity two — and this test additionally asserts
/// the arity directly, which is the half a fixture-count cannot carry.
#[test]
fn test_hole_and_written_universe_are_independent() {
    let verdicts = elab_fixture("p49_mint_collision_independence.lean");
    let names: Vec<&str> = verdicts.iter().map(|(n, _)| n.as_str()).collect();
    assert_eq!(
        names,
        ["n3h", "useN3h", "n3w", "useN3w", "n3", "useN3"],
        "p49: declaration set moved — update the expected list deliberately"
    );
    for (name, verdict) in &verdicts {
        assert!(
            verdict.is_ok(),
            "p49: `{name}` must elaborate. A `cannot assign rigid universe \
             parameter` here means a level hole and a written universe have \
             become one level again — the mint namespace is no longer \
             reserved. Got: {verdict:?}"
        );
    }

    // The arity, measured rather than inferred from the use sites: `n3` and
    // its `Sort w` rename must register the SAME universe interface, because
    // "the spelling no longer matters" is the whole claim.
    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();
    for src in [
        "def n3w (\u{3b2} : Sort _) (\u{3b3} : Sort w) (y : \u{3b3}) (l : List \u{3b2}) : Nat := 0\n",
        "def n3 (\u{3b2} : Sort _) (\u{3b3} : Sort u_0) (y : \u{3b3}) (l : List \u{3b2}) : Nat := 0\n",
    ] {
        let decls = parse_file(src).expect("p49 arity probe must parse");
        for decl in &decls {
            let processed = preprocess_decl_with_context(decl, &mut file_ctx);
            elaborate_decl_and_register_with_context(&mut env, &processed, &mut file_ctx)
                .expect("p49 arity probe must elaborate");
        }
    }
    for name in ["n3w", "n3"] {
        let info = env
            .get_const(&clean_kernel::Name::from_string(name))
            .unwrap_or_else(|| panic!("p49: `{name}` must be registered"));
        assert_eq!(
            info.level_params.len(),
            2,
            "p49: `{name}` must export TWO independent universe parameters — one \
             means the hole and the second binder's universe were conflated, \
             which is exactly the state the reservation removed. Got: {:?}",
            info.level_params
        );
    }
}

/// The reservation itself (p51): the mint namespace is not writable. `?` is
/// not an identifier-start character so the level grammar has no production
/// for `Sort ?u_0` — but a guillemet identifier bypasses the lexer's
/// identifier rules entirely (`Sort «my?weird»` elaborated at `2ce2cf2c1`),
/// and that door has to be shut explicitly or the whole reservation rests on
/// a lexer accident.
///
/// BOTH productions that build a `Level::Param` from a written identifier are
/// asserted, and separately: the gate probe greps the whole `clean check`
/// output for the fragment and could not tell one arm's refusal from the
/// other's. The antiquotation arm is degenerate in a plain `def` for every
/// name (`Sort $u` failed at the KERNEL with `Undefined universe level
/// parameter 'u'` at `2ce2cf2c1`), so what this pins there is the REASON and
/// the LAYER — refused as reserved, by the elaborator — which is what stops
/// the arm becoming a way in if the quotation path is ever completed.
#[test]
fn test_written_universe_in_the_mint_namespace_is_refused() {
    let verdicts = elab_fixture("p51_reserved_mint_namespace_MUST_FAIL.lean");
    let names: Vec<&str> = verdicts.iter().map(|(n, _)| n.as_str()).collect();
    assert_eq!(
        names,
        ["writesAMintName", "writesAMintNameAntiquot"],
        "p51: declaration set moved — update the expected list deliberately"
    );
    for (name, verdict) in &verdicts {
        let err = verdict.as_ref().err().unwrap_or_else(|| {
            panic!("p51: `{name}` must be refused — the mint namespace is not writable")
        });
        assert!(
            err.contains("ReservedUniverseName"),
            "p51: `{name}`'s refusal changed shape. If it now PASSES, the mint \
             namespace is writable again and the p47/p49 collision class is back; \
             if it fails at the KERNEL instead, this production has stopped being \
             guarded and only the other one is. Got: {err}"
        );
    }
}

/// The `Sort w` control on its own: an auto-bound universe whose name CANNOT
/// collide with a mint was always rigid, and stays so. This is the invariant
/// the collision case had silently lost.
#[test]
fn test_autobound_universe_without_collision_is_rigid() {
    let verdicts = elab_source(
        "non-colliding autobound",
        "def badAutoNamed (β : Sort _) : Sort w := Nat\n",
    );
    assert_eq!(verdicts.len(), 1);
    let err = verdicts[0]
        .1
        .as_ref()
        .expect_err("an auto-bound `w` is rigid, so `Sort w := Nat` is a loud mismatch");
    assert!(
        err.contains(r#"expected: "Sort w""#),
        "control lost its shape; got: {err}"
    );
}

/// TRIPWIRE for the direction p47 does NOT cover — "should be ASSIGNABLE,
/// treated as RIGID". Probed 2026-08-26 and found CLEAN: the class is not
/// reachable today, so NOTHING was implemented for it. These declarations are
/// the pin that fails if it ever becomes reachable.
///
/// The hazard is a rigid name surviving into the NEXT declaration while the
/// shared level mint reissues that same `u_N` string, which would make a
/// fresh universe METAVARIABLE born rigid and produce a spurious
/// `cannot assign rigid universe parameter u_0 := …` on a declaration that
/// never wrote `u_0`. `MetaState::rigid_level_params` documents itself as set
/// once per declaration against a fresh `MetaState`; this is that comment,
/// executed. (The bridge's DELIBERATE rigidity for enclosing level names
/// inside a tactic block is a different thing and is pinned by p42.)
#[test]
fn test_rigid_level_params_do_not_leak_into_a_later_declaration() {
    let verdicts = elab_fixture("p50_rigid_does_not_leak_across_decls.lean");
    let names: Vec<&str> = verdicts.iter().map(|(n, _)| n.as_str()).collect();
    assert_eq!(
        names,
        [
            "leakDeclared",
            "leakDeclaredAfter",
            "leakDeclaredForced",
            "leakFile",
            "leakFileAfter",
            "leakFileAfterPoly"
        ],
        "p50: declaration set moved — update the expected list deliberately"
    );
    for (name, verdict) in &verdicts {
        assert!(
            verdict.is_ok(),
            "p50: `{name}` must elaborate. A refusal here — especially \
             `cannot assign rigid universe parameter` — means a previous \
             declaration's rigid set leaked into this one's mint namespace, \
             which is the class this fixture exists to catch. Got: {verdict:?}"
        );
    }
}

/// The classifier itself, against a live `ElabCtx`: all three roles, and the
/// TOTALITY that makes it a classifier rather than a predicate — a declared
/// name is `Rigid`, a minted one is `Minted`, an unseen one is `Foreign`, and
/// only the first is unassignable.
#[test]
fn test_level_param_role_classifies_declared_minted_and_foreign() {
    use crate::level_role::LevelParamRole;

    let env = Environment::with_prelude();
    let mut ctx = crate::infer::ElabCtx::new(&env);
    ctx.set_decl_universe_params(&[clean_parser::SurfaceName::generated_path("u")]);

    assert_eq!(
        ctx.level_param_role(&clean_kernel::Name::from_string("u")),
        LevelParamRole::Rigid,
        "a declared `.{{u}}` param is rigid"
    );
    assert_eq!(
        ctx.level_param_role(&clean_kernel::Name::from_string("nowhere")),
        LevelParamRole::Foreign,
        "a name this declaration never bound is foreign"
    );

    // Mint one. It lands in `universe_params` — which is exactly why that
    // vector cannot be used as a rigidity proxy — but NOT in the rigid set.
    let minted = ctx.fresh_universe_param();
    let clean_kernel::Level::Param(minted_name) = &minted else {
        panic!("fresh_universe_param must return a Level::Param, got {minted:?}");
    };
    assert_eq!(
        ctx.level_param_role(minted_name),
        LevelParamRole::Minted,
        "`{minted_name}` was minted by this declaration: assignable, not rigid"
    );
    // 2026-08-26b: and it is in the RESERVED namespace, which is what makes
    // `Minted` unreachable from a name the user WROTE. Without this assertion
    // the classifier could still be correct while the two populations shared a
    // spelling — the state that produced p47 and cost p49.
    assert!(
        clean_parser::SurfaceName::from_name(minted_name.clone())
            .component_text()
            .is_some_and(crate::level_mint::is_reserved_level_name),
        "a minted level must be unwritable at the surface; `{minted_name}` is not \
         in the reserved namespace"
    );

    assert!(!LevelParamRole::Rigid.is_assignable());
    assert!(LevelParamRole::Minted.is_assignable());
    assert!(LevelParamRole::Foreign.is_assignable());
}
