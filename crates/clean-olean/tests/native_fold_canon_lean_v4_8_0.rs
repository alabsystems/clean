// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The Lean 4.8.0 world of native-fold authority
//! (`clean_kernel::env::native_fold_authority`, table
//! `crates/clean-kernel/src/env/native_fold_canon.tsv`, world `lean-v4.8.0`).
//!
//! Lean 4.8.0 is a supported target, not the workspace pin: trust-ir's
//! operational semantics are Lean 4.8.0 + lake, and Trust's default-on
//! `bridge_gate_default_on` re-checks them through this kernel. When a
//! name-keyed fold became content-keyed (`docs/issues/2026-09-26-kernel-
//! native-fold-by-name.md`) no row covered Lean 4.8.0's `Init`, whose
//! arithmetic is compiled differently from 4.30's, and four trust-ir lemmas
//! proved by `omega` stopped checking (`2026-09-27` section of that issue).
//!
//! Unlike the pinned toolchain's world, this one is NOT every row the decoded
//! `Init` mints. It pins exactly the rows named in [`REVIEWED_NEW`]: digests
//! no other world holds, each read against Lean 4.8.0's source and shown to
//! compute what the kernel's fold computes (the review is recorded in the
//! issue; the differential test below re-checks it on every run). A minted
//! row whose digest another world already pins is admitted by that world —
//! the digest covers the whole closure, so it is the same definition — and is
//! deliberately NOT copied here: a row later withdrawn from its own world for
//! cause must not live on as an unreviewed copy.
//!
//! Every other minted row stays unpinned, so its fold does not fire and the
//! term δ-unfolds: completeness only. The string-literal rule additionally
//! reviews `Char.ofNat` against its Unicode-scalar definition. This grants
//! neither UInt nor BitVec native reducers authority; their carriers still
//! require their own reviews (`lean_profile_reducer_differential.rs`).
//!
//! Needs the `leanprover/lean4:v4.8.0` toolchain installed under elan. Absent,
//! the four reviewed optional tests print `NATIVE_FOLD_LEAN_V4_8_0_GATE=skipped:…`
//! (the suite runner records UNKNOWN) and return; `CLEAN_OLEAN_REQUIRE_LEAN_V4_8_0=1`
//! makes their absence a failure instead. The imported-string proof and false-twin
//! test requires that toolchain and fails when its subject cannot be measured.

use std::collections::{BTreeSet, HashSet};
use std::path::Path;

use clean_kernel::env::{canonical_fold_rows, Declaration, Environment};
use clean_kernel::expr::{BinderInfo, Expr, ExprKind};
use clean_kernel::level::Level;
use clean_kernel::name::Name;
use clean_kernel::tc::TypeChecker;
use clean_olean::verify_batch_full::typecheck_constants_full;
use clean_olean::{load_module_with_deps, load_modules_with_deps};

#[path = "support/fold_canon.rs"]
mod fold_canon;
#[path = "support/installed_lean.rs"]
mod installed_lean;
use fold_canon::{check_world, fold_with_fresh_boundaries, mint, repin_requested};

/// A minted row before a role is assigned: `(world, name, hex)`.
type MintedRow = (String, String, String);
use installed_lean::{compile_fixture, installed_lean, skip_unmeasured, InstalledLean};

const TOOLCHAIN: &str = "leanprover/lean4:v4.8.0";
const GATE: &str = "NATIVE_FOLD_LEAN_V4_8_0";
const REQUIRE_ENV: &str = "CLEAN_OLEAN_REQUIRE_LEAN_V4_8_0";

/// The fold keys this world admits although no other world pins their Lean
/// 4.8.0 digest — each reviewed (`docs/issues/2026-09-26-kernel-native-fold-
/// by-name.md`, section "2026-09-27 — the Lean 4.8.0 world"). The fourteen
/// `reduce_nat` heads are exactly the heads Lean 4.8.0's own kernel folds
/// natively over these same definitions; `instDecidableAnd` (a boundary of
/// `Nat.div` and `Nat.mod`) and `Bool.decEq` (reached through `Nat.decLe` →
/// `instDecidableEqBool`, which `Nat.div`, `Nat.mod` and every head resting on
/// them need) are the only fresh digests in the heads' boundary closure, so
/// none of those folds without them. Adding a name here is
/// a claim that its 4.8.0 definition computes what the fold computes: review
/// it first, and extend [`test_lean_v4_8_0_reviewed_folds_agree_with_their_definitions`].
const REVIEWED_NEW: &[&str] = &[
    "Nat.add",
    "Nat.sub",
    "Nat.mul",
    "Nat.div",
    "Nat.mod",
    "Nat.gcd",
    "Nat.pow",
    "Nat.beq",
    "Nat.ble",
    "Nat.land",
    "Nat.lor",
    "Nat.xor",
    "Nat.shiftLeft",
    "Nat.shiftRight",
    "instDecidableAnd",
    "Bool.decEq",
    "Char.ofNat",
];

/// The fourteen binary heads of Lean's `reduce_nat`.
const REDUCE_NAT_HEADS: [&str; 14] = [
    "Nat.add",
    "Nat.sub",
    "Nat.mul",
    "Nat.div",
    "Nat.mod",
    "Nat.gcd",
    "Nat.pow",
    "Nat.beq",
    "Nat.ble",
    "Nat.land",
    "Nat.lor",
    "Nat.xor",
    "Nat.shiftLeft",
    "Nat.shiftRight",
];

/// Lean 4.8.0, or `None` after reporting the skip (see the module docs).
fn lean_v4_8_0() -> Option<InstalledLean> {
    let lean = installed_lean(TOOLCHAIN);
    if lean.is_none() {
        skip_unmeasured(GATE, "lean-v4.8.0-not-installed", REQUIRE_ENV);
    }
    lean
}

fn world(lean: &InstalledLean) -> String {
    format!("lean-{}", lean.version)
}

fn n(s: &str) -> Name {
    Name::from_string(s)
}

fn c(s: &str) -> Expr {
    Expr::const_(n(s), vec![])
}

fn nat() -> Expr {
    c("Nat")
}

/// Load `module` of the toolchain at `lib` into `env`; under a re-pin, the way
/// the pre-authority kernel did (every fold by name).
fn load(mut env: Environment, lib: &Path, module: &str) -> Environment {
    let run = |env: &mut Environment| {
        load_module_with_deps(env, module, &[lib.to_path_buf()])
            .unwrap_or_else(|e| panic!("load {module} ({}): {e}", lib.display()));
    };
    if repin_requested() {
        clean_kernel::env::native_fold_mint_bypass::run(|| run(&mut env));
    } else {
        run(&mut env);
    }
    env
}

/// `rfl : lhs = rhs` at `ty`, with the kernel's error when it does not check.
fn rfl_at(
    env: &Environment,
    ty: Expr,
    lhs: Expr,
    rhs: Expr,
    heartbeats: u32,
) -> Result<(), String> {
    let one = Level::succ(Level::zero());
    let eq = Expr::apps(
        Expr::const_(n("Eq"), vec![one.clone()]),
        [ty.clone(), lhs, rhs.clone()],
    );
    let refl = Expr::apps(Expr::const_(n("Eq.refl"), vec![one]), [ty, rhs]);
    let mut tc = TypeChecker::new(env);
    tc.set_heartbeat_limit(heartbeats);
    tc.check_type(&refl, &eq)
        .map(|_| ())
        .map_err(|e| format!("{e:?}"))
}

fn nat_rfl(env: &Environment, lhs: Expr, rhs: Expr) -> Result<(), String> {
    rfl_at(
        env,
        nat(),
        lhs,
        rhs,
        clean_kernel::tc::DEFAULT_HEARTBEAT_LIMIT,
    )
}

#[test]
fn test_lean_v4_8_0_init_fold_digests_are_pinned() {
    // SELF-SKIP OK: Lean 4.8.0 toolchain absent under elan; lean_v4_8_0() prints NATIVE_FOLD_LEAN_V4_8_0_GATE=skipped:lean-v4.8.0-not-installed, and CLEAN_OLEAN_REQUIRE_LEAN_V4_8_0=1 makes it fail.
    let Some(lean) = lean_v4_8_0() else { return };
    let world = world(&lean);
    let env = load(Environment::for_lean_replay(), &lean.lib, "Init");
    let minted = mint(&world, &env);
    let elsewhere: HashSet<(String, String)> = canonical_fold_rows()
        .into_iter()
        .filter(|(w, _, _, _)| *w != world)
        .map(|(_, name, hex, _)| (name, hex))
        .collect();
    for name in REVIEWED_NEW {
        assert!(
            minted.iter().any(|(_, n, _)| n == name),
            "reviewed `{name}` no longer mints over Lean 4.8.0's Init; re-review"
        );
    }
    let (reviewed, rest): (Vec<MintedRow>, Vec<MintedRow>) = minted
        .iter()
        .cloned()
        .partition(|(_, name, _)| REVIEWED_NEW.contains(&name.as_str()));
    let (shared, unreviewed): (Vec<MintedRow>, Vec<MintedRow>) = rest
        .into_iter()
        .partition(|(_, name, hex)| elsewhere.contains(&(name.clone(), hex.clone())));
    // Reviewed rows are `fold` (re-checked three ways below, every run); a
    // fresh boundary they rest on is `definition`, whatever other worlds keep.
    let admitted = fold_with_fresh_boundaries(&env, &reviewed, &unreviewed);
    eprintln!(
        "{world}: {} minted = {} reviewed + {} pinned elsewhere + {} unreviewed ({} as boundaries)",
        minted.len(),
        reviewed.len(),
        shared.len(),
        unreviewed.len(),
        admitted.len() - reviewed.len()
    );
    check_world(&world, &admitted);
    if repin_requested() {
        // The compiled table is the one this binary was built with; the
        // authorization and completeness checks below need the re-pinned one
        // (rebuild, rerun). `check_world` has already re-pinned, so a re-pin
        // run ends RED rather than reporting `ok` with nothing measured.
        panic!(
            "{world}: CLEAN_NATIVE_FOLD_REPIN re-pinned native_fold_canon.tsv; the authorization and completeness assertions below were NOT measured — re-run without CLEAN_NATIVE_FOLD_REPIN"
        );
    }
    // Nothing unreviewed is admitted: every fresh digest outside the reviewed
    // list is refused.
    for (_, name, _) in &unreviewed {
        assert!(
            !env.native_fold_authorized(&n(name)),
            "`{name}` folds over Lean 4.8.0 without review: {:?}",
            env.native_fold_verdict(&n(name))
        );
    }
    // Completeness: every `reduce_nat` head folds, as it does in Lean 4.8.0's
    // own kernel, at sizes δ cannot reach.
    for head in REDUCE_NAT_HEADS {
        assert!(
            env.native_fold_authorized(&n(head)),
            "{head} must fold over Lean 4.8.0's Init: {:?}",
            env.native_fold_verdict(&n(head))
        );
    }
    let big = 1u64 << 40;
    let gcd = Expr::apps(
        c("Nat.gcd"),
        [Expr::nat_lit(big * 6), Expr::nat_lit(big * 4)],
    );
    nat_rfl(&env, gcd, Expr::nat_lit(big * 2)).expect("Nat.gcd (6·2^40) (4·2^40) = 2^41");
}

/// The expected value of `head a b` on naturals, by Rust arithmetic.
fn reference(head: &str, a: u64, b: u64) -> Expr {
    let (a, b) = (u128::from(a), u128::from(b));
    let lit = |v: u128| Expr::nat_lit(u64::try_from(v).expect("reference value fits u64"));
    let boolean = |v: bool| c(if v { "Bool.true" } else { "Bool.false" });
    let gcd = |mut x: u128, mut y: u128| {
        while x != 0 {
            (x, y) = (y % x, x);
        }
        y
    };
    match head {
        "Nat.add" => lit(a + b),
        "Nat.sub" => lit(a.saturating_sub(b)),
        "Nat.mul" => lit(a * b),
        // Lean's conventions: `x / 0 = 0`, `x % 0 = x`.
        "Nat.div" => lit(a.checked_div(b).unwrap_or(0)),
        "Nat.mod" => lit(a.checked_rem(b).unwrap_or(a)),
        "Nat.gcd" => lit(gcd(a, b)),
        "Nat.pow" => lit(a.pow(u32::try_from(b).expect("small exponent"))),
        "Nat.beq" => boolean(a == b),
        "Nat.ble" => boolean(a <= b),
        "Nat.land" => lit(a & b),
        "Nat.lor" => lit(a | b),
        "Nat.xor" => lit(a ^ b),
        "Nat.shiftLeft" => lit(a << b),
        "Nat.shiftRight" => lit(a >> b),
        other => panic!("no reference for {other}"),
    }
}

/// Each reviewed head, three ways on the same literals: the kernel's FOLD on
/// `head a b`, Lean 4.8.0's own DEFINITION (`value a b`, the head replaced by
/// its δ-unfolding so its own fold cannot fire) evaluated by δι, and Rust
/// arithmetic. The review in the issue is the general argument; this pins
/// that the three agree on every input, every run.
#[test]
fn test_lean_v4_8_0_reviewed_folds_agree_with_their_definitions() {
    // SELF-SKIP OK: Lean 4.8.0 toolchain absent under elan; lean_v4_8_0() prints NATIVE_FOLD_LEAN_V4_8_0_GATE=skipped:lean-v4.8.0-not-installed, and CLEAN_OLEAN_REQUIRE_LEAN_V4_8_0=1 makes it fail.
    let Some(lean) = lean_v4_8_0() else { return };
    let env = load(Environment::for_lean_replay(), &lean.lib, "Init");
    let char_review = || {
        clean_kernel::env::native_fold_review::review(&env, &n("Char.ofNat"), !repin_requested())
    };
    let reviewed = if repin_requested() {
        clean_kernel::env::native_fold_mint_bypass::run(char_review)
    } else {
        char_review()
    };
    assert_eq!(
        reviewed.cases, 17,
        "eight string shapes and nine Unicode boundaries"
    );
    assert_eq!(reviewed.fired, 17);
    assert!(
        reviewed.passed(),
        "Lean 4.8 character/literal review: {reviewed:#?}"
    );
    if !repin_requested() {
        assert!(env.native_fold_authorized(&n("Char.ofNat")));
    }
    const INPUTS: [u64; 7] = [0, 1, 2, 3, 6, 10, 13];
    for head in REDUCE_NAT_HEADS {
        let ci = env.get_const(&n(head)).expect("head declared");
        let value = ci.value.clone().expect("head has a value");
        assert!(
            ci.level_params.is_empty(),
            "{head} is not universe-polymorphic"
        );
        let mut checked = 0usize;
        for a in INPUTS {
            for b in INPUTS {
                if head == "Nat.pow" && b > 6 {
                    continue;
                }
                let args = [Expr::nat_lit(a), Expr::nat_lit(b)];
                let expected = reference(head, a, b);
                let ty = if matches!(head, "Nat.beq" | "Nat.ble") {
                    c("Bool")
                } else {
                    nat()
                };
                let beats = clean_kernel::tc::DEFAULT_HEARTBEAT_LIMIT;
                let folded = Expr::apps(c(head), args.clone());
                rfl_at(&env, ty.clone(), folded, expected.clone(), beats)
                    .unwrap_or_else(|e| panic!("fold {head} {a} {b} ≠ {expected:?}: {e}"));
                let unfolded = Expr::apps(value.clone(), args);
                rfl_at(&env, ty, unfolded, expected.clone(), beats).unwrap_or_else(|e| {
                    panic!("Lean 4.8.0's {head} {a} {b} does not δι-reduce to {expected:?}: {e}")
                });
                checked += 1;
            }
        }
        // 7 × 7 pairs, `Nat.pow` 7 × 5 (exponents up to 6).
        let expected_count = if head == "Nat.pow" { 35 } else { 49 };
        assert_eq!(checked, expected_count, "{head}: inputs checked");
    }

    // The two reviewed `Decidable` heads: each registered reducer against Lean
    // 4.8.0's own definition on every pair of decided arguments, in Lean's
    // kernel theory exactly (no Clean reducer), and both against the truth.
    let mut tc = TypeChecker::new(&env);
    tc.set_kernel_theory(clean_kernel::env::KernelTheory::LeanReference);
    let decided = |truth: bool| -> (Expr, Expr) {
        if truth {
            (
                c("True"),
                Expr::apps(c("Decidable.isTrue"), [c("True"), c("True.intro")]),
            )
        } else {
            let not_false = Expr::lam(BinderInfo::Default, c("False"), Expr::bvar(0));
            (
                c("False"),
                Expr::apps(c("Decidable.isFalse"), [c("False"), not_false]),
            )
        }
    };
    let boolean = |v: bool| c(if v { "Bool.true" } else { "Bool.false" });
    let mut cases: Vec<(&str, Vec<Expr>, bool)> = Vec::new();
    for p in [true, false] {
        for q in [true, false] {
            let ((pp, dp), (qq, dq)) = (decided(p), decided(q));
            cases.push(("instDecidableAnd", vec![pp, qq, dp, dq], p && q));
            cases.push(("Bool.decEq", vec![boolean(p), boolean(q)], p == q));
        }
    }
    for (head, args, truth) in cases {
        let name = n(head);
        let value = env
            .get_const(&name)
            .and_then(|ci| ci.value.clone())
            .expect("head value");
        let reducer = env.get_native_reducer(&name).expect("head reducer");
        let refs: Vec<&Expr> = args.iter().collect();
        let reduced = reducer(&refs).expect("reducer fires on decided arguments");
        let by_definition = Expr::apps(value, args.iter().cloned());
        let expected = if truth {
            "Decidable.isTrue"
        } else {
            "Decidable.isFalse"
        };
        tc.reset_local_context();
        tc.reset_heartbeat();
        let whnf = tc.whnf(&by_definition);
        for (what, term) in [("definition", &whnf), ("reducer", &reduced)] {
            assert!(
                matches!(term.get_app_fn().kind(), ExprKind::Const(k, _) if k.to_string() == expected),
                "{head} {args:?}: the {what} gives {term:?}, not {expected}"
            );
        }
        tc.reset_heartbeat();
        assert!(
            tc.is_def_eq(&by_definition, &reduced),
            "{head} {args:?}: reducer {reduced:?} ≠ Lean 4.8.0's definition"
        );
    }
}

/// The regression Trust measured: at Clean main `a3d6008de0`, trust-ir's four
/// `validChar` lemmas — proved by `omega` over Lean 4.8.0's `Init` — failed
/// `check_type: TypeMismatch` in the bridge gate's re-check, because no
/// Lean 4.8.0 `Nat` fold was canonical. The fixture is that block of
/// `TrustIr/Basic.lean`, verbatim, compiled here with Lean 4.8.0. Checked in
/// the gate's own environment shape (`Environment::default()` plus the native
/// reducers, then the `.olean` closure) and in the re-check lanes'
/// (`Environment::for_lean_replay`).
#[test]
fn test_trustir_valid_char_lemmas_check_over_lean_v4_8_0_init() {
    // SELF-SKIP OK: Lean 4.8.0 toolchain absent under elan (needed to compile the fixture); lean_v4_8_0() prints NATIVE_FOLD_LEAN_V4_8_0_GATE=skipped:lean-v4.8.0-not-installed, and CLEAN_OLEAN_REQUIRE_LEAN_V4_8_0=1 makes it fail.
    let Some(lean) = lean_v4_8_0() else { return };
    let fixture = compile_fixture(&lean, "trustir_valid_char", "TrustIrValidChar");
    let search = [fixture.path().to_path_buf(), lean.lib.clone()];
    let bridge_shape = {
        let mut env = Environment::default();
        env.ensure_native_reducers();
        env
    };
    for (shape, mut env) in [
        ("bridge gate", bridge_shape),
        ("re-check lanes", Environment::for_lean_replay()),
    ] {
        let summaries =
            load_modules_with_deps(&mut env, &["TrustIrValidChar".to_string()], &search)
                .unwrap_or_else(|e| panic!("{shape}: load TrustIrValidChar: {e}"));
        let targets: BTreeSet<String> = summaries
            .iter()
            .filter(|s| s.module_name.as_deref() == Some("TrustIrValidChar"))
            .flat_map(|s| s.added_names.iter().map(ToString::to_string))
            .collect();
        for lemma in [
            "TrustIr.validChar_of_lt_256",
            "TrustIr.not_validChar_surrogate",
            "TrustIr.not_validChar_above_max",
            "TrustIr.validChar_lt_two_pow_32",
        ] {
            assert!(targets.contains(lemma), "{shape}: fixture lost {lemma}");
        }
        let (pass, fail, errors) =
            typecheck_constants_full(&env, &targets, clean_kernel::tc::DEFAULT_HEARTBEAT_LIMIT);
        assert_eq!(
            fail,
            0,
            "{shape}: {fail} of {} fixture constants fail the kernel re-check: {errors:#?}",
            pass + fail
        );
        assert_eq!(
            pass,
            targets.len(),
            "{shape}: every fixture constant re-checked"
        );
    }
}

#[test]
fn test_lean_v4_8_0_imported_string_proofs_and_false_twin() {
    let lean = installed_lean(TOOLCHAIN)
        .expect("Lean 4.8.0 is required to re-check the imported string proofs and false twin");
    let fixture = compile_fixture(&lean, "string_literals", "StringLiterals");
    let search = [fixture.path().to_path_buf(), lean.lib.clone()];
    let targets: BTreeSet<String> = [
        "empty",
        "ascii",
        "unicode",
        "unequal_ascii",
        "unequal_unicode",
        "unequal_empty",
    ]
    .into_iter()
    .map(|name| format!("StringLiterals.{name}"))
    .collect();
    for (shape, mut env) in [
        ("bridge", Environment::default()),
        ("replay", Environment::for_lean_replay()),
    ] {
        load_modules_with_deps(&mut env, &["StringLiterals".to_string()], &search)
            .unwrap_or_else(|error| panic!("{shape}: fixture import: {error}"));
        let (pass, fail, errors) =
            typecheck_constants_full(&env, &targets, clean_kernel::tc::DEFAULT_HEARTBEAT_LIMIT);
        assert_eq!((pass, fail), (6, 0), "{shape}: {errors:#?}");
        for target in &targets {
            assert!(
                env.axiom_deps(&n(target))
                    .expect("imported theorem")
                    .is_empty(),
                "{shape}: {target}"
            );
        }
        let proof = env
            .get_const(&n("StringLiterals.unequal_ascii"))
            .and_then(|info| info.value.as_ref())
            .expect("genuine Lean proof");
        let false_equality = Expr::apps(
            Expr::const_(n("Eq"), vec![Level::succ(Level::zero())]),
            [c("String"), Expr::str_lit("enum"), Expr::str_lit("enum")],
        );
        let false_type = Expr::app(c("Not"), false_equality);
        let tc = TypeChecker::new(&env);
        let error = tc
            .check_type(proof, &false_type)
            .expect_err("the original proof cannot prove enum differs from itself");
        assert!(
            matches!(error, clean_kernel::tc::TypeError::TypeMismatch { .. }),
            "{shape}: {error:?}"
        );
    }
}

/// Admission is by content, not by toolchain: over Lean 4.8.0's `Init.Prelude`
/// (which declares no `Nat.gcd`) a user `Nat.gcd := fun _ _ => 0` still does
/// not fold — `Nat.gcd 4 6 = 2` is refused while δ gives `0` — and the
/// Prelude's own reviewed `Nat.mul` does, at a size δ cannot reach.
#[test]
fn test_lean_v4_8_0_user_nat_gcd_is_refused() {
    // SELF-SKIP OK: Lean 4.8.0 toolchain absent under elan; lean_v4_8_0() prints NATIVE_FOLD_LEAN_V4_8_0_GATE=skipped:lean-v4.8.0-not-installed, and CLEAN_OLEAN_REQUIRE_LEAN_V4_8_0=1 makes it fail.
    let Some(lean) = lean_v4_8_0() else { return };
    let mut env = load(Environment::for_lean_replay(), &lean.lib, "Init.Prelude");
    assert!(
        env.get_const(&n("Nat.gcd")).is_none(),
        "Init.Prelude declares no Nat.gcd"
    );
    let big = 1u64 << 31;
    let product = Expr::apps(c("Nat.mul"), [Expr::nat_lit(big), Expr::nat_lit(big)]);
    nat_rfl(&env, product, Expr::nat_lit(big * big)).expect("positive control: 2^31 * 2^31 = 2^62");
    let nat2 = Expr::pi(
        BinderInfo::Default,
        nat(),
        Expr::pi(BinderInfo::Default, nat(), nat()),
    );
    let zero = Expr::lam(
        BinderInfo::Default,
        nat(),
        Expr::lam(BinderInfo::Default, nat(), c("Nat.zero")),
    );
    env.add_decl(Declaration::Definition {
        name: n("Nat.gcd"),
        level_params: vec![],
        type_: nat2,
        value: zero,
        is_reducible: true,
    })
    .expect("user Nat.gcd");
    let gcd = Expr::apps(c("Nat.gcd"), [Expr::nat_lit(4), Expr::nat_lit(6)]);
    assert!(
        nat_rfl(&env, gcd.clone(), Expr::nat_lit(2)).is_err(),
        "ATTACK ACCEPTED: a user Nat.gcd folded over Lean 4.8.0's Prelude"
    );
    nat_rfl(&env, gcd, Expr::nat_lit(0)).expect("the user definition's own δ answer");
    assert!(!env.native_fold_authorized(&n("Nat.gcd")));
}
