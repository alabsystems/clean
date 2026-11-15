// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! RED/GREEN pins for native-fold authority (`native_fold_authority.rs`) and
//! the Clean-world pin battery for `native_fold_canon.tsv`.
//!
//! Every attack here was ACCEPTED by the kernel before authority existed:
//! each rule fired on a constant's name, whatever the environment said the
//! name meant. Each attack has a positive control beside it showing that the
//! canonical constant still computes.

use super::*;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;
use crate::tc::TypeChecker;

fn n(s: &str) -> Name {
    Name::from_string(s)
}

fn c(s: &str) -> Expr {
    Expr::const_(n(s), vec![])
}

fn one() -> Level {
    Level::succ(Level::zero())
}

fn nat() -> Expr {
    c("Nat")
}

fn lit(v: u64) -> Expr {
    Expr::nat_lit(v)
}

fn nat_to_nat_to_nat() -> Expr {
    Expr::pi(
        BinderInfo::Default,
        nat(),
        Expr::pi(BinderInfo::Default, nat(), nat()),
    )
}

/// `@Eq Nat a b`.
fn eq_nat(a: Expr, b: Expr) -> Expr {
    Expr::apps(Expr::const_(n("Eq"), vec![one()]), [nat(), a, b])
}

/// `@Eq.refl Nat a`.
fn refl_nat(a: Expr) -> Expr {
    Expr::apps(Expr::const_(n("Eq.refl"), vec![one()]), [nat(), a])
}

fn theorem(env: &mut Environment, name: &str, ty: Expr, value: Expr) -> Result<(), EnvError> {
    env.add_decl(Declaration::Theorem {
        name: n(name),
        level_params: vec![],
        type_: ty,
        value,
    })
}

fn def(env: &mut Environment, name: &str, ty: Expr, value: Expr) -> Result<(), EnvError> {
    env.add_decl(Declaration::Definition {
        name: n(name),
        level_params: vec![],
        type_: ty,
        value,
        is_reducible: true,
    })
}

/// `rfl : lhs = rhs` at `Nat` — checked by the kernel, which is the whole
/// question: does `lhs` reduce to `rhs`?
fn rfl_checks(env: &Environment, lhs: Expr, rhs: Expr) -> bool {
    let tc = TypeChecker::new(env);
    tc.check_type(&refl_nat(rhs.clone()), &eq_nat(lhs, rhs))
        .is_ok()
}

/// The Crystal E4c chain, end to end: a user `Nat.gcd := fun _ _ => 0` in an
/// environment that does not declare `Nat.gcd`, then `False`.
///
/// Before authority every step returned `Ok` (measured on `with_prelude` at
/// `d57e0e018`): the delta step proves `gcd x y = 0`, the name-keyed fold
/// proves `gcd 4 6 = 2`, and `Eq.trans`/`congrArg`/`Eq.mp` turn them into
/// `False` with an empty domain-axiom closure.
#[test]
fn test_e4c_user_gcd_does_not_fold_and_false_is_refused() {
    let mut env = Environment::with_prelude();
    assert!(
        env.get_const(&n("Nat.gcd")).is_none(),
        "the attack needs an environment that does not declare Nat.gcd"
    );
    let zero_fn = Expr::lam(
        BinderInfo::Default,
        nat(),
        Expr::lam(BinderInfo::Default, nat(), c("Nat.zero")),
    );
    def(&mut env, "Nat.gcd", nat_to_nat_to_nat(), zero_fn).expect("a user may define Nat.gcd");

    // Step 2 (δ, legitimate): ∀ x y, Nat.gcd x y = 0.
    let gcd_xy = Expr::apps(c("Nat.gcd"), [Expr::bvar(1), Expr::bvar(0)]);
    let all_zero_ty = Expr::pi(
        BinderInfo::Default,
        nat(),
        Expr::pi(BinderInfo::Default, nat(), eq_nat(gcd_xy, lit(0))),
    );
    let all_zero_val = Expr::lam(
        BinderInfo::Default,
        nat(),
        Expr::lam(BinderInfo::Default, nat(), refl_nat(lit(0))),
    );
    theorem(&mut env, "e4c_gcd_zero", all_zero_ty, all_zero_val)
        .expect("δ-unfolding the user's Nat.gcd is legitimate");

    // Step 3 (the fold): Nat.gcd 4 6 = 2 by rfl. REFUSED now.
    let gcd_4_6 = Expr::apps(c("Nat.gcd"), [lit(4), lit(6)]);
    assert!(
        !rfl_checks(&env, gcd_4_6.clone(), lit(2)),
        "Nat.gcd 4 6 = 2 must NOT check by rfl against a user's Nat.gcd"
    );
    assert!(
        matches!(
            env.native_fold_verdict(&n("Nat.gcd")),
            Err(FoldRefusal::NotCanonical { .. })
        ),
        "the user's Nat.gcd is a definition, but not the canonical one: {:?}",
        env.native_fold_verdict(&n("Nat.gcd"))
    );
    // The δ answer is what the kernel now gives.
    assert!(rfl_checks(&env, gcd_4_6.clone(), lit(0)));

    // Steps 4-5: 2 = 0 via Eq.trans, then False via congrArg/Eq.mp. The whole
    // chain rests on step 3, so the kernel must refuse it.
    let h20 = Expr::apps(
        Expr::const_(n("Eq.trans"), vec![one()]),
        [
            nat(),
            lit(2),
            gcd_4_6,
            lit(0),
            refl_nat(lit(2)),
            Expr::apps(c("e4c_gcd_zero"), [lit(4), lit(6)]),
        ],
    );
    let motive = Expr::lam(BinderInfo::Default, nat(), Expr::prop());
    let succ_case = Expr::lam(
        BinderInfo::Default,
        nat(),
        Expr::lam(BinderInfo::Default, Expr::prop(), c("True")),
    );
    let p = Expr::lam(
        BinderInfo::Default,
        nat(),
        Expr::apps(
            Expr::const_(n("Nat.rec"), vec![one()]),
            [motive, c("False"), succ_case, Expr::bvar(0)],
        ),
    );
    let p_at = |k: u64| Expr::app(p.clone(), lit(k));
    let congr = Expr::apps(
        Expr::const_(n("congrArg"), vec![one(), one()]),
        [nat(), Expr::prop(), lit(2), lit(0), p.clone(), h20],
    );
    let false_proof = Expr::apps(
        Expr::const_(n("Eq.mp"), vec![Level::zero()]),
        [p_at(2), p_at(0), congr, c("True.intro")],
    );
    assert!(
        theorem(&mut env, "e4c_false", c("False"), false_proof).is_err(),
        "the E4c chain must not reach False"
    );
}

/// An AXIOM must not compute. A user axiom `Nat.gcd` in `with_prelude`
/// (which does not declare it) folded `Nat.gcd 4 6` to `2` by name.
#[test]
fn test_user_axiom_gcd_does_not_compute() {
    let mut env = Environment::with_prelude();
    env.add_decl(Declaration::Axiom {
        name: n("Nat.gcd"),
        level_params: vec![],
        type_: nat_to_nat_to_nat(),
    })
    .expect("a user may declare Nat.gcd as an axiom");
    assert!(!rfl_checks(
        &env,
        Expr::apps(c("Nat.gcd"), [lit(4), lit(6)]),
        lit(2)
    ));
    assert_eq!(
        env.native_fold_verdict(&n("Nat.gcd")),
        Err(FoldRefusal::HeadNotDefinition(n("Nat.gcd")))
    );
}

/// `Nat.shiftRight` as a value-less AXIOM (the bare `init_nat` path registers
/// it that way) must not compute `8 >>> 1 = 4`.
#[test]
fn test_shiftright_axiom_does_not_compute() {
    let mut env = Environment::new();
    env.init_nat().expect("init_nat");
    env.init_eq().expect("init_eq");
    let info = env
        .get_const(&n("Nat.shiftRight"))
        .expect("init_nat declares Nat.shiftRight");
    assert_eq!(
        info.kind,
        ConstantKind::Axiom,
        "the bare path keeps the axiom"
    );
    assert!(
        !rfl_checks(
            &env,
            Expr::apps(c("Nat.shiftRight"), [lit(8), lit(1)]),
            lit(4)
        ),
        "an axiom has no computational content to fold"
    );
}

/// Positive control: every canonical `Nat` fold `with_prelude` defines still
/// fires, including at magnitudes δ-unfolding could never reach.
#[test]
fn test_canonical_nat_folds_still_fire_in_the_prelude() {
    let env = Environment::with_prelude();
    for head in [
        "Nat.add",
        "Nat.sub",
        "Nat.mul",
        "Nat.div",
        "Nat.mod",
        "Nat.pow",
        "Nat.beq",
        "Nat.ble",
        "Nat.land",
        "Nat.lor",
        "Nat.xor",
        "Nat.shiftLeft",
    ] {
        assert!(
            env.native_fold_verdict(&n(head)).is_ok(),
            "{head}: {:?}",
            env.native_fold_verdict(&n(head))
        );
    }
    let two_pow = |k: u64| {
        Expr::bignat_lit(
            crate::expr::BigNat::Small(2)
                .checked_pow_big(&crate::expr::BigNat::Small(k))
                .expect("2^k fits"),
        )
    };
    // 2^200 by the fold: δ would need 2^200 Nat.rec steps.
    assert!(rfl_checks(
        &env,
        Expr::apps(c("Nat.pow"), [lit(2), lit(200)]),
        two_pow(200)
    ));
    assert!(rfl_checks(
        &env,
        Expr::apps(c("Nat.mul"), [two_pow(64), two_pow(64)]),
        two_pow(128)
    ));
    assert!(rfl_checks(
        &env,
        Expr::apps(c("Nat.mod"), [lit(1_000_003), lit(97)]),
        lit(1_000_003 % 97)
    ));
    assert!(rfl_checks(
        &env,
        Expr::apps(c("Nat.div"), [lit(1_000_003), lit(97)]),
        lit(1_000_003 / 97)
    ));
    assert!(rfl_checks(
        &env,
        Expr::apps(c("Nat.add"), [lit(2), lit(3)]),
        lit(5)
    ));
}

/// A mismatched native candidate stays refused while its checked definition computes.
#[test]
fn test_bitvec_shift_review_refusals_keep_typed_definitions() {
    let env = Environment::with_prelude();
    let tc = TypeChecker::new(&env);
    for (head, answer) in [("BitVec.shiftLeft", 254), ("BitVec.ushiftRight", 127)] {
        assert!(
            matches!(
                env.native_fold_verdict(&n(head)),
                Err(FoldRefusal::ReviewRefused { .. })
            ),
            "{head} must retain its negative review"
        );
        let bitvec = |value| Expr::apps(c("BitVec.ofNat"), [lit(8), lit(value)]);
        let application = Expr::apps(c(head), [lit(8), bitvec(255), lit(1)]);
        tc.check_type(&application, &Expr::app(c("BitVec"), lit(8)))
            .expect("the checked definition keeps its BitVec result type");
        assert!(tc.is_def_eq(&application, &bitvec(answer)), "{head}");
        assert!(
            !tc.is_def_eq(&application, &lit(answer)),
            "{head} must not return the mismatched Nat candidate"
        );
    }
}

/// Bootstrap lifetime checks run alone so their global gate cannot affect other tests.
#[test]
fn test_mint_bypass_scope_restores_after_unwind_and_overlap() {
    const CHILD: &str = "CLEAN_MINT_SCOPE_TEST_CHILD";
    let (_, module) = module_path!().split_once("::").expect("kernel test module");
    let test_name = format!("{module}::test_mint_bypass_scope_restores_after_unwind_and_overlap");
    let expected_args = vec![
        test_name.clone(),
        "--exact".into(),
        "--test-threads=1".into(),
    ];
    let isolated = std::env::var(CHILD).ok().as_deref() == Some(test_name.as_str())
        && std::env::args().skip(1).collect::<Vec<_>>() == expected_args;
    if !isolated {
        let output =
            std::process::Command::new(std::env::current_exe().expect("libtest executable"))
                .args(&expected_args)
                .env(CHILD, &test_name)
                .output()
                .expect("isolated bootstrap scope regression");
        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        assert!(
            output.status.success()
                && stdout
                    .matches("test result: ok. 1 passed; 0 failed; 0 ignored;")
                    .count()
                    == 1,
            "isolated bootstrap regression: {}\n{stdout}\n{stderr}",
            output.status
        );
        return;
    }

    let mut env = Environment::with_prelude();
    let zero_fn = Expr::lam(
        BinderInfo::Default,
        nat(),
        Expr::lam(BinderInfo::Default, nat(), c("Nat.zero")),
    );
    def(&mut env, "Nat.gcd", nat_to_nat_to_nat(), zero_fn).expect("forged user gcd");
    let wrong_answer_checks =
        || rfl_checks(&env, Expr::apps(c("Nat.gcd"), [lit(4), lit(6)]), lit(2));
    assert!(
        !wrong_answer_checks(),
        "normal authority rejects the forged gcd answer"
    );
    let panic = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        mint_bypass::run(|| {
            assert!(
                wrong_answer_checks(),
                "bootstrap control must actually open the gate"
            );
            panic!("expected bootstrap scope regression panic");
        });
    }));
    assert!(panic.is_err());
    assert!(
        !wrong_answer_checks(),
        "unwinding must close the last bootstrap scope"
    );

    let result = mint_bypass::run(|| {
        mint_bypass::run(|| assert!(wrong_answer_checks()));
        assert!(
            wrong_answer_checks(),
            "an inner return must not close the outer scope"
        );
        let panic = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            mint_bypass::run(|| panic!("expected inner scope regression panic"));
        }));
        assert!(panic.is_err());
        assert!(
            wrong_answer_checks(),
            "an inner unwind must not close the outer scope"
        );
        17
    });
    assert_eq!(result, 17);
    assert!(!wrong_answer_checks());

    let (entered_tx, entered_rx) = std::sync::mpsc::sync_channel(0);
    let (release_tx, release_rx) = std::sync::mpsc::sync_channel(0);
    let worker = std::thread::spawn(move || {
        mint_bypass::run(|| {
            entered_tx.send(()).expect("announce active scope");
            release_rx.recv().expect("release overlapping scope");
        });
    });
    entered_rx.recv().expect("worker owns a bootstrap scope");
    mint_bypass::run(|| assert!(wrong_answer_checks()));
    assert!(
        wrong_answer_checks(),
        "a shorter overlapping scope must not close the worker's"
    );
    release_tx.send(()).expect("finish worker scope");
    worker.join().expect("bootstrap worker");
    assert!(
        !wrong_answer_checks(),
        "the last overlapping scope must close the gate"
    );
    assert!(rfl_checks(
        &env,
        Expr::apps(c("Nat.gcd"), [lit(4), lit(6)]),
        lit(0)
    ));
}

/// The Clean-world pin battery: the `clean-*` rows of `native_fold_canon.tsv`
/// are exactly what Clean's own builders mint, with the ROLES the review
/// assigns (`native_fold_review.rs`): `fold` for a row whose own rules pass
/// the three-way review, `definition` for a row a `fold` row needs as a
/// boundary or a recognized argument, nothing for the rest. A drift fails here
/// with the rows to re-pin; `CLEAN_NATIVE_FOLD_REPIN=1` rewrites them. Every
/// review line is printed (`REVIEW …`, with `--nocapture`) for the record.
#[test]
fn test_clean_canonical_fold_digests_are_pinned() {
    let repin = std::env::var_os("CLEAN_NATIVE_FOLD_REPIN").is_some();
    let build = || -> Vec<(&str, Environment)> {
        vec![
            (
                "clean-prelude",
                Environment::try_with_prelude_uncached().expect("prelude"),
            ),
            (
                "clean-import-prelude",
                Environment::try_with_prelude_for_import().expect("import prelude"),
            ),
            ("clean-bare-nat", {
                let mut env = Environment::new();
                env.init_nat().expect("init_nat");
                env
            }),
        ]
    };
    let worlds = if repin {
        mint_bypass::run(build)
    } else {
        build()
    };
    let mut minted: Vec<(String, String, String, String)> = Vec::new();
    for (world, env) in &worlds {
        // A re-pin reviews the way Lean's kernel folds (every `reduce_nat`
        // head by name) and without the production leg, since the compiled
        // table is the one being replaced; an ordinary run reviews under the
        // compiled table, production leg included, and must reproduce it.
        let reviewed = if repin {
            mint_bypass::run(|| crate::env::native_fold_review::review_world(env, world, false))
        } else {
            crate::env::native_fold_review::review_world(env, world, true)
        };
        for row in &reviewed {
            println!("{}", row.summary_line(world));
            if let Some(pinned) = row.pinned_row(world) {
                minted.push(pinned);
            }
            if !repin && row.role == Some(FoldRole::Fold) {
                if let Err(why) = crate::env::native_fold_review::fold_row_fires(env, &row.name) {
                    panic!("{world}: `fold` row {} does not fire: {why}", row.name);
                }
            }
        }
    }
    minted.sort();
    minted.dedup();
    let mut pinned: Vec<(String, String, String, String)> =
        super::super::native_fold_canon::canonical_fold_rows()
            .into_iter()
            .filter(|(world, _, _, _)| CLEAN_WORLDS.contains(&world.as_str()))
            .collect();
    pinned.sort();
    // A re-pin writes unconditionally (the compiled table can be stale).
    if repin {
        repin_worlds(CLEAN_WORLDS, &minted);
        return;
    }
    if minted == pinned {
        return;
    }
    let missing: Vec<_> = minted.iter().filter(|r| !pinned.contains(r)).collect();
    let stale: Vec<_> = pinned.iter().filter(|r| !minted.contains(r)).collect();
    panic!(
        "native_fold_canon.tsv's clean-* rows drifted from Clean's builders or their review.\n\
         minted but not pinned ({}): {missing:#?}\npinned but not minted ({}): {stale:#?}\n\
         Re-pin with CLEAN_NATIVE_FOLD_REPIN=1 only after confirming each changed\n\
         `fold` row still computes what its definition does.",
        missing.len(),
        stale.len()
    );
}

/// The worlds this battery owns (the `lean-*` and mixed worlds belong to
/// `crates/clean-olean/tests/native_fold_canon_lean.rs`).
const CLEAN_WORLDS: &[&str] = &["clean-prelude", "clean-import-prelude", "clean-bare-nat"];

/// Rewrite the rows of `worlds`, keeping every other world's rows.
fn repin_worlds(worlds: &[&str], rows: &[(String, String, String, String)]) {
    let path =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("src/env/native_fold_canon.tsv");
    let text = std::fs::read_to_string(&path).expect("read native_fold_canon.tsv");
    let mut out: Vec<String> = text
        .lines()
        .filter(|line| {
            line.starts_with('#')
                || (!line.trim().is_empty()
                    && !line
                        .split('\t')
                        .next()
                        .is_some_and(|world| worlds.contains(&world)))
        })
        .map(str::to_string)
        .collect();
    out.extend(
        rows.iter()
            .map(|(w, name, hex, role)| format!("{w}\t{name}\t{hex}\t{role}")),
    );
    std::fs::write(&path, out.join("\n") + "\n").expect("write native_fold_canon.tsv");
}

/// Census (printed with `--nocapture`): every fold key the prelude holds,
/// with its kind and verdict. It asserts the invariant the pin battery exists
/// for: a prelude definition whose closure the table pins is admitted in the
/// role it is pinned with (`fold` admits its own rules, `definition` only its
/// closure), and one the table does not pin is refused as `NotCanonical`.
#[test]
fn test_prelude_fold_key_census() {
    let env = Environment::with_prelude();
    assert!(
        env.nat_literal_extension_canonical(),
        "the prelude's Nat must be the canonical literal carrier"
    );
    let pinned: HashMap<String, String> = super::super::native_fold_canon::canonical_fold_rows()
        .into_iter()
        .filter(|(world, _, _, _)| world == "clean-prelude")
        .map(|(_, name, _, role)| (name, role))
        .collect();
    let mut names: Vec<&Name> = fold_key_universe().iter().collect();
    names.sort_by_cached_key(|n| n.to_string());
    for name in names {
        let kind = match env.get_const(name) {
            None => "absent".to_string(),
            Some(ci) => format!(
                "{:?}{}",
                ci.kind,
                if ci.value.is_some() { "+value" } else { "" }
            ),
        };
        let verdict = env.native_fold_verdict(name);
        println!("CENSUS\t{name}\t{kind}\t{verdict:?}");
        match pinned.get(&name.to_string()).map(String::as_str) {
            Some("fold") => assert!(
                verdict.is_ok(),
                "{name} is a `fold` row of clean-prelude but refused: {verdict:?}"
            ),
            Some("definition" | "refused") => {
                assert!(
                    matches!(
                        verdict,
                        Err(FoldRefusal::NotReviewed { .. } | FoldRefusal::ReviewRefused { .. })
                    ),
                    "{name} is not a `fold` row: its own rules must be off: {verdict:?}"
                );
                assert!(env.native_fold_definition_admitted(name));
            }
            _ => assert!(
                verdict.is_err(),
                "{name} is not pinned in clean-prelude but admitted: {verdict:?}"
            ),
        }
    }
}

/// `Int` literal in the kernel's canonical constructor form.
fn int_lit(v: i128) -> Expr {
    if v >= 0 {
        Expr::app(c("Int.ofNat"), Expr::nat_lit_u128(v.unsigned_abs()))
    } else {
        Expr::app(c("Int.negSucc"), Expr::nat_lit_u128(v.unsigned_abs() - 1))
    }
}

/// `rfl : lhs = rhs` at `Int`.
fn rfl_checks_int(env: &Environment, lhs: Expr, rhs: Expr) -> bool {
    let int = c("Int");
    let ty = Expr::apps(
        Expr::const_(n("Eq"), vec![one()]),
        [int.clone(), lhs, rhs.clone()],
    );
    let proof = Expr::apps(Expr::const_(n("Eq.refl"), vec![one()]), [int, rhs]);
    TypeChecker::new(env).check_type(&proof, &ty).is_ok()
}

/// `Int.div`/`Int.mod` are Lean 4.8.0's T-rounding DEFINITIONS in the
/// prelude, and they compute — three ways that must agree on every sample:
/// the kernel with the head's native fold (admitted because the closure is
/// pinned), the definition's own body by δ-ι (the head never consulted), and
/// Rust's `checked_div`/`checked_rem` (with Lean's `x / 0 = 0`, `x % 0 = x`).
///
/// RED before the definitions (clean 3809edf31 .. e00470647): the prelude
/// declared both as OPAQUE placeholders (`fun _ _ => 0`), native-fold
/// authority refused the fold over an opaque head, and nothing else computed
/// them — `Int.div 12 4 = 3` did not check, so every consumer's integer
/// division/remainder denotation (Trust's `clean_ground` differentials,
/// trust-ir's `.SDiv`/`.SRem`/`castS`) was stuck.
#[test]
fn test_prelude_int_div_mod_are_lean_definitions_that_compute() {
    let env = Environment::with_prelude();
    for head in ["Int.div", "Int.mod"] {
        let info = env.get_const(&n(head)).expect("prelude declares the head");
        assert_eq!(info.kind, ConstantKind::Definition, "{head}");
        assert!(
            env.native_fold_verdict(&n(head)).is_ok(),
            "{head}: {:?}",
            env.native_fold_verdict(&n(head))
        );
    }
    let body = |head: &str| {
        env.get_const(&n(head))
            .and_then(|info| info.value.clone())
            .expect("a definition has a value")
    };
    let (div_body, mod_body) = (body("Int.div"), body("Int.mod"));
    let big = i128::from(i64::MAX);
    let mut samples: Vec<i128> = (-9..=9).collect();
    samples.extend([100, -100, 2_147_483_647, -2_147_483_648, big, -big]);
    let divisors: Vec<i128> = (-4..=4).chain([7, -7, 1_000_003, -1_000_003]).collect();
    for &a in &samples {
        for &b in &divisors {
            let quot = if b == 0 {
                0
            } else {
                a.checked_div(b).expect("no overflow")
            };
            let rem = if b == 0 {
                a
            } else {
                a.checked_rem(b).expect("no overflow")
            };
            for (head, def_body, want) in
                [("Int.div", &div_body, quot), ("Int.mod", &mod_body, rem)]
            {
                let args = [int_lit(a), int_lit(b)];
                assert!(
                    rfl_checks_int(&env, Expr::apps(c(head), args.clone()), int_lit(want)),
                    "{head} {a} {b} must reduce to {want} (kernel, fold admitted)"
                );
                assert!(
                    rfl_checks_int(&env, Expr::apps(def_body.clone(), args), int_lit(want)),
                    "{head} {a} {b} must reduce to {want} (its definition, by δ-ι)"
                );
            }
        }
    }
    // Negative controls: the Euclidean and floor readings are refused.
    assert!(!rfl_checks_int(
        &env,
        Expr::apps(c("Int.mod"), [int_lit(-7), int_lit(3)]),
        int_lit(2)
    ));
    assert!(!rfl_checks_int(
        &env,
        Expr::apps(c("Int.div"), [int_lit(-7), int_lit(2)]),
        int_lit(-4)
    ));
    assert!(!rfl_checks_int(
        &env,
        Expr::apps(div_body, [int_lit(-7), int_lit(2)]),
        int_lit(-4)
    ));
}
