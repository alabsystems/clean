// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for genuine kernel verification of Metamath theorems.

use super::{kernel_verify_database, kernel_verify_theorem, KernelVerifyOutcome};
use crate::metamath::parse_database;

/// The standard `demo0.mm` database: a complete real Metamath theorem `th1`
/// (`|- t = t`) over a tiny arithmetic/propositional signature, proved from the
/// `$a` axioms `tze, tpl, weq, wim, a1, a2, mp`.
const DEMO0_DB: &str = "\
$c 0 + = -> ( ) term wff |- $.
$v t r s P Q $.
tt $f term t $.
tr $f term r $.
ts $f term s $.
wp $f wff P $.
wq $f wff Q $.
tze $a term 0 $.
tpl $a term ( t + r ) $.
weq $a wff t = r $.
wim $a wff ( P -> Q ) $.
a1 $a |- ( t = r -> ( t = s -> r = s ) ) $.
a2 $a |- ( t + 0 ) = t $.
${
    min $e |- P $.
    maj $e |- ( P -> Q ) $.
    mp $a |- Q $.
$}
th1 $p |- t = t $= tt tze tpl tt weq tt tt weq tt a2 tt tze tpl tt weq tt tze tpl tt weq tt tt weq wim tt a2 tt tze tpl tt tt a1 mp mp $.
";

/// MILESTONE 7: a complete REAL Metamath theorem (`demo0`'s `th1 : |- t = t`),
/// translated from its `.mm` proof and verified by the Clean kernel end to end.
#[test]
fn test_kernel_verify_demo0_th1() {
    let db = parse_database(DEMO0_DB).expect("parse demo0");
    let outcome = kernel_verify_theorem(&db, "th1").expect("verification should run");
    assert_eq!(
        outcome,
        KernelVerifyOutcome::Verified,
        "demo0 th1 must be kernel-verified end-to-end, got {outcome:?}"
    );
}

/// M12 PREDICATE-LOGIC ROUTING. A proof that applies a `$d`-bearing axiom (here an
/// `ax-5`-shaped `|- ( ph -> A. x ph )`, `$d x ph`) is routed to the GROUND guarded
/// path, where the kernel enforces the disjoint-variable condition via `disjPair`
/// guards — so it now VERIFIES (the importer no longer blanket-skips `$d`). A
/// theorem whose proof uses only `$d`-FREE axioms verifies on the fast schematic
/// path even if it declares a (vacuous) `$d`. The rigorous accept/REJECT soundness
/// of the guard is covered by the kernel's `metamath_reflect` tests
/// (`test_dv_register_and_verify_guarded`).
#[test]
fn test_kernel_verify_disjoint_axiom_via_ground_path() {
    let db_src = "\
$c wff setvar |- A. ( -> ) $.
$v x ph $.
vx $f setvar x $.
wph $f wff ph $.
wal $a wff A. x ph $.
$d x ph $.
ax5 $a |- ( ph -> A. x ph ) $.
th5 $p |- ( ph -> A. x ph ) $= vx wph ax5 $.
";
    let db = parse_database(db_src).expect("parse $d-axiom db");

    // th5 applies the $d-bearing ax5 → ground guarded path → VERIFIED (the kernel
    // discharged ax5's $d guard because th5's x, ph are distinct concrete symbols).
    let th5 = kernel_verify_theorem(&db, "th5").expect("verification should run");
    assert_eq!(
        th5,
        KernelVerifyOutcome::Verified,
        "a theorem applying a $d-bearing axiom (with $d satisfied) must verify via \
         the guarded ground path, got {th5:?}"
    );
}

/// A theorem with NO `$d`, whose proof uses only `$d`-free axioms, still verifies
/// on the schematic path — the common (propositional) case is unchanged.
#[test]
fn test_kernel_verify_disjoint_free_theorem_schematic() {
    let db_src = "\
$c wff |- ( -> ) $.
$v P Q $.
wp $f wff P $.
wq $f wff Q $.
wi $a wff ( P -> Q ) $.
ax $a |- ( P -> Q ) $.
thnod $p |- ( P -> Q ) $= wp wq ax $.
";
    let db = parse_database(db_src).expect("parse db");
    let thnod = kernel_verify_theorem(&db, "thnod").expect("verification should run");
    assert_eq!(
        thnod,
        KernelVerifyOutcome::Verified,
        "the $d-free theorem must kernel-verify on the schematic path, got {thnod:?}"
    );
}

/// LITMUS: claiming a conclusion the proof does not establish (`|- t = 0` instead
/// of `|- t = t`) must NOT verify — the kernel rejects the mismatched derivation.
#[test]
fn test_kernel_verify_wrong_conclusion_rejected() {
    // Same proof as th1, but the asserted conclusion is `|- t = 0` (false).
    let bad_db = DEMO0_DB.replace("th1 $p |- t = t $=", "th1 $p |- t = 0 $=");
    let db = parse_database(&bad_db).expect("parse");
    let outcome = kernel_verify_theorem(&db, "th1").expect("verification should run");
    assert_ne!(
        outcome,
        KernelVerifyOutcome::Verified,
        "a proof of `t = t` must not verify the false claim `t = 0`"
    );
}

/// MILESTONE 8: lemma REUSE. `th2 : |- ( t + 0 ) = ( t + 0 )` is proved by
/// applying the earlier `$p` theorem `th1` at the instance `t := ( t + 0 )`. The
/// importer inlines `th1`'s verified proof tree under that substitution and the
/// Clean kernel certifies `th2` — demonstrating kernel-checked lemma reuse.
#[test]
fn test_kernel_verify_lemma_reuse() {
    let db_src = format!("{DEMO0_DB}th2 $p |- ( t + 0 ) = ( t + 0 ) $= tt tze tpl th1 $.\n");
    let db = parse_database(&db_src).expect("parse reuse db");
    let report = kernel_verify_database(&db).expect("verify db");
    assert!(
        report.verified.iter().any(|l| l == "th1"),
        "th1 must verify; report={report:?}"
    );
    assert!(
        report.verified.iter().any(|l| l == "th2"),
        "th2 (which reuses th1) must verify; report={report:?}"
    );
    assert!(report.failed.is_empty(), "no failures expected: {report:?}");
}

/// The batch report verifies every `$p` theorem in `demo0` (just `th1`).
#[test]
fn test_kernel_verify_database_report() {
    let db = parse_database(DEMO0_DB).expect("parse");
    let report = kernel_verify_database(&db).expect("verify db");
    assert_eq!(report.verified, vec!["th1".to_string()]);
    assert!(report.failed.is_empty() && report.skipped.is_empty());
}

/// MILESTONE 9: COMPRESSED proofs (set.mm's format). `z0 : term 0` has the
/// trivial compressed proof `( tze ) A`; `th1c : |- t = t` is the compressed
/// re-encoding of `th1`'s 34-step proof (label table
/// `tt tze tpl weq a2 wim a1 mp` ⇒ codes A..H). Both are decoded and
/// kernel-verified, proving the compressed decoder feeds the same stack machine.
#[test]
fn test_kernel_verify_compressed_proofs() {
    let db_src = format!(
        "{DEMO0_DB}\
z0 $p term 0 $= ( tze ) A $.
th1c $p |- t = t $= ( tze tpl weq a2 wim a1 mp ) ABCADAADAEABCADABCADAADFAEABCAAGHH $.
"
    );
    let db = parse_database(&db_src).expect("parse compressed db");
    let report = kernel_verify_database(&db).expect("verify db");
    assert!(
        report.verified.iter().any(|l| l == "z0"),
        "compressed z0 must verify; report={report:?}"
    );
    assert!(
        report.verified.iter().any(|l| l == "th1c"),
        "compressed th1c must verify; report={report:?}"
    );
    assert!(report.failed.is_empty(), "no failures expected: {report:?}");
}

/// PATTERN B regression. A theorem that DECLARES a `$d` but proves its goal purely
/// from `$d`-free assertions (mirrors set.mm's `ax6v`/`ax6ev`, derived from `ax-6` +
/// `df-ex`) is registered on the PLAIN schematic path (`Π σ, MMThm C`, all-σ — sound,
/// since the proof is `$d`-free). It must NOT be logged as carrying `disjPair` guards:
/// doing so made a REUSER discharge phantom guards into the theorem's `$f` float-hyp
/// slots, a `setvar`-vs-guard type mismatch that wrongly skipped it. Here `pureq`
/// declares `$d x y` but proves `|- x = y` from the `$d`-free `axeq`; `usepureq`
/// reuses `pureq`. BOTH must kernel-verify (the reuser regressed before the fix).
#[test]
fn test_kernel_verify_declared_dollar_d_but_pure_proof_reuses_cleanly() {
    let db_src = "\
$c wff |- setvar = $.
$v x y $.
vx $f setvar x $.
vy $f setvar y $.
weq $a wff x = y $.
axeq $a |- x = y $.
${
    $d x y $.
    pureq $p |- x = y $= vx vy axeq $.
$}
${
    $d x y $.
    usepureq $p |- x = y $= vx vy pureq $.
$}
";
    let db = parse_database(db_src).expect("parse pure-$d db");
    let report = kernel_verify_database(&db).expect("verify db");
    assert!(
        report.verified.iter().any(|l| l == "pureq"),
        "pureq (declares $d, $d-free proof) must verify; report={report:?}"
    );
    assert!(
        report.verified.iter().any(|l| l == "usepureq"),
        "usepureq (reuses the pure-$d pureq) must verify, NOT skip on phantom guards; \
         report={report:?}"
    );
    assert!(report.failed.is_empty(), "no failures expected: {report:?}");
}

/// M13-dummy α-rename (the `sbt`/`sbtru` self-pair fix). A proof's DIRECT dummy
/// work variable is detected via its `$f` float leaf and renamed to a globally-
/// fresh code, while REAL variables are left untouched — so the dummy becomes a
/// fixed constant `∉ vu`, provably distinct from every real variable, and a
/// reuser's substitution can never collide with it (no false `disjPair(y,y)`).
#[test]
fn test_dummy_rename_makes_dummy_fresh_real_vars_untouched() {
    use clean_kernel::metamath_reflect::MMProofTree;
    use hashbrown::HashMap;

    // setvar typecode = 1; dummy y = 5; real var x = 2; a hyp slot var = 100.
    let float_names: hashbrown::HashSet<String> = ["vy".to_string()].into_iter().collect();
    let mut axiom_map: HashMap<String, (Vec<Vec<u64>>, Vec<u64>)> = HashMap::new();
    axiom_map.insert("vy".to_string(), (Vec::new(), vec![1, 5])); // $f setvar y

    // thm step substitutes a var to the form [x, y] = [2, 5]; its arg floats dummy y.
    let tree = MMProofTree::Apply {
        assertion: "thm".to_string(),
        subst: vec![(100, vec![2, 5])],
        args: vec![MMProofTree::Apply {
            assertion: "vy".to_string(),
            subst: vec![],
            args: vec![],
        }],
    };

    let mut direct = std::collections::BTreeMap::new();
    super::collect_direct_dummies(&tree, &float_names, &axiom_map, &mut direct);
    assert_eq!(
        direct.get(&5),
        Some(&(1u64, "vy".to_string())),
        "dummy y (code 5) must be detected via its float leaf"
    );

    let mut code_map: HashMap<u64, u64> = HashMap::new();
    code_map.insert(5, 1u64 << 40); // fresh code, ∉ any variable universe
    let mut float_rename: HashMap<String, String> = HashMap::new();
    float_rename.insert("vy".to_string(), "mm.~dfloat~fresh".to_string());

    let renamed = super::rename_tree_dummies(&tree, &code_map, &float_rename);
    let MMProofTree::Apply { subst, args, .. } = &renamed else {
        panic!("expected Apply");
    };
    assert_eq!(
        subst[0].1,
        vec![2, 1u64 << 40],
        "dummy code 5 → fresh; real var 2 untouched"
    );
    let MMProofTree::Apply { assertion, .. } = &args[0] else {
        panic!("expected float leaf");
    };
    assert_eq!(
        assertion, "mm.~dfloat~fresh",
        "dummy float leaf must be renamed"
    );
}

/// REGRESSION (arithmetic safety): a `$p` theorem whose compressed proof body
/// contains a long run of high-alphabet digits (`U`..=`Y`) makes the number
/// decoder's accumulator (`value = value*5 + digit`) grow past `usize::MAX`.
/// With `overflow-checks` on, the unchecked multiply panicked/aborted the whole
/// verifier from the public `kernel_verify_database` entry point — a DoS on
/// arbitrary untrusted `.mm` input. The decoder must instead treat an
/// out-of-range index as a malformed (skipped) proof and return cleanly.
///
/// 28 consecutive `Y` chars overflow `value*5` on a 64-bit target (27 fit;
/// the 28th multiply exceeds `usize::MAX`). Before the fix this test aborts on
/// overflow; after the fix `kernel_verify_database` returns `Ok` and the
/// malformed theorem is never marked verified.
#[test]
fn test_kernel_verify_compressed_proof_index_overflow_does_not_panic() {
    // 28 'Y' (high digit 5) chars: value*5 overflows usize on the 28th char.
    let overflow_run = "Y".repeat(28);
    let db_src = format!(
        "\
$c wff $.
$v P $.
wp $f wff P $.
wff-ax $a wff P $.
bad $p wff P $= ( wff-ax ) {overflow_run} $.
"
    );
    let db = parse_database(&db_src).expect("parse malicious db");
    // Must NOT panic/abort on the overflowing accumulator.
    let report = kernel_verify_database(&db).expect("verification run should not error out");
    assert!(
        !report.verified.iter().any(|label| label == "bad"),
        "an overflowing compressed proof index must never be marked verified"
    );
}
