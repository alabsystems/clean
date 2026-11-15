// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `clean check` sorry and axiom verdicts: the closure census and the
//! foundational-axiom identity (split from `cmd_core_tests.rs`).

use crate::cmd_core_tests::check_snippet_allowing_sorry;

// ── The "uses sorry" verdict is the constant closure's (2026-09-28) ──────
//
// MEASURED before the fix, `clean check --json`: on `df2e47d78` every
// `@sorryAx` row below exited 0 with `status: pass` and `sorry_axioms: 0`,
// and `uses_lemma` passed beside a failing `lemma1`; on origin/main
// `f501f6a77` the import-cone gate refused those rows as "cited closure not
// credited" but still reported `sorry_axioms: 0`, and under `--allow-sorry`
// passed them with `sorry_axioms: 0` — the report's only taint evidence said
// the pass was clean.

/// (label, source, the declaration that must fail, expected census)
const SORRY_CLOSURE_ROWS: &[(&str, &str, &str, u64)] = &[
    (
        "non-literal flag",
        "theorem bad : False := @sorryAx False (!true)\n",
        "bad",
        1,
    ),
    (
        "partial application",
        "theorem bad : Bool → False := sorryAx False\n",
        "bad",
        1,
    ),
    (
        "decide-coerced flag",
        "theorem bad : False := @sorryAx False (decide False)\n",
        "bad",
        1,
    ),
    (
        "definition alias",
        "def mysorry := @sorryAx\ntheorem bad : False := mysorry False true\n",
        "bad",
        2,
    ),
    (
        "only through a sorry'd lemma",
        "theorem lemma1 : False := sorry\ntheorem uses_lemma : 1 = 2 := False.elim lemma1\n",
        "uses_lemma",
        2,
    ),
];

#[test]
fn check_refuses_every_closure_sorry_as_uses_sorry_and_counts_it() {
    for (label, code, culprit, census) in SORRY_CLOSURE_ROWS {
        let outcome = check_snippet_allowing_sorry("closure_sorry.lean", code, false);
        assert!(
            outcome.trust_failures.iter().any(|row| row
                .starts_with(&format!("{culprit}: declaration uses"))
                && row.contains("sorry")),
            "[{label}] `{culprit}` must fail as a sorry use: {outcome:?}"
        );
        assert_eq!(
            outcome.sorry_axioms, *census,
            "[{label}] sorry_axioms is the closure census: {outcome:?}"
        );
        assert_eq!(outcome.success_count, 0, "[{label}] {outcome:?}");
    }
}

#[test]
fn check_names_the_lemma_a_dependent_inherits_sorry_through() {
    let (_, code, _, _) = SORRY_CLOSURE_ROWS[4];
    let outcome = check_snippet_allowing_sorry("dep.lean", code, false);
    assert!(
        outcome
            .trust_failures
            .iter()
            .any(|row| row.starts_with("uses_lemma:") && row.contains("(through lemma1)")),
        "{outcome:?}"
    );
}

/// Under `--allow-sorry` the rows pass — and `sorry_axioms` is the evidence
/// that they are sorry-tainted. It read 0 for all of them before the fix.
#[test]
fn allow_sorry_passes_closure_sorry_but_the_census_records_it() {
    for (label, code, _, census) in SORRY_CLOSURE_ROWS {
        let outcome = check_snippet_allowing_sorry("closure_sorry_allowed.lean", code, true);
        assert!(
            outcome.trust_failures.is_empty(),
            "[{label}] --allow-sorry waives the sorry: {outcome:?}"
        );
        assert_eq!(
            outcome.sorry_axioms, *census,
            "[{label}] the waived passes must stay visible as sorry-tainted: {outcome:?}"
        );
    }
}

#[test]
fn a_user_axiom_is_disclosed_and_not_counted_as_sorry() {
    let outcome = check_snippet_allowing_sorry(
        "user_axiom.lean",
        "axiom bogus : (1 : Nat) = 2\ntheorem uses_bogus : (1 : Nat) = 2 := bogus\n",
        false,
    );
    assert_eq!(outcome.success_count, 2, "{outcome:?}");
    assert_eq!(
        outcome.sorry_axioms, 0,
        "an axiom is not a sorry: {outcome:?}"
    );
    assert!(outcome.trust_failures.is_empty(), "{outcome:?}");
    assert_eq!(
        outcome.assumptions,
        vec![
            "bogus: rests on axiom(s) bogus".to_string(),
            "uses_bogus: rests on axiom(s) bogus".to_string(),
        ],
        "both passes must be disclosed as resting on `bogus`: {outcome:?}"
    );
}

#[test]
fn trusted_ay_behind_an_alias_is_refused() {
    let outcome = check_snippet_allowing_sorry(
        "trusted_alias.lean",
        "def myTrusted := @trustedAy\ntheorem bad : False := @myTrusted False\n",
        true,
    );
    assert!(
        outcome
            .trust_failures
            .iter()
            .any(|row| row.starts_with("bad: declaration uses trustedAy (through myTrusted)")),
        "--allow-sorry never waives a solver marker: {outcome:?}"
    );
    assert_eq!(outcome.success_count, 0, "{outcome:?}");
}

// ── Foundational-axiom identity (2026-09-28) ─────────────────────────────
//
// Measured on origin/main 4bacc8770: every source below passed `clean check`
// with `status: pass`, `sorry_axioms: 0` and `assumptions: []` — a proof of
// `False` credited as resting only on the foundation. The axiom classifier
// compared `name.to_string()` against a whitelist that also named
// `proofIrrel`, `Eq.refl`, `WellFounded.fix`, `String.decEq` (none of them a
// kernel axiom), and a one-component `«Quot.sound»` prints exactly like the
// kernel's `Quot.sound`.

/// A user axiom that only SHARES (or prints like) a whitelisted name is an
/// ordinary assumption: the pass stands, and is disclosed by name —
/// unambiguously rendered, so `«Eq.refl»` never reads as the kernel's.
#[test]
fn foundation_name_spoofs_are_disclosed_as_assumptions() {
    for (file, source, axiom) in [
        (
            "poly.lean",
            "axiom proofIrrel {α : Sort u} : α\ntheorem bad : (0 : Nat) = 1 := proofIrrel\n",
            "proofIrrel",
        ),
        (
            "false.lean",
            "axiom proofIrrel : False\ntheorem bad : False := proofIrrel\n",
            "proofIrrel",
        ),
        (
            "root.lean",
            "namespace Foo\naxiom _root_.proofIrrel : False\nend Foo\ntheorem bad : False := proofIrrel\n",
            "proofIrrel",
        ),
        (
            "tactic.lean",
            "axiom proofIrrel : False\ntheorem bad : (2 : Nat) + 2 = 5 := by exact absurd proofIrrel id\n",
            "proofIrrel",
        ),
        (
            "choice.lean",
            "axiom proofIrrel : Nonempty False\ntheorem bad : False := Classical.choice proofIrrel\n",
            "proofIrrel",
        ),
        (
            "eqrefl.lean",
            "axiom «Eq.refl» : False\ntheorem bad : False := «Eq.refl»\n",
            "«Eq.refl»",
        ),
        (
            "wffix.lean",
            "axiom «WellFounded.fix» : False\ntheorem bad : False := «WellFounded.fix»\n",
            "«WellFounded.fix»",
        ),
        (
            "stringdeceq.lean",
            "axiom «String.decEq» : (1 : Nat) = 2\ntheorem bad : (1 : Nat) = 2 := «String.decEq»\n",
            "«String.decEq»",
        ),
        // An invisible or confusable character is shown as an escape, never
        // as itself: on ad89a748b both rows below were disclosed as
        // "bad: rests on axiom(s) propext", the foundation's own spelling.
        (
            "zwsp.lean",
            "axiom «pro\u{200b}pext» : False\ntheorem bad : False := «pro\u{200b}pext»\n",
            "«pro\\u{200b}pext»",
        ),
        (
            "cyrillic.lean",
            "axiom prop\u{435}xt : False\ntheorem bad : False := prop\u{435}xt\n",
            "«prop\\u{435}xt»",
        ),
    ] {
        let outcome = check_snippet_allowing_sorry(file, source, false);
        let row = format!("bad: rests on axiom(s) {axiom}");
        assert!(
            outcome.assumptions.contains(&row),
            "{file}: the pass must be disclosed as `{row}`: {outcome:?}"
        );
        assert_eq!(outcome.sorry_axioms, 0, "{file}: {outcome:?}");
    }

    // A `private` axiom is disclosed by its module-local kernel name, the
    // name Lean 4.8.0's `#print axioms` prints (`_private.<Module>.0.<name>`,
    // G21): unambiguous even beside another module's axiom of the same user
    // name. Outside any Lake package the module is `lean <file>`'s: the file's
    // real path relative to the working directory, and `_stdin` for a file
    // outside it, which a tempdir is (Lean 4.8.0, measured 2026-10-09:
    // `'_private._stdin.0.pt' depends on axioms: [_private._stdin.0.ax]`).
    let outcome = check_snippet_allowing_sorry(
        "private.lean",
        "private axiom proofIrrel : False\ntheorem bad : False := proofIrrel\n",
        false,
    );
    let disclosed: Vec<&String> = outcome
        .assumptions
        .iter()
        .filter(|row| row.starts_with("bad: rests on axiom(s) "))
        .collect();
    assert!(
        matches!(disclosed.as_slice(), [row]
            if row.as_str() == "bad: rests on axiom(s) _private._stdin.0.proofIrrel"),
        "private.lean: the pass must be disclosed by the axiom's module-local name: {outcome:?}"
    );
    assert_eq!(outcome.sorry_axioms, 0, "private.lean: {outcome:?}");

    // An `example` has no name to register; its assumption is disclosed too.
    let outcome = check_snippet_allowing_sorry(
        "example.lean",
        "axiom proofIrrel : False\nexample : False := proofIrrel\n",
        false,
    );
    assert!(
        outcome
            .assumptions
            .contains(&"example: rests on axiom(s) proofIrrel".to_string()),
        "{outcome:?}"
    );
}

/// A declaration whose name is reserved for a kernel-owned axiom — by
/// printed form (`«Quot.sound»`, one component) or structurally — is refused
/// at the declaration, and nothing is credited through it.
#[test]
fn reserved_kernel_names_are_refused_by_check() {
    for (file, source, printed) in [
        (
            "quotsound.lean",
            "axiom «Quot.sound» : False\ntheorem bad : False := «Quot.sound»\n",
            "«Quot.sound»",
        ),
        (
            "choice.lean",
            "axiom «Classical.choice» : False\ntheorem bad : False := «Classical.choice»\n",
            "«Classical.choice»",
        ),
        (
            "quotlift.lean",
            "axiom «Quot.lift» : (0 : Nat) = 1\ntheorem bad : (0 : Nat) = 1 := «Quot.lift»\n",
            "«Quot.lift»",
        ),
        (
            "thm.lean",
            "theorem «Quot.sound» : True := True.intro\ntheorem bad : True := «Quot.sound»\n",
            "«Quot.sound»",
        ),
        (
            "opaque.lean",
            "opaque «Classical.choice» : Nat\n",
            "«Classical.choice»",
        ),
    ] {
        let outcome = check_snippet_allowing_sorry(file, source, false);
        assert!(
            outcome
                .errors
                .iter()
                .any(|error| error.contains("is reserved") && error.contains(printed)),
            "{file}: the reserved name must be refused naming {printed}: {outcome:?}"
        );
        assert!(
            outcome.assumptions.is_empty(),
            "{file}: nothing may be credited through a refused name: {outcome:?}"
        );
    }
}

/// KR1 slice 1 (R132): the stub theory left `with_prelude`, and a theorem
/// that reaches it through an opting-in import says so per declaration. With
/// `import Mathlib.Data.Set.Basic` (whose prelude provider calls
/// `init_set_theory`), `def kr1_card : Type := SetTheory.Cardinal` passes and
/// is disclosed as resting on `SetTheory.Cardinal` by name. Control: without
/// the import the constant is absent and the declaration does not pass, so
/// the stub is not in the default environment.
#[test]
fn a_stub_theory_axiom_is_disclosed_per_declaration() {
    let body = "def kr1_card : Type := SetTheory.Cardinal\n";
    let outcome = check_snippet_allowing_sorry(
        "stub_theory_opt_in.lean",
        &format!("import Mathlib.Data.Set.Basic\n{body}"),
        false,
    );
    assert!(
        outcome
            .assumptions
            .contains(&"kr1_card: rests on axiom(s) SetTheory.Cardinal".to_string()),
        "the opted-in stub axiom is disclosed by name: {outcome:?}"
    );
    let bare = check_snippet_allowing_sorry("stub_theory_default.lean", body, false);
    assert_eq!(
        bare.success_count, 0,
        "control: the default prelude holds no SetTheory stub: {bare:?}"
    );
    assert!(bare.assumptions.is_empty(), "{bare:?}");
}
