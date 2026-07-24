// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Closure-replay regression over a REAL Isabelle/HOL foundational proof
//! closure.
//!
//! The fixture `tests/fixtures/isabelle/hol_foundational_closure.jsonl` is the
//! verbatim transitive proof closure of a batch of foundational HOL theorems
//! (refl/sym/trans/conjI/impI/mp/conjunct/disjI/iffI/notI), exported from the
//! prebuilt `HOL-Proofs` session (`record_proofs=2`) via
//! `scripts/isabelle/export_pure_proofs.ML` (`export_closure`). Each line is one
//! theorem keyed by its proof-term serial.
//!
//! This test drives the whole closure through the native verifier
//! ([`clean_mathverse::hol::isabelle_pure_verify::import_proven_theorems`]) and
//! records how many theorems clean's kernel verifies to the three foundational
//! axioms. It is an honest progress metric: the count rises as the base-axiom
//! bootstrap grows (see task #15). It asserts only a conservative lower bound so
//! it never silently regresses — bump the bound as the bootstrap expands.

use clean_mathverse::hol::isabelle_pure::parse_proven_theorem;
use clean_mathverse::hol::isabelle_pure_verify::import_proven_theorems;
use clean_mathverse::shard::ShardWriter;

const FIXTURE: &str = include_str!("fixtures/isabelle/hol_foundational_closure.jsonl");

#[test]
fn replays_real_hol_foundational_closure() {
    let theorems: Vec<_> = FIXTURE
        .lines()
        .filter(|l| !l.trim().is_empty())
        .filter_map(|l| parse_proven_theorem(l).ok())
        .collect();
    assert!(
        theorems.len() >= 130,
        "fixture should parse the full closure, got {}",
        theorems.len()
    );

    let mut writer = ShardWriter::new();
    let result = import_proven_theorems(&theorems, &mut writer);

    // Honest progress report (visible with `--nocapture`).
    eprintln!(
        "HOL foundational closure: {} parsed, {} KernelVerified, {} rejected",
        theorems.len(),
        result.kernel_verified,
        result.rejected
    );
    eprintln!("rejection reasons: {:?}", result.rejection_reasons);

    // Conservation: the driver accounts for every theorem (verified or rejected
    // by a recorded reason) — nothing is silently dropped.
    assert_eq!(
        result.kernel_verified + result.rejected,
        theorems.len(),
        "every theorem must be either verified or rejected-with-reason"
    );
    let reason_total: usize = result.rejection_reasons.values().sum();
    assert_eq!(
        reason_total, result.rejected,
        "every rejection has a reason"
    );

    // Soundness invariant: the driver only writes a shard entry AFTER clean's
    // kernel accepts the proof, so the written count equals the verified count.
    assert_eq!(result.kernel_verified, result.names.len());

    // Progress frontier (currently 62/137 KernelVerified): closure replay is
    // all-or-nothing per dependency chain, so a single failing node blocks every
    // dependent (the "unresolved-dep" bucket). Handled: structural nodes
    // (AbsP/Abst/PBound + proof-level redexes), Pure connectives (imp/all/prop) +
    // HOL.All → clean ∀, axioms reflexive/symmetric/transitive/combination/
    // equal_elim/equal_intr/prop_def/impI/mp/subst/ext, the arity facts, a
    // reflexivity short-circuit (statements embedding to a syntactic `a = a`), the
    // HOL type-representation cluster (`itself`/`Pure.type`/OFCLASS, via implicit
    // type-arg reconstruction in `Ctx::apply_thm`), and HOL.True_or_False
    // (classical EM + propext). The fixture is the COMPLETE foundational closure
    // (137 nodes) re-exported with the raw-proof fallback that captures the
    // internal `*_def_raw` nodes the earlier export dropped.
    //
    // Raw-proof `AbsP { h: None }` recovery: the raw export omits each discharged
    // hypothesis term, so `translate_theorem` recovers the OUTERMOST premises from
    // the statement's leading `Pure.imp` chain, and for the `*_def_raw` connective
    // nodes (whose remaining discharges are *internal*) falls back to a
    // kernel-checked statement-level proof — premise-identity, conclusion
    // reflexivity, or definitional unfolding via `Eq.subst` over the `c ≡ def(c)`
    // premise. This lifted the frontier 56 → 62 (the Not/conj/disj/True/False
    // def-raw nodes and their immediate dependents).
    //
    // Remaining: the deeply-nested internal-hypothesis nodes (e.g. the
    // `P = True ⟹ P` family and All/Ex defs, 11–247 omitted internal AbsP each)
    // need full Pure proof-term type inference to recover their local hypothesis
    // types — research-grade — plus the broader eliminators and the cascade they
    // gate. The kernel guarantees every counted theorem is genuinely verified to
    // the three foundational axioms.
    // 67 -> 73: corrected the Pure de Bruijn convention for `PBound`. Isabelle
    // (`Pure/proofterm.ML`, `incr_bv_same` / `prf_loose_Pbvar1`) keeps two
    // SEPARATE counters - `AbsP` bumps the proof level, `Abst` bumps the term
    // level - so a `PBound` indexes `AbsP` binders ONLY, never `Abst`. The
    // translator had counted `Abst` in the `PBound` space too, which collapsed
    // `h C` (a proof applied to a `forall`-bound term, as in the conj/disj
    // eliminators) into `App(BVar0, BVar0)` and kernel-rejected the connective
    // intro nodes. Fixing `proof_bvar`/`shift_proof`/`subst_pbound*`/`beta_step`
    // to skip `Abst` in the proof space unblocks conjI/disjI1/disjI2/notI (plus a
    // bidirectional expected-equation channel through `Pure.equal_elim ->
    // combination/symmetric/reflexive` that pins operands the raw export omits as
    // `% NONE`).
    // 73 -> 122: STATEMENT-LEVEL proofs for the HOL ELIMINATION rules, which
    // bypass the intricate def-raw recorded proofs (full Pure proof-term type
    // inference for their deeply-nested internal `AbsP { h: None }` is
    // research-grade). The statement of each derived rule determines a direct,
    // kernel-checked clean proof, added as new `prove_from_premises` arms:
    //   - `subst_elim_body`: substitution / equality-elimination shapes — an
    //     `App(motive, b)` conclusion from a `motive a` premise and an equation
    //     premise relating `a`/`b` (either direction) via `@Eq.subst`; plus the
    //     `Prop`-level identity-motive case (a bare conclusion `C`, a bare premise
    //     `D`, an equation `C`/`D`) via `@Eq.mp`. Flips subst/ssubst/iffD1/iffD2/
    //     eqTrueE/spec/allE/notE/FalseE/exI/exE/rev_mp/fun_cong/arg_cong/cong/iffI.
    //   - `connective_elim_body`: connective elimination via the impredicative
    //     encoding (a `conj P Q` / `disj P Q` hypothesis IS a generalized
    //     eliminator — apply it to the goal + case proofs). Flips conjunct1/
    //     conjunct2/conjE/disjE.
    // The kernel re-checks every produced term against the embedded statement, so
    // a wrong match is rejected — never miscounted.
    // 122 -> 129: STATEMENT-LEVEL proofs for the HOL CLASSICAL-reasoning rules,
    // built from `Classical.em` + `propext` (foundational closure) instead of the
    // intricate recorded def-raw proofs. A new `classical_rule_proof` /
    // `prove_classical_rule_first` arm recognizes each rule by its embedded
    // statement shape (`Not Q ≡ isabelle.def.HOL.Not Q`, defeq `Q → ∀R.R`;
    // `False ≡ isabelle.def.HOL.False`, defeq `∀R.R`) and emits a direct proof,
    // attempted before the recorded proof:
    //   - `eqTrueI` (`P ⟹ (P = True)`): `propext` of `P ↔ True_enc`.
    //   - `classical` (`(¬P ⟹ P) ⟹ P`): `em P` (P→hp, ¬P→h applied to the HOL
    //     negation coerced from the kernel one).
    //   - `ccontr` (`(¬P ⟹ False) ⟹ P`): `em P`, the ¬P branch discharging
    //     `h (Not P) : ∀R.R` applied to `P`.
    //   - `swap` (`¬P ⟹ (¬Q ⟹ P) ⟹ Q`): `em Q`, the ¬Q branch chaining
    //     premise1 (→P) then premise0 (Not P → ∀R.R) applied to `Q`.
    // Flipping these four also unblocks three dependents (the `unresolved-dep`
    // bucket dropped 7 → 1). Remaining failures are a distinct, deeper bucket
    // (kernel-reject / unmapped-axiom / unsupported-shape on def-raw nodes with
    // omitted internal hypotheses — research-grade Pure proof-term type inference).
    assert!(
        result.kernel_verified >= 129,
        "kernel-verified count regressed below 129: got {}",
        result.kernel_verified
    );
}
