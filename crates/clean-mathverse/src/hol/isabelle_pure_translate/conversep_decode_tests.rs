// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **Exact-corpus reject-decode fixtures for the `conversep`/`rel_conversep`
//! relator family** (the 104-strong explicit-converse-const population the
//! converse-duality census flagged as the honest larger foothold — 88 anon + 16
//! named, disjoint from the closed λ-flip duality trio). Each fixture is the
//! VERBATIM `main_v3` corpus JSON line (extracted by serial via the `.idx`
//! seek-read); the tests parse it in-process and assert the precise structural
//! signature that drives its kernel-reject, so a later translator change that
//! alters how these lines decode is caught here BEFORE a grand replay. See
//! `docs/analysis/zproof-conversep-family.md` for the full taxonomy and the
//! per-serial verdicts.
//!
//! **Taxonomy verdict (all bucket (b) — the congruence/wrapper tower wall).**
//! Every one of the 104 is an EQUATION whose two sides mention `Relation.conversep`
//! applied to a hand-modeled BNF/order combinator (`rel_fun`/`rel_sum`/`rel_prod`/
//! `rel_set`/`Grp`/`vimage2p`/`less_eq`/`relcompp`) — a functor/order
//! converse-COMMUTATION fact (`rel_F R\<inverse>\<inverse> = (rel_F R)\<inverse>\<inverse>`,
//! `(r\<inverse>\<inverse> \<le> s\<inverse>\<inverse>) = (r \<le> s)`, `rel_sum … = relcompp (conversep …) (Grp …)`).
//! `Relation.conversep` itself has NO `_def` in the corpus and is NOT hand-modeled,
//! so it embeds OPAQUELY; but crucially NONE of the 104 is
//! δ-reflexive-after-unfolding (there is no `conversep (conversep R) = R`
//! double-converse anywhere in the family — verified by a full census scan), so
//! registering / hand-modeling `conversep` would NOT close them by δβ-reflexivity.
//! The recorded proofs are BNF wrapper-towers that reject at the sort-`AbsP` +
//! multi-tvar `thm`/`Pure.equal_elim` application (`Pi[N]->Eq got=Pi[N]->Eq`,
//! identical props → the crossed-namespace multi-tvar type-instantiation seam that
//! is the documented ≥3-tvar binder-order follow-up), or leak a `True.intro`
//! through an elided-sort-hyp `PBound` (`Pi[1]->FVar got=True`), or bottom in a
//! `Pure.equal_elim` `contains-free-var`. Addressable MECHANICAL count: **0** this
//! cycle — no arm is built (exactly the disposition the λ-flip census reached for
//! its family). These fixtures are honest FAIL-BEFORE anchors.
//!
//! | serial  | name / kind                        | grand reject signature                     | sub-shape |
//! |---------|------------------------------------|--------------------------------------------|-----------|
//! | s1338660| `Basic_BNFs.fun.rel_conversep`     | `Pi[N]->Eq got=Pi[N]->Eq @thm`             | relator-converse commutation |
//! | s1338672| `Basic_BNFs.fun.rel_flip`          | `Pi[6]->Eq got=Pi[6]->Eq @thm`             | relator-flip |
//! | s1338656| `Basic_BNFs.fun.rel_compp_Grp`     | `Pi[4]->Eq got=Pi[4]->Eq @thm`             | relator-composition `Grp` |
//! | s863550 | `Relation.conversep_mono`          | `Pi[4]->Eq got=Pi[4]->Eq @thm`             | order `\<le>`-converse commutation |
//! | s1509774| anon (`∀x. lhs = rhs`)             | `Pi[1]->FVar got=True @thm`                | ∀-wrapped eq, elided-sort-hyp `True.intro` leak |
//! | s4471640| anon (`symp_on` conclusion)        | `contains-free-var @axm:Pure.equal_elim`   | non-eq `symp_on`, equal_elim free-var |
//!
//! Like the eta-operand round's anchors these drive translate with an EMPTY
//! closure (never a verify group / never the machine-wide verify lock): NONE may
//! foundationally verify (the recorded proof's `PThm` dependencies are absent), so
//! the fixtures document the *fail-before* honest state. Reproducing the exact
//! GRAND-time reject signature additionally requires each theorem's full
//! registration + proof closure (a deep BNF wrapper chain), reconstructed only in
//! a full replay — out of scope for a unit fixture by design.

use super::super::isabelle_pure::parse_proven_theorem;
use super::*;

const S1338660: &str =
    include_str!("../../../tests/fixtures/isabelle/reject_decode/s1338660_fun_rel_conversep.jsonl");
const S1338672: &str =
    include_str!("../../../tests/fixtures/isabelle/reject_decode/s1338672_fun_rel_flip.jsonl");
const S1338656: &str =
    include_str!("../../../tests/fixtures/isabelle/reject_decode/s1338656_fun_rel_compp_grp.jsonl");
const S863550: &str =
    include_str!("../../../tests/fixtures/isabelle/reject_decode/s863550_conversep_mono.jsonl");
const S1509774: &str = include_str!(
    "../../../tests/fixtures/isabelle/reject_decode/s1509774_forall_rel_conversep_eq.jsonl"
);
const S4471640: &str = include_str!(
    "../../../tests/fixtures/isabelle/reject_decode/s4471640_symp_on_conversep_freevar.jsonl"
);

// ── small structural probes over the parsed IsaTerm ─────────────────────────

/// The head and argument spine of a curried application.
fn app_spine(t: &IsaTerm) -> (&IsaTerm, Vec<&IsaTerm>) {
    let mut args = Vec::new();
    let mut cur = t;
    while let IsaTerm::App { f, a } = cur {
        args.push(a.as_ref());
        cur = f.as_ref();
    }
    args.reverse();
    (cur, args)
}

/// Peel `Pure.prop` / `Trueprop` / `Pure.all` wrappers, descending into the
/// `Pure.all` body's abstraction so a `∀x. body` reduces to `body`.
fn peel_to_core(t: &IsaTerm) -> &IsaTerm {
    let mut cur = t;
    while let IsaTerm::App { f, a } = cur {
        if matches!(f.as_ref(), IsaTerm::Const { n, .. }
            if n == "Pure.prop" || n == "HOL.Trueprop" || n == "Trueprop")
        {
            cur = a.as_ref();
            continue;
        }
        // `Pure.all (Abs body)` / `HOL.All (Abs body)` → descend into body.
        if matches!(f.as_ref(), IsaTerm::Const { n, .. } if n == "Pure.all" || n == "HOL.All") {
            if let IsaTerm::Abs { b, .. } = a.as_ref() {
                cur = b.as_ref();
                continue;
            }
        }
        break;
    }
    cur
}

/// `A ⟹ B` (`Pure.imp A B`, modulo wrappers) → `(A, B)`.
fn split_imp(t: &IsaTerm) -> Option<(&IsaTerm, &IsaTerm)> {
    let mut cur = t;
    // Strip only the prop wrappers (not `Pure.all`) before matching `imp`.
    while let IsaTerm::App { f, a } = cur {
        if matches!(f.as_ref(), IsaTerm::Const { n, .. }
            if n == "Pure.prop" || n == "HOL.Trueprop" || n == "Trueprop")
        {
            cur = a.as_ref();
        } else {
            break;
        }
    }
    if let IsaTerm::App { f, a: rhs } = cur {
        if let IsaTerm::App { f: impf, a: lhs } = f.as_ref() {
            if matches!(impf.as_ref(), IsaTerm::Const { n, .. } if n == "Pure.imp") {
                return Some((lhs, rhs));
            }
        }
    }
    None
}

/// The premise chain and final conclusion of a `⟹`-nested statement.
fn premises_and_concl(prop: &IsaTerm) -> (Vec<&IsaTerm>, &IsaTerm) {
    let mut prems = Vec::new();
    let mut cur = prop;
    while let Some((lhs, rhs)) = split_imp(cur) {
        prems.push(lhs);
        cur = rhs;
    }
    (prems, cur)
}

/// Whether a subterm anywhere applies/names `Relation.conversep` — the signature
/// that places a line in the census's explicit-converse-const family.
fn mentions_conversep(t: &IsaTerm) -> bool {
    match t {
        IsaTerm::Const { n, .. } => n == "Relation.conversep",
        IsaTerm::App { f, a } => mentions_conversep(f) || mentions_conversep(a),
        IsaTerm::Abs { b, .. } => mentions_conversep(b),
        _ => false,
    }
}

/// Whether the head const of a term equals `name`.
fn head_is(t: &IsaTerm, name: &str) -> bool {
    let (h, _) = app_spine(t);
    matches!(h, IsaTerm::Const { n, .. } if n == name)
}

/// Every mode the escalation runs, in order (mirrors `escalation_modes`'
/// membership/method/instance axes; the trailing `Unfold` pass is where the
/// def-const / projection arms would fire). Shared shape with the eta-operand
/// round's anchors.
const MODES: &[(ClassMembership, MethodEmbed, InstanceEmbed)] = &[
    (
        ClassMembership::Erase,
        MethodEmbed::Opaque,
        InstanceEmbed::Opaque,
    ),
    (
        ClassMembership::Real,
        MethodEmbed::Opaque,
        InstanceEmbed::Opaque,
    ),
    (
        ClassMembership::Real,
        MethodEmbed::DictUnfold,
        InstanceEmbed::Unfold,
    ),
];

/// Drive every escalation mode against an EMPTY closure + empty registries and
/// return the collected honest outcomes. NONE may foundationally verify (the
/// recorded proof's `PThm` dependencies are absent) — this asserts the reject is
/// a genuine translate/closure defect, never a parser gap, and returns the
/// per-mode diagnostic strings for the analysis doc.
fn drive_all_modes(thm: &IsaProvenTheorem) -> Vec<String> {
    let mut out = Vec::new();
    for (m, me, ie) in MODES.iter().copied() {
        let r = translate_theorem(
            thm,
            &BTreeMap::new(),
            &BTreeMap::new(),
            &BTreeMap::new(),
            &BTreeMap::new(),
            &BTreeMap::new(),
            &BTreeMap::new(),
            m,
            me,
            ie,
        );
        match r {
            Ok(Declaration::Theorem { type_, value, .. }) => {
                let mut env = Environment::with_prelude();
                let accepted = env
                    .add_decl(Declaration::Theorem {
                        name: clean_kernel::name::Name::from_string("ConversepReject.probe"),
                        level_params: Vec::new(),
                        type_,
                        value,
                    })
                    .is_ok();
                assert!(
                    !accepted,
                    "fixture must not verify with an empty closure (would not be a faithful reject anchor)"
                );
                out.push(format!(
                    "{m:?}/{me:?}/{ie:?}: translated-but-kernel-rejects"
                ));
            }
            Ok(_) => out.push(format!("{m:?}/{me:?}/{ie:?}: non-theorem decl")),
            Err(e) => out.push(format!("{m:?}/{me:?}/{ie:?}: {e:?}")),
        }
    }
    out
}

/// Common family assertions: parses, `node=AbsP` root (matches every grand reject
/// signature's `node=AbsP`), the statement is in the explicit-`conversep` family,
/// and no empty-closure mode foundationally verifies (fail-before anchor).
fn assert_family_fail_before(json: &str, serial: i64) -> IsaProvenTheorem {
    let thm = parse_proven_theorem(json).expect("conversep fixture parses");
    assert_eq!(thm.serial, serial, "fixture serial");
    assert!(
        matches!(thm.proof, IsaProof::AbsP { .. }),
        "root proof node is AbsP (matches node=AbsP in the grand reject)"
    );
    assert!(
        mentions_conversep(&thm.prop),
        "statement is in the explicit Relation.conversep family"
    );
    let outcomes = drive_all_modes(&thm);
    assert_eq!(outcomes.len(), MODES.len());
    thm
}

// ── s1338660 — `Basic_BNFs.fun.rel_conversep` relator-converse commutation ──

/// `rel_fun (=) R\<inverse>\<inverse> = (rel_fun (=) R)\<inverse>\<inverse>` — the `fun` BNF's relator commutes
/// with converse. `rel_fun` is hand-modeled (a registered BNF-combinator def-const)
/// but `Relation.conversep` embeds opaquely; the equation is NOT δ-reflexive
/// (unfolding both sides needs the `∀`-bound-variable swap under the `(=)` guard),
/// so it bottoms in the recorded BNF wrapper-tower — the grand
/// `Pi[N]->Eq got=Pi[N]->Eq @thm` reject.
#[test]
fn decode_s1338660_fun_rel_conversep_commutation() {
    let thm = assert_family_fail_before(S1338660, 1338660);
    assert_eq!(thm.name, "Basic_BNFs.fun.rel_conversep");
    let (prems, concl) = premises_and_concl(&thm.prop);
    assert!(
        prems.is_empty(),
        "no object premises (only erased sort AbsPs)"
    );
    let core = peel_to_core(concl);
    assert!(head_is(core, "HOL.eq"), "conclusion is an equation");
    // Both operands of the equation mention conversep (the commutation shape).
    let (_, eq_args) = app_spine(core);
    assert_eq!(eq_args.len(), 2, "binary equation");
    assert!(
        eq_args.iter().all(|a| mentions_conversep(a)),
        "both sides of the commutation equation mention conversep"
    );
    // The proof is a thin wrapper: apply the referenced defining theorem to the
    // erased sort witnesses (an `AppP` spine under the sort `AbsP`s).
    let IsaProof::AbsP { b, .. } = &thm.proof else {
        panic!("root AbsP");
    };
    assert!(
        proof_reaches_thm_appp(b),
        "proof applies a referenced `thm` to the sort witnesses (wrapper tower)"
    );
}

// ── s1338672 — `Basic_BNFs.fun.rel_flip` ────────────────────────────────────

#[test]
fn decode_s1338672_fun_rel_flip() {
    let thm = assert_family_fail_before(S1338672, 1338672);
    assert_eq!(thm.name, "Basic_BNFs.fun.rel_flip");
    let (_, concl) = premises_and_concl(&thm.prop);
    let core = peel_to_core(concl);
    assert!(head_is(core, "HOL.eq"), "conclusion is an equation");
    assert!(mentions_conversep(core), "flip equation mentions conversep");
}

// ── s1338656 — `Basic_BNFs.fun.rel_compp_Grp` (relator-composition `Grp`) ────

#[test]
fn decode_s1338656_fun_rel_compp_grp() {
    let thm = assert_family_fail_before(S1338656, 1338656);
    assert_eq!(thm.name, "Basic_BNFs.fun.rel_compp_Grp");
    let (_, concl) = premises_and_concl(&thm.prop);
    let core = peel_to_core(concl);
    assert!(head_is(core, "HOL.eq"), "conclusion is an equation");
    assert!(
        mentions_conversep(core),
        "the composition-Grp equation mentions conversep"
    );
}

// ── s863550 — `Relation.conversep_mono` order `\<le>`-converse commutation ───

/// `(r\<inverse>\<inverse> \<le> s\<inverse>\<inverse>) = (r \<le> s)` — the ORDER-converse cousin (predicate
/// `\<le>`, not a BNF relator). Same wall: not δ-reflexive (the `\<le>` unfolds to a
/// `∀` whose converse needs a bound-variable swap).
#[test]
fn decode_s863550_conversep_mono_order() {
    let thm = assert_family_fail_before(S863550, 863550);
    assert_eq!(thm.name, "Relation.conversep_mono");
    let (_, concl) = premises_and_concl(&thm.prop);
    let core = peel_to_core(concl);
    assert!(head_is(core, "HOL.eq"), "conclusion is an equation");
    // The equation is about `less_eq` on relations (the order-converse family).
    let (_, eq_args) = app_spine(core);
    assert_eq!(eq_args.len(), 2, "binary equation");
    assert!(
        eq_args
            .iter()
            .any(|a| head_is(a, "Orderings.ord_class.less_eq")),
        "an operand is a `\\<le>` on relations"
    );
    assert!(
        mentions_conversep(core),
        "the order equation mentions conversep"
    );
}

// ── s1509774 — anon `∀x. lhs = rhs`, the `Pi[1]->FVar got=True` sub-shape ────

/// A `⟦sort⟧ ⟹ ∀x. (lhs = rhs)` conversep equation whose recorded proof leaks a
/// `True.intro` through an elided-sort-hyp `PBound` (grand
/// `Pi[1]->FVar got=True @thm`). Once peeled through the `Pure.all` binder the
/// conclusion is again an `HOL.eq` — i.e. this is the SAME congruence-tower family,
/// only its proof shape yields a `got=True` (rather than `Eq got=Eq`) reject.
#[test]
fn decode_s1509774_forall_conversep_eq_true_intro_shape() {
    let thm = assert_family_fail_before(S1509774, 1509774);
    assert!(thm.name.is_empty(), "anon intermediate serial");
    let (prems, concl) = premises_and_concl(&thm.prop);
    assert!(
        prems
            .iter()
            .all(|p| head_is(p, "Pure.type") || is_sort_constraint(p)),
        "leading premises are erased sort constraints"
    );
    // The conclusion is `Pure.all (Abs …)` wrapping an equation.
    assert!(
        head_is(concl, "Pure.all") || head_is(concl, "HOL.All"),
        "conclusion is universally quantified"
    );
    let core = peel_to_core(concl);
    assert!(
        head_is(core, "HOL.eq"),
        "the ∀-body is an equation (same congruence-tower family)"
    );
    assert!(
        mentions_conversep(core),
        "the ∀-body equation mentions conversep"
    );
}

// ── s4471640 — anon `symp_on` conclusion, `contains-free-var @equal_elim` ────

/// The lone NON-equation member: a `symp_on` (symmetry-predicate) conclusion with
/// conversep-bearing premises, whose recorded proof bottoms in a `Pure.equal_elim`
/// congruence that leaks a free type variable (grand `contains-free-var
/// @axm:Pure.equal_elim`). Still bucket (b): a congruence tower, not a def gap.
#[test]
fn decode_s4471640_symp_on_conversep_freevar() {
    let thm = assert_family_fail_before(S4471640, 4471640);
    assert!(thm.name.is_empty(), "anon intermediate serial");
    let (prems, concl) = premises_and_concl(&thm.prop);
    let core = peel_to_core(concl);
    assert!(
        head_is(core, "Relation.symp_on"),
        "conclusion head is symp_on (the non-equation member), got {core:?}"
    );
    assert!(
        prems.iter().any(|p| mentions_conversep(p)),
        "a premise carries conversep (the family signature is proof/premise-side here)"
    );
}

/// Whether `p` is (modulo prop wrappers) a `Pure.imp`-free sort membership witness
/// — an `OFCLASS`/`type_class`-shaped constraint the driver erases.
fn is_sort_constraint(p: &IsaTerm) -> bool {
    let (h, _) = app_spine(p);
    matches!(h, IsaTerm::Const { n, .. } if n.ends_with("_class") || n == "Pure.type")
}

/// Whether the proof body reaches a `thm`-headed `AppP` spine (the wrapper-tower
/// shape: apply a referenced defining theorem to the discharged sort witnesses).
fn proof_reaches_thm_appp(p: &IsaProof) -> bool {
    match p {
        IsaProof::AppP { f, .. } => {
            let mut head = f.as_ref();
            while let IsaProof::AppP { f, .. } = head {
                head = f.as_ref();
            }
            matches!(head, IsaProof::Thm { .. }) || proof_reaches_thm_appp(f)
        }
        IsaProof::AbsP { b, .. } | IsaProof::Abst { b, .. } => proof_reaches_thm_appp(b),
        _ => false,
    }
}
