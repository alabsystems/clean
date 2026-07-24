// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **Exact-corpus decode fixtures** for the campaign's long-queued *Thm-spine
//! roots*, *fun-got-Eq* and *Pi[1]->Sort operand-trio* reject serials
//! (`docs/analysis/zproof-thmspine-decode.md`). Each fixture is the VERBATIM
//! `main_v3` corpus JSON line (extracted by serial via the `.idx` seek-read).
//!
//! The decode round's decisive finding is that the eight named targets split
//! into TWO groups by their CURRENT in-process verdict (reproduced here, closure-
//! free, against a prelude-only env — the same `import_proven_theorems` the grand
//! runs):
//!
//! | serial  | decoded statement                              | grand reject sig (v2/v3)                                 | today |
//! |---------|------------------------------------------------|---------------------------------------------------------|-------|
//! | s72426  | `s = t ⟹ t = s`  (`HOL.sym`, sort-explicit)    | `expected=fun got=Eq \| head=thm \| node=AbsP`          | **KV** |
//! | s75490  | `P ⟹ P ∨ Q`  (`disjI1`)                        | `expected=Pi[1]->Sort got=Pi[1]->Sort \| axm:equal_elim \| AppP` | **KV** |
//! | s75542  | `Q ⟹ P ∨ Q`  (`disjI2`)                        | `expected=Pi[1]->Sort got=Pi[1]->Sort \| axm:equal_elim \| AppP` | **KV** |
//! | s75194  | `P ⟹ Q ⟹ P ∧ Q`  (`conjI`)                    | `expected=Pi[1]->Sort got=Pi[1]->Sort \| axm:equal_elim \| AppP` | **KV** |
//! | s310624 | `typedef ⟹ y∈A ⟹ Rep(Abs y)=y` (`Abs_inverse`) | `expected=Pi[1]->FVar got=Pi[1]->FVar \| head=thm \| node=AbsP` | rej |
//! | s311396 | same, elaborated congruence spine              | `expected=Eq got=Eq \| head=thm \| node=AbsP`           | rej |
//!
//! **KV group** (`sym` + the `disjI1`/`disjI2`/`conjI` trio) — these are already
//! discharged by landed FOUNDATIONAL statement-shape arms
//! ([`Ctx::subst_elim_body`]'s `Eq.symm` case; [`prove_connective_law`]), so they
//! `KernelVerified` with an EMPTY closure (kv `0->1`). The pass-after tests are
//! standing regression anchors: if either arm regresses, the KV assertion flips.
//! Their v2-era reject signatures are the recorded-proof `equal_elim`/`sort-abstraction`
//! congruence-tower wall the arms SIDESTEP — hence their absence from the current
//! `main_v3` reject dump (`krej_v3.txt`).
//!
//! **Reject group** (`Abs_inverse` s310624/s311396, and — decoded in the doc,
//! fixtures omitted for size — the `complete_lattice.Inf_lower` s357682 and
//! `Sum_Type` roundtrip s666500) — these bottom on the shared **schematic-`TVar`
//! tyinst → leaked type-param sentinel** wall (`apply_thm`/`apply_thm_explicit`;
//! the r10 phantom-parameter family, the same wall the eta-decode round refuted a
//! candidate for on s110344 and deferred to a dedicated expecting-lane cycle). The
//! fail-before anchors drive them closure-free (→ `unresolved-dep`, the honest
//! empty-closure floor); the FULL-closure kernel-reject that reproduces the exact
//! grand signatures is documented in the analysis doc (the closures are 189–1077
//! lines / up to 85 MB, out of scope for a committed fixture — reproducible via
//! the `.idx` seek-read).

use super::super::isabelle_pure::parse_proven_theorem;
use super::*;

const S72426: &str =
    include_str!("../../../tests/fixtures/isabelle/reject_decode/s72426_sym_fun_got_eq.jsonl");
const S75490: &str =
    include_str!("../../../tests/fixtures/isabelle/reject_decode/s75490_disjI1_pi_sort.jsonl");
const S75542: &str =
    include_str!("../../../tests/fixtures/isabelle/reject_decode/s75542_disjI2_pi_sort.jsonl");
const S75194: &str =
    include_str!("../../../tests/fixtures/isabelle/reject_decode/s75194_conjI_pi_sort.jsonl");
const S310624: &str =
    include_str!("../../../tests/fixtures/isabelle/reject_decode/s310624_absinverse_pi_fvar.jsonl");
const S311396: &str =
    include_str!("../../../tests/fixtures/isabelle/reject_decode/s311396_absinverse_eq_eq.jsonl");
/// The MINIMAL registration closure that flips both `Abs_inverse` serials from
/// reject to `KernelVerified`: the single REAL corpus `_def` line (extracted by
/// serial via the `.idx` seek-read) that registers `Typedef.type_definition` as a
/// 3-conjunct poly-inst predicate whose third conjunct is the guarded universal
/// `∀y. y ∈ A ⟶ Rep (Abs y) = y` the arm projects.
const S310432_TYPEDEF_DEF: &str = include_str!(
    "../../../tests/fixtures/isabelle/reject_decode/s310432_type_definition_def.jsonl"
);
/// A locale-projection-FAMILY exemplar at the exact preemption boundary of the
/// new guarded arm: `partial_preordering le ⟹ preordering_axioms le lt ⟹
/// preordering le lt` (the `preordering.intro` construction). `prove_locale_projection`
/// returns `None` for it TODAY (its conclusion is a whole predicate, not a
/// conjunct), so it is dispatched to `prove_locale_construction` — i.e. it is
/// PRECISELY the kind of line the new Pass 3 (appended to `prove_locale_projection`)
/// could wrongly grab. It verifies under the `class.preorder`/preordering
/// registration closure; the anchor asserts Pass 3 leaves it byte-identical (KV).
const S100912: &str =
    include_str!("../../../tests/fixtures/isabelle/reject_decode/s100912_preordering_intro.jsonl");
/// A second construction-boundary exemplar (schematic-`Var` operands), same role.
const S100914: &str =
    include_str!("../../../tests/fixtures/isabelle/reject_decode/s100914_preordering_intro.jsonl");
/// The four `_def` registration lines that register `partial_preordering`,
/// `preordering_axioms`, `preordering` and `class.preorder` — the closure under
/// which the two construction exemplars verify.
const S107054_CLOSURE: &str =
    include_str!("../../../tests/fixtures/isabelle/reject_decode/s107054_closure.jsonl");

// ── small structural probes (mirror `reject_decode_tests.rs`) ──────────────

/// The head constant/term and argument spine of a curried application.
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

/// Peel `Pure.prop` / `Trueprop` identity wrappers.
fn strip_prop(t: &IsaTerm) -> &IsaTerm {
    let mut cur = t;
    while let IsaTerm::App { f, a } = cur {
        if matches!(f.as_ref(), IsaTerm::Const { n, .. }
            if n == "Pure.prop" || n == "HOL.Trueprop" || n == "Trueprop")
        {
            cur = a.as_ref();
        } else {
            break;
        }
    }
    cur
}

/// `A ⟹ B` (`Pure.imp A B`, modulo wrappers) → `(A, B)`.
fn split_imp(t: &IsaTerm) -> Option<(&IsaTerm, &IsaTerm)> {
    let t = strip_prop(t);
    if let IsaTerm::App { f, a: rhs } = t {
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
    (prems, strip_prop(cur))
}

/// The head-const name of a (wrapper-stripped) application, if any.
fn head_const(t: &IsaTerm) -> Option<&str> {
    match app_spine(strip_prop(t)).0 {
        IsaTerm::Const { n, .. } => Some(n),
        _ => None,
    }
}

/// The proof's spine head — `axm:<name>`, `"thm"`, or the leaf node kind
/// (mirrors `isabelle_pure_verify::dump::spine_head`, the grand reject's `head=`).
fn spine_head(p: &IsaProof) -> String {
    match p {
        IsaProof::Axm { name, .. } => format!("axm:{name}"),
        IsaProof::Thm { .. } => "thm".to_string(),
        IsaProof::AppP { f, .. } | IsaProof::AppT { f, .. } => spine_head(f),
        IsaProof::AbsP { b, .. } | IsaProof::Abst { b, .. } => spine_head(b),
        other => format!("{other:?}"),
    }
}

/// Whether the proof tree contains a `thm` node whose `tyinst` maps a schematic
/// to a bare `TVar` (the schematic-instantiation shape whose specialization leaks
/// the phantom `'a` type-param on the `Abs_inverse` roots).
fn has_schematic_tvar_tyinst(p: &IsaProof) -> bool {
    fn walk(p: &IsaProof) -> bool {
        match p {
            IsaProof::Thm { tyinst, .. } => tyinst
                .iter()
                .any(|ti| matches!(&ti.ty, super::super::isabelle_pure::IsaType::TVar { .. })),
            IsaProof::AbsP { b, .. } | IsaProof::Abst { b, .. } | IsaProof::AppT { f: b, .. } => {
                walk(b)
            }
            IsaProof::AppP { f, a } => walk(f) || walk(a),
            _ => false,
        }
    }
    walk(p)
}

/// Run `import_proven_theorems` on a single line against a prelude-only env (no
/// closure) and return `(kernel_verified, rejected, rejection_reasons)`.
fn import_one(line: &str) -> (usize, usize, BTreeMap<String, usize>) {
    let thm = parse_proven_theorem(line.trim()).expect("fixture parses");
    let mut writer = crate::shard::ShardWriter::new();
    let r = crate::hol::isabelle_pure_verify::import_proven_theorems(
        std::slice::from_ref(&thm),
        &mut writer,
    );
    (r.kernel_verified, r.rejected, r.rejection_reasons)
}

// ── KV group — foundational statement-shape arms, closure-free ─────────────

#[test]
fn decode_s72426_sym_is_kernel_verified() {
    let thm = parse_proven_theorem(S72426.trim()).expect("s72426 parses");
    assert_eq!(thm.serial, 72426);
    assert!(matches!(thm.proof, IsaProof::AbsP { .. }), "root is AbsP");
    // Statement: `type_class ⟹ (s = t) ⟹ (t = s)` — HOL.sym, sort-explicit.
    let (prems, concl) = premises_and_concl(&thm.prop);
    assert!(
        prems.iter().any(|p| head_const(p) == Some("HOL.eq")),
        "an `s = t` premise"
    );
    assert_eq!(head_const(concl), Some("HOL.eq"), "conclusion is `t = s`");
    // The equation operands are TRANSPOSED between premise and conclusion.
    let eq_prem = prems
        .iter()
        .find(|p| head_const(p) == Some("HOL.eq"))
        .expect("eq premise");
    let (_, pa) = app_spine(strip_prop(eq_prem));
    let (_, ca) = app_spine(concl);
    assert_eq!(pa.len(), 2);
    assert_eq!(ca.len(), 2);
    assert_eq!(
        format!("{:?}", pa[0]),
        format!("{:?}", ca[1]),
        "premise lhs == conclusion rhs (swapped)"
    );
    // Pass-after: discharged by `subst_elim_body`'s `Eq.symm` arm — KV, no closure.
    let (kv, rej, _) = import_one(S72426);
    assert_eq!((kv, rej), (1, 0), "sym KernelVerifies closure-free");
}

#[test]
fn decode_s75490_disj_intro1_is_kernel_verified() {
    let thm = parse_proven_theorem(S75490.trim()).expect("s75490 parses");
    assert_eq!(thm.serial, 75490);
    // Recorded proof root is an AppP headed by the `Pure.equal_elim` axiom — the
    // grand reject's `head=axm:Pure.equal_elim | node=AppP`.
    assert!(matches!(thm.proof, IsaProof::AppP { .. }), "root is AppP");
    assert_eq!(spine_head(&thm.proof), "axm:Pure.equal_elim");
    let (prems, concl) = premises_and_concl(&thm.prop);
    assert_eq!(head_const(concl), Some("HOL.disj"), "conclusion is `P ∨ Q`");
    assert_eq!(prems.len(), 1, "single premise `P`");
    // Pass-after: discharged by `prove_connective_law` (disjI1) — KV, no closure.
    let (kv, rej, _) = import_one(S75490);
    assert_eq!((kv, rej), (1, 0), "disjI1 KernelVerifies closure-free");
}

#[test]
fn decode_s75542_disj_intro2_is_kernel_verified() {
    let thm = parse_proven_theorem(S75542.trim()).expect("s75542 parses");
    assert_eq!(thm.serial, 75542);
    assert!(matches!(thm.proof, IsaProof::AppP { .. }), "root is AppP");
    assert_eq!(spine_head(&thm.proof), "axm:Pure.equal_elim");
    let (prems, concl) = premises_and_concl(&thm.prop);
    assert_eq!(head_const(concl), Some("HOL.disj"), "conclusion is `P ∨ Q`");
    assert_eq!(prems.len(), 1, "single premise `Q`");
    let (kv, rej, _) = import_one(S75542);
    assert_eq!((kv, rej), (1, 0), "disjI2 KernelVerifies closure-free");
}

#[test]
fn decode_s75194_conj_intro_is_kernel_verified() {
    let thm = parse_proven_theorem(S75194.trim()).expect("s75194 parses");
    assert_eq!(thm.serial, 75194);
    assert!(matches!(thm.proof, IsaProof::AppP { .. }), "root is AppP");
    assert_eq!(spine_head(&thm.proof), "axm:Pure.equal_elim");
    let (prems, concl) = premises_and_concl(&thm.prop);
    assert_eq!(head_const(concl), Some("HOL.conj"), "conclusion is `P ∧ Q`");
    assert_eq!(prems.len(), 2, "two premises `P`, `Q`");
    let (kv, rej, _) = import_one(S75194);
    assert_eq!((kv, rej), (1, 0), "conjI KernelVerifies closure-free");
}

// ── Reject group — `Abs_inverse`, schematic-TVar tyinst leaked-param wall ───

/// Both `Abs_inverse` shapes: statement `type_definition Rep Abs A ⟹ y∈A ⟹
/// Rep(Abs y)=y`, proof references the generic `Typedef.type_definition.Abs_inverse`
/// (`thm 310610`) under a SCHEMATIC-`TVar` tyinst whose specialization leaks the
/// phantom type-param fvar (`Pi[1]->FVar` for the direct s310624, `Eq got=Eq` for
/// the congruence-wrapped s311396). Closure-free they reject `unresolved-dep`
/// (the recorded proof cannot resolve `thm 310610` etc.); the FULL-closure run
/// reproduces the exact grand kernel-reject (see the analysis doc §3).
fn assert_absinverse_shape(line: &str, serial: i64) {
    let thm = parse_proven_theorem(line.trim()).expect("Abs_inverse parses");
    assert_eq!(thm.serial, serial);
    assert!(matches!(thm.proof, IsaProof::AbsP { .. }), "root is AbsP");
    let (prems, concl) = premises_and_concl(&thm.prop);
    assert!(
        prems
            .iter()
            .any(|p| head_const(p) == Some("Typedef.type_definition")),
        "a `type_definition Rep Abs A` premise"
    );
    assert!(
        prems.iter().any(|p| head_const(p) == Some("Set.member")),
        "a `y ∈ A` membership premise"
    );
    assert_eq!(
        head_const(concl),
        Some("HOL.eq"),
        "conclusion is `Rep (Abs y) = y`"
    );
    // The proof references a generic theorem under a schematic-`TVar` tyinst —
    // the leaked-type-param source.
    assert!(
        has_schematic_tvar_tyinst(&thm.proof),
        "proof carries a schematic-TVar tyinst (the phantom-param source)"
    );
    // Fail-before (closure-free): the recorded proof cannot resolve its `PThm`
    // dependency, so no foundational proof is produced — honest `unresolved-dep`.
    let (kv, rej, reasons) = import_one(line);
    assert_eq!(kv, 0, "no closure-free foundational proof");
    assert_eq!(rej, 1, "rejected closure-free");
    assert!(
        reasons.keys().any(|k| k.contains("unresolved")),
        "closure-free reject is unresolved-dep, got {reasons:?}"
    );
}

#[test]
fn decode_s310624_absinverse_pi_fvar_rejects() {
    assert_absinverse_shape(S310624, 310624);
}

#[test]
fn decode_s311396_absinverse_eq_eq_rejects() {
    assert_absinverse_shape(S311396, 311396);
}

// ── Reject group PASS-AFTER — the guarded-universal conjunct arm (r13) ───────

/// Run `import_proven_theorems` over `closure ++ [seed]` and return
/// `(kernel_verified, rejected, rejection_reasons)`. The closure `_def` lines
/// verify reflexively (poly-inst registrations), so the only line that can reject
/// is `seed`.
fn import_with_closure(closure: &str, seed: &str) -> (usize, usize, BTreeMap<String, usize>) {
    let mut thms: Vec<_> = closure
        .lines()
        .filter(|l| !l.trim().is_empty())
        .map(|l| parse_proven_theorem(l).expect("closure `_def` line parses"))
        .collect();
    thms.push(parse_proven_theorem(seed.trim()).expect("seed parses"));
    let n = thms.len();
    let mut writer = crate::shard::ShardWriter::new();
    let r = crate::hol::isabelle_pure_verify::import_proven_theorems(&thms, &mut writer);
    // Every closure `_def` verifies; assert the whole batch KVs (seed included).
    assert_eq!(r.kernel_verified + r.rejected, n, "all lines accounted for");
    (r.kernel_verified, r.rejected, r.rejection_reasons)
}

/// **PASS-AFTER (the flip).** With the single `Typedef.type_definition_def`
/// registration present, `Abs_inverse` — `type_definition Rep Abs A ⟹ y ∈ A ⟹
/// Rep (Abs y) = y` — now `KernelVerifies` through the guarded-universal conjunct
/// projection ([`Ctx::guarded_conjunct_projection`], `prove_locale_projection`
/// Pass 3): `type_definition`'s third conjunct `∀y. y ∈ A ⟶ Rep (Abs y) = y` is
/// projected, its object type variables are re-solved through the `'a ↔ 'b` swap
/// (the def-side leak the shared `extract_conjunct` cannot fix), its `∀`-telescope
/// opened, the membership guard threaded from the `y ∈ A` premise, and the eq
/// conclusion first-order matched. The recorded proof still reaches unresolved
/// `PThm` deps (they are NOT in this closure), so the verdict is the new arm's —
/// minted by the kernel re-checking `value : type` δβ-reducing the def-const. This
/// is the pass-after twin of [`decode_s310624_absinverse_pi_fvar_rejects`] /
/// [`decode_s311396_absinverse_eq_eq_rejects`] (which assert the historical
/// empty-closure decline).
#[test]
fn kernel_verifies_s310624_via_guarded_conjunct() {
    let (kv, rej, reasons) = import_with_closure(S310432_TYPEDEF_DEF, S310624);
    assert_eq!(
        (kv, rej),
        (2, 0),
        "s310624 + type_definition_def both KV via the guarded arm; reasons={reasons:?}"
    );
}

/// The elaborated-spine twin — same `Abs_inverse` statement, `member` premise
/// LEADING the `type_definition` premise (the order the guarded arm handles
/// order-independently by threading the guard from whichever premise carries it).
#[test]
fn kernel_verifies_s311396_via_guarded_conjunct() {
    let (kv, rej, reasons) = import_with_closure(S310432_TYPEDEF_DEF, S311396);
    assert_eq!(
        (kv, rej),
        (2, 0),
        "s311396 + type_definition_def both KV via the guarded arm; reasons={reasons:?}"
    );
}

// ── NO-PREEMPTION anchors — the locale-family lines stay byte-identical ──────

/// **NO-PREEMPTION.** `s100912` — `partial_preordering le ⟹ preordering_axioms
/// le lt ⟹ preordering le lt` (`preordering.intro`) — verifies TODAY via
/// [`Ctx::prove_locale_construction`]. Crucially, [`Ctx::prove_locale_projection`]
/// returns `None` for it (its conclusion is a whole registered predicate, not a
/// conjunct), so it falls through to construction — making it EXACTLY the kind of
/// line the new guarded Pass 3 (appended to `prove_locale_projection`) could
/// wrongly grab and preempt. Under the `class.preorder`/preordering registration
/// closure it stays `KernelVerified`: Pass 3 declines (the guarded conjunct's
/// operation-headed conclusion `le x z` does not first-order match the predicate
/// conclusion `preordering le lt`), leaving the construction arm's verdict
/// byte-identical. A preemption regression trips this.
#[test]
fn no_preemption_s100912_construction_unchanged() {
    let (kv, rej, reasons) = import_with_closure(S107054_CLOSURE, S100912);
    assert_eq!(
        rej, 0,
        "construction s100912 must stay KV (guarded Pass 3 must not preempt); reasons={reasons:?}"
    );
    assert!(
        kv >= 1,
        "s100912 KernelVerifies via prove_locale_construction"
    );
}

/// A second no-preemption anchor: `s100914`, the same `preordering.intro` at
/// schematic-`Var` operands, byte-identical under the Pass-3 arm.
#[test]
fn no_preemption_s100914_construction_unchanged() {
    let (kv, rej, reasons) = import_with_closure(S107054_CLOSURE, S100914);
    assert_eq!(
        rej, 0,
        "construction s100914 must stay KV (guarded Pass 3 must not preempt); reasons={reasons:?}"
    );
    assert!(
        kv >= 1,
        "s100914 KernelVerifies via prove_locale_construction"
    );
}
