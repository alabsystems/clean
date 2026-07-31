// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **Exact-corpus reject-decode fixtures** for three named `main_v3` reject
//! serials, pinned as in-process regression anchors for the campaign's next
//! flip-gate cycle. Each fixture is the VERBATIM corpus JSON line (extracted by
//! serial via the `.idx` seek-read); the tests parse it in-process and assert the
//! precise structural signature that drives its kernel-reject, so a later
//! translator change that alters how these lines decode is caught here BEFORE a
//! grand replay. See `docs/analysis/zproof-eta-operand-decode.md` for the full
//! decode and the per-serial fixability verdict.
//!
//! The three serials (all `node=AbsP` roots, all `HOL.Orderings` order-class
//! reconstructions):
//!
//! | serial  | reject signature (grand)                             | shape |
//! |---------|------------------------------------------------------|-------|
//! | s102494 | `mismatch expected=isabelle.def.HOL.Not got=FVar`    | `preordering (λa b. le b a) (λa b. lt b a) ⟹ preordering le lt` — **converse/λ-wrapped operands** |
//! | s107054 | `mismatch expected=isabelle.def.HOL.Not got=FVar`    | `class.preorder le lt ⟹ preordering le lt` — **bare operands, clean locale→locale projection** |
//! | s110344 | `contains-free-var`                                  | `OFCLASS('a, order_class) ⟹ class.order le lt` — **class-intro, phantom-param FVar leak** |
//!
//! These drive translate with an EMPTY closure (a handful of parsed decls, never
//! a verify group / never the machine-wide verify lock), so they document the
//! *fail-before* honest state: the recorded proof reaches an unresolved-`PThm`
//! dependency and no statement-level fallback foundationally proves it. The
//! grand-time kernel-reject signatures above additionally require the theorems'
//! full registration closure (375 lines for these three), which is reconstructed
//! only in a full replay — out of scope for a unit fixture by design.

// `IsaProof` / `IsaProvenTheorem` / `IsaTerm` / `IsaType` come through the
// `super::*` glob (re-exported into the parent module); only `parse_proven_theorem`
// needs an explicit path.
use super::super::isabelle_pure::parse_proven_theorem;
use super::*;

/// Serializes EVERY closure replay in this module against the **process-global**
/// `ISA_DUMP_REJECTS` env var. `import_proven_theorems` reads that var at reject
/// time, so a replay running while a *different* test has the var set writes its
/// rejects into the other test's dump file (the observed cross-contamination).
/// The plain [`kv_counts`] acquires this lock for its whole replay; a
/// dump-reading test acquires it FIRST (across `set_var` → replay → read →
/// `remove_var`) and drives the replay through the lock-free [`kv_counts_raw`] so
/// no other replay can interleave while its dump path is installed. Poison-
/// tolerant (the guarded state is only an env var + a temp file).
static REPLAY_LOCK: std::sync::Mutex<()> = std::sync::Mutex::new(());

/// Acquire [`REPLAY_LOCK`], tolerating poisoning.
fn replay_guard() -> std::sync::MutexGuard<'static, ()> {
    REPLAY_LOCK.lock().unwrap_or_else(|e| e.into_inner())
}

const S102494: &str = include_str!(
    "../../../tests/fixtures/isabelle/reject_decode/s102494_eta_converse_operand.jsonl"
);
const S107054: &str =
    include_str!("../../../tests/fixtures/isabelle/reject_decode/s107054_locale_preordering.jsonl");
const S110344: &str = include_str!(
    "../../../tests/fixtures/isabelle/reject_decode/s110344_class_order_freevar.jsonl"
);
/// The minimal registration closure that turns s107054 from a reject into a
/// `KernelVerified` — the four REAL corpus `_def` lines (extracted by serial via
/// the `.idx` seek-read) that register the locale predicates the discharge reads:
/// `partial_preordering_def` (100576), `preordering_axioms_def` (100820),
/// `preordering_def` (100904), `class.preorder_def` (106676).
const S107054_CLOSURE: &str =
    include_str!("../../../tests/fixtures/isabelle/reject_decode/s107054_closure.jsonl");
/// The full 192-line transitive PROOF closure of s110344 (extracted by serial via
/// the corpus `.idx` seek-read, `include_registrations: false`), whose replay
/// reproduces the GRAND-time reject signature exactly: 191/192 `KernelVerified`,
/// s110344 the lone reject. This is the closure §8 of
/// `docs/analysis/zproof-eta-operand-decode.md` uses to reproduce and pin the
/// `apply_thm_expecting_solved` type-sentinel leak in-process (a unit-test-scale
/// replay — never a verify-lock slice/corpus run).
const S110344_CLOSURE: &str =
    include_str!("../../../tests/fixtures/isabelle/reject_decode/s110344_closure.jsonl");
/// Two MORE members of the `contains-free-var` Orderings OfClass→membership
/// family (extracted by serial via the corpus `.idx` seek-read,
/// `include_registrations: false`): s163466 (`ab_semigroup_add_class ⟹ …`) and
/// s164374 (`ab_semigroup_mult_class ⟹ …`). Each is co-blocked exactly like
/// s110344 and flips 191→192 through the OfClass→membership `And.left`/`And.right`
/// superclass projection (`Ctx::project_ofclass_membership`).
const S163466_CLOSURE: &str =
    include_str!("../../../tests/fixtures/isabelle/reject_decode/s163466_closure.jsonl");
const S164374_CLOSURE: &str =
    include_str!("../../../tests/fixtures/isabelle/reject_decode/s164374_closure.jsonl");
/// **The corpus registration line that opens the #106 routing gap.** The ONE
/// real corpus line — `Orderings.class.preorder_def` (s106676) — that the
/// 192-line s110344 proof closure OMITS but every registration-closed corpus
/// slice CONTAINS. Adding it to `S110344_CLOSURE` (making the pre-pass registries
/// corpus-faithful) flips s110344 from `KernelVerified` to a reject: registering
/// the `class.preorder` LOCALE predicate as a poly-inst bakes a poly-inst-flavored
/// `class.preorder` operand into the `preorder_class`/`order_class` class-def
/// bodies, which desyncs against the opaque-flavored operand the OfClass
/// projection / `order_class.axioms` legs reconstruct. See
/// `docs/analysis/zproof-eta-operand-decode.md` §11.
const S110344_CLASS_PREORDER_REG: &str =
    include_str!("../../../tests/fixtures/isabelle/reject_decode/s110344_class_preorder_reg.jsonl");
/// **No-preemption A/B anchors** — four NON-Orderings members of the pin round's
/// 12-closure zero-regression set (§9.3), extracted by serial via the `.idx`
/// seek-read. None carries an OfClass-under-real-membership position the
/// projection touches, so their `KernelVerified`/`rejected` counts are IDENTICAL
/// with the projection ON vs OFF — the load-bearing check that the arm only ever
/// flips the co-blocked family, never a byte of an unrelated verifying proof.
const S76216_CLOSURE: &str =
    include_str!("../../../tests/fixtures/isabelle/reject_decode/s76216_closure.jsonl");
const S132338_CLOSURE: &str =
    include_str!("../../../tests/fixtures/isabelle/reject_decode/s132338_closure.jsonl");
const S132550_CLOSURE: &str =
    include_str!("../../../tests/fixtures/isabelle/reject_decode/s132550_closure.jsonl");
const S144042_CLOSURE: &str =
    include_str!("../../../tests/fixtures/isabelle/reject_decode/s144042_closure.jsonl");

/// **#107 corpus-grade Orderings OfClass family** (the whole `contains-free-var`
/// set §11.3 named). Each member is `OFCLASS('a, <X>_class) ⟹ class.<X> ops` and
/// KVs on its own 192-line minimal closure (via the §10 OfClass projection) — but
/// REJECTS once its SUPERCLASS locale predicate `class.<super>_def` is poly-inst
/// registered (as every corpus slice registers it), because the reconstruction's
/// opaque `class.<super>` operand desyncs against the poly-inst-flavored one the
/// class-def body then bakes (`zproof-eta-operand-decode.md` §11). The
/// `ISA_CLASS_OPERAND_ALIGN` flag makes both poly-inst → the whole family flips
/// back to KV. The three closures below join the already-committed s110344 /
/// s163466 / s164374 closures; each is the proof-dependency closure
/// (`include_registrations:false`), extracted by seed serial via the `main_v3`
/// `.idx` seek-read (`isabelle_slice::extract_slice`).
const S164998_CLOSURE: &str =
    include_str!("../../../tests/fixtures/isabelle/reject_decode/s164998_closure.jsonl");
const S166104_CLOSURE: &str =
    include_str!("../../../tests/fixtures/isabelle/reject_decode/s166104_closure.jsonl");
const S167242_CLOSURE: &str =
    include_str!("../../../tests/fixtures/isabelle/reject_decode/s167242_closure.jsonl");
/// The two SHARED superclass-locale registration lines that open the desync for
/// the `Groups.*` family members (the analogue of `class.preorder_def` / s106676
/// for s110344), each the verbatim corpus `_def` axiom line (seek-read by name):
/// `Groups.class.semigroup_add_def` (s162906) desyncs `ab_semigroup_add` /
/// `monoid_add` / `cancel_semigroup_add`; `Groups.class.semigroup_mult_def`
/// (s163814) desyncs `ab_semigroup_mult` / `monoid_mult`.
const SEMIGROUP_ADD_CLASS_REG: &str =
    include_str!("../../../tests/fixtures/isabelle/reject_decode/semigroup_add_class_reg.jsonl");
const SEMIGROUP_MULT_CLASS_REG: &str =
    include_str!("../../../tests/fixtures/isabelle/reject_decode/semigroup_mult_class_reg.jsonl");

// ── small structural probes over the parsed IsaTerm / IsaProof ─────────────

/// The head constant name and argument spine of a curried application.
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

/// Peel `Pure.prop` / `Trueprop` identity wrappers, counting how many were
/// stripped (the double-`Pure.prop` conclusion of s107054 is a decode marker).
fn strip_prop_wrappers_counted(t: &IsaTerm) -> (&IsaTerm, usize) {
    let mut cur = t;
    let mut n = 0;
    while let IsaTerm::App { f, a } = cur {
        let head = matches!(f.as_ref(), IsaTerm::Const { n, .. }
                if n == "Pure.prop" || n == "HOL.Trueprop" || n == "Trueprop");
        if head {
            n += 1;
            cur = a.as_ref();
        } else {
            break;
        }
    }
    (cur, n)
}

/// `A ⟹ B` (`Pure.imp A B`, modulo wrappers) → `(A, B)`.
fn split_imp(t: &IsaTerm) -> Option<(&IsaTerm, &IsaTerm)> {
    let (t, _) = strip_prop_wrappers_counted(t);
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
    (prems, strip_prop_wrappers_counted(cur).0)
}

/// Whether the proof tree contains a `thm` node whose `tyinst` maps a
/// schematic to a bare `TVar` (the schematic-instantiation shape whose
/// specialization leaks the phantom `'a` parameter on s110344).
fn has_schematic_tvar_tyinst(p: &IsaProof) -> bool {
    let mut found = false;
    fn walk(p: &IsaProof, found: &mut bool) {
        match p {
            IsaProof::Thm { tyinst, .. }
                if tyinst.iter().any(|ti| {
                    matches!(&ti.ty, super::super::isabelle_pure::IsaType::TVar { .. })
                }) =>
            {
                *found = true;
            }
            IsaProof::AbsP { b, .. } | IsaProof::Abst { b, .. } => walk(b, found),
            IsaProof::AppP { f, a } => {
                walk(f, found);
                walk(a, found);
            }
            IsaProof::AppT { f, .. } => walk(f, found),
            _ => {}
        }
    }
    walk(p, &mut found);
    found
}

/// Every mode the escalation runs, in order (mirrors `escalation_modes`'
/// membership/method/instance axes; the trailing `Unfold` pass is where the
/// locale-projection arms fire).
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
/// recorded proof's `PThm` dependencies are absent) — this asserts the reject
/// is a genuine translate/closure defect, never a parser gap, and returns the
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
                // A produced decl must NOT foundationally verify against a
                // prelude-only env (no closure) — otherwise the fixture would
                // not capture the real closure-dependent reject.
                let mut env = Environment::with_prelude();
                let accepted = env
                    .add_decl(Declaration::Theorem {
                        name: clean_kernel::name::Name::from_string("Reject.probe"),
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

// ── s102494 — converse / λ-wrapped operand `preordering` duality ───────────

#[test]
fn decode_s102494_converse_lambda_operands() {
    let thm = parse_proven_theorem(S102494).expect("s102494 parses");
    assert_eq!(thm.serial, 102494);
    // Root proof node is an AbsP (matches `node=AbsP` in the grand reject).
    assert!(matches!(thm.proof, IsaProof::AbsP { .. }), "root is AbsP");

    let (prems, concl) = premises_and_concl(&thm.prop);
    // Two leading premises: the erased sort constraint, then the λ-operand
    // `preordering`; the conclusion is the bare-operand `preordering`.
    assert!(prems.len() >= 2, "type_class + preordering premises");

    // The conclusion is `Orderings.preordering le lt` with BARE operands.
    let (chead, cargs) = app_spine(concl);
    assert!(
        matches!(chead, IsaTerm::Const { n, .. } if n == "Orderings.preordering"),
        "conclusion head is preordering, got {chead:?}"
    );
    assert_eq!(cargs.len(), 2, "preordering is binary");
    assert!(
        cargs.iter().all(|a| matches!(a, IsaTerm::Free { .. })),
        "conclusion operands are BARE frees (less_eq / less)"
    );

    // The `preordering` PREMISE (second premise) applies it to λ-abstractions
    // whose body is the CONVERSE relation `R (Bound 0) (Bound 1)` — the decode
    // that makes this order-*duality*, not a βη-variant, so no structural
    // conjunct match can discharge it.
    let (_, pargs) = app_spine(strip_prop_wrappers_counted(prems[1]).0);
    assert_eq!(pargs.len(), 2, "premise preordering is binary");
    let op1 = pargs[0];
    let IsaTerm::Abs { b: outer, .. } = op1 else {
        panic!("premise operand is λ-wrapped, got {op1:?}");
    };
    let IsaTerm::Abs { b: body, .. } = outer.as_ref() else {
        panic!("premise operand is doubly λ-wrapped");
    };
    // body = `R (Bound 0) (Bound 1)` — arguments FLIPPED (converse).
    let (_, bargs) = app_spine(body);
    assert_eq!(bargs.len(), 2);
    assert!(
        matches!(bargs[0], IsaTerm::Bound { i: 0 }) && matches!(bargs[1], IsaTerm::Bound { i: 1 }),
        "converse: inner arg is Bound 0, outer is Bound 1 (R b a), got {bargs:?}"
    );

    // Fail-before: no mode foundationally verifies against an empty closure.
    let outcomes = drive_all_modes(&thm);
    assert_eq!(outcomes.len(), MODES.len());
}

// ── s107054 — clean `class.preorder ⟹ preordering` locale projection ───────

#[test]
fn decode_s107054_bare_operand_locale_projection() {
    let thm = parse_proven_theorem(S107054).expect("s107054 parses");
    assert_eq!(thm.serial, 107054);
    assert!(matches!(thm.proof, IsaProof::AbsP { .. }), "root is AbsP");

    let (prems, concl) = premises_and_concl(&thm.prop);
    assert!(prems.len() >= 2, "type_class + class.preorder premises");

    // A `class.preorder` premise (the stronger locale the projection reads
    // conjuncts from).
    assert!(
        prems.iter().any(|p| {
            let (h, _) = app_spine(strip_prop_wrappers_counted(p).0);
            matches!(h, IsaTerm::Const { n, .. } if n == "Orderings.class.preorder")
        }),
        "one premise is class.preorder"
    );

    // Conclusion is `preordering le lt` with BARE operands (unlike s102494).
    let (chead, cargs) = app_spine(concl);
    assert!(
        matches!(chead, IsaTerm::Const { n, .. } if n == "Orderings.preordering"),
        "conclusion head is preordering"
    );
    assert!(
        cargs.iter().all(|a| matches!(a, IsaTerm::Free { .. })),
        "conclusion operands are BARE frees — the clean projection shape"
    );

    // Decode marker: the conclusion carries a DOUBLE `Pure.prop` wrapper (the
    // shape `strip_prop_wrappers` must peel through for the locale arm to key).
    let (_, rhs) = split_imp(split_imp(&thm.prop).expect("first imp").1).expect("second imp");
    let (_, nwrap) = strip_prop_wrappers_counted(rhs);
    assert!(
        nwrap >= 2,
        "conclusion has a double Pure.prop wrapper, got {nwrap}"
    );

    let outcomes = drive_all_modes(&thm);
    assert_eq!(outcomes.len(), MODES.len());
}

// ── s107054 PASS-AFTER — conclusion-side nested-locale-predicate reassembly ──

/// With the minimal registration closure present (the four real `_def` lines),
/// s107054 `class.preorder le lt ⟹ preordering le lt` now KernelVerifies through
/// the conclusion-side reassembly arm (`Ctx::discharge_pred_conjunct` step 4):
/// `preordering`'s conjuncts are the nested locale predicates `partial_preordering
/// le` (δ= `refl ∧ trans`) and `preordering_axioms le lt` (δ= the `Not`-carrying
/// strict axiom), which the flat `class.preorder` body (`strict ∧ refl ∧ trans`)
/// supplies conjunct-by-conjunct. The recorded proof still reaches unresolved
/// `PThm` deps (they are NOT in this closure), so the verdict is the new arm's —
/// minted by the kernel re-checking `value : type` δβ-reducing every def-const.
/// This is the pass-after twin of [`decode_s107054_bare_operand_locale_projection`]
/// (which asserts the historical empty-closure decline).
#[test]
fn kernel_verifies_s107054_via_locale_reassembly() {
    let mut thms = Vec::new();
    for line in S107054_CLOSURE.lines().filter(|l| !l.trim().is_empty()) {
        thms.push(parse_proven_theorem(line).expect("closure `_def` line parses"));
    }
    thms.push(parse_proven_theorem(S107054).expect("s107054 parses"));
    let n = thms.len();
    let mut writer = crate::shard::ShardWriter::new();
    let result = crate::hol::isabelle_pure_verify::import_proven_theorems(&thms, &mut writer);
    // Nothing rejected — the only theorem that could reject is s107054 (the four
    // `_def` lines verify reflexively as poly-inst registrations); it now KVs.
    assert_eq!(
        result.rejected, 0,
        "s107054 + its 4 def deps all verify; reasons={:?}",
        result.rejection_reasons
    );
    assert_eq!(
        result.kernel_verified, n,
        "all {n} lines (4 defs + s107054) KernelVerify via the reassembly arm"
    );
}

// ── s110344 — `OFCLASS order_class ⟹ class.order` phantom-param FVar leak ───

#[test]
fn decode_s110344_class_order_freevar_shape() {
    let thm = parse_proven_theorem(S110344).expect("s110344 parses");
    assert_eq!(thm.serial, 110344);
    assert!(matches!(thm.proof, IsaProof::AbsP { .. }), "root is AbsP");

    let (prems, concl) = premises_and_concl(&thm.prop);
    // Single leading `OFCLASS('a, order_class)` sort premise.
    assert_eq!(prems.len(), 1, "one order_class sort premise");
    let (phead, _) = app_spine(strip_prop_wrappers_counted(prems[0]).0);
    assert!(
        matches!(phead, IsaTerm::Const { n, .. } if n == "Orderings.order_class"),
        "premise is the order_class OFCLASS, got {phead:?}"
    );

    // Conclusion is the CLASS predicate `class.order le lt` (the class-intro
    // reconstruction, whose `order_class.axioms` legs leak the phantom param).
    let (chead, _) = app_spine(concl);
    assert!(
        matches!(chead, IsaTerm::Const { n, .. } if n == "Orderings.class.order"),
        "conclusion head is class.order, got {chead:?}"
    );

    // The proof carries the schematic `'a ↦ ?'a` tyinst whose explicit
    // specialization is where the unbound type-param fvar surfaces.
    assert!(
        has_schematic_tvar_tyinst(&thm.proof),
        "proof has a schematic-to-TVar tyinst (the phantom-param source)"
    );

    let outcomes = drive_all_modes(&thm);
    assert_eq!(outcomes.len(), MODES.len());
}

// ── s110344 + family PASS-AFTER — the pin (§9) + the OfClass→membership
//    conjunctionD1 projection (§10), and the projection's no-preemption A/B ─────

/// Parse a closure fixture's non-blank lines into `IsaProvenTheorem`s.
fn parse_closure(closure: &str) -> Vec<IsaProvenTheorem> {
    closure
        .lines()
        .filter(|l| !l.trim().is_empty())
        .map(|l| parse_proven_theorem(l).expect("closure line parses"))
        .collect()
}

/// Replay a closure through the (single-threaded) importer and return
/// `(kernel_verified, rejected)`. Serialized against every other replay + the
/// dump-reading tests (see [`REPLAY_LOCK`]) so a concurrent replay never writes
/// into a dump test's `ISA_DUMP_REJECTS` file.
fn kv_counts(thms: &[IsaProvenTheorem]) -> (usize, usize) {
    let _g = replay_guard();
    kv_counts_raw(thms)
}

/// [`kv_counts`] WITHOUT the [`REPLAY_LOCK`] — for the dump-reading tests that
/// already hold the lock across their `set_var`/read window (calling
/// [`kv_counts`] there would deadlock on the non-reentrant mutex).
fn kv_counts_raw(thms: &[IsaProvenTheorem]) -> (usize, usize) {
    let mut writer = crate::shard::ShardWriter::new();
    let r = crate::hol::isabelle_pure_verify::import_proven_theorems(thms, &mut writer);
    (r.kernel_verified, r.rejected)
}

/// **CORPUS-GRADE routing anchor (#106) — the corpus-representative counterpart
/// of [`kernel_verifies_s110344_via_pin_and_ofclass_projection`].**
///
/// That test KVs s110344 on the 192-line minimal closure. This one shows the KV is
/// an ARTIFACT of the minimal closure OMITTING a registration every real corpus
/// slice carries: adding the single real corpus line
/// `Orderings.class.preorder_def` (s106676) — which the registration-closed
/// flip-gate slice always includes — flips s110344 to a REJECT under the identical
/// driver. s106676 registers the `class.preorder` LOCALE predicate as a poly-inst,
/// which bakes a poly-inst-flavored `class.preorder` operand into the
/// `preorder_class`/`order_class` class-def bodies; the OfClass projection /
/// `order_class.axioms` legs reconstruct the OPAQUE-flavored operand, and no
/// escalation mode makes both consistent (mode 1 wants poly-inst, gets opaque
/// FVar; mode 3 wants opaque, gets poly-inst). This is the ROOT CAUSE of the
/// `isabelle-flip-gate --add` corpus-scale failure for the whole
/// `contains-free-var` Orderings OfClass family (s110344/s163466/s164374/s164998/
/// s166104/s167242). See `docs/analysis/zproof-eta-operand-decode.md` §11.
///
/// FAIL-BEFORE anchor: 192 KV + s110344 the lone reject. It flips to 193/0 when the
/// flavor-consistency fix lands — DO NOT `flip-gate --add` these serials until then
/// (they genuinely do not KV at corpus scale).
#[test]
fn s110344_rejects_under_corpus_class_preorder_registration() {
    let mut thms = parse_closure(S110344_CLOSURE);
    let reg = parse_proven_theorem(S110344_CLASS_PREORDER_REG.trim())
        .expect("class.preorder_def registration line parses");
    assert_eq!(
        reg.serial, 106676,
        "the reg line is Orderings.class.preorder_def"
    );
    thms.push(reg);
    // Serial-ascending = the streaming/topological order the corpus replay uses.
    thms.sort_by_key(|t| t.serial);
    assert_eq!(
        thms.len(),
        193,
        "192-line closure + the one corpus registration"
    );

    // Capture WHICH serial rejects (kv/rejected totals alone cannot tell s110344
    // from the reg line apart). The dump path is pid+time unique.
    let dump = std::env::temp_dir().join(format!(
        "isa_s110344_corpusreg_{}_{}.txt",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map(|d| d.as_nanos())
            .unwrap_or(0)
    ));
    let _replay_lock = replay_guard();
    let _ = std::fs::remove_file(&dump);
    // Already holding REPLAY_LOCK — must use the lock-free `kv_counts_raw`
    // (`kv_counts` re-locks the non-reentrant mutex → deadlock, per its doc).
    let (kv, rej) = crate::process_env::with_serialized_env_vars(
        &[("ISA_DUMP_REJECTS", &dump.to_string_lossy())],
        || kv_counts_raw(&thms),
    );

    assert_eq!(
        rej, 1,
        "exactly one line rejects once class.preorder is poly-inst registered"
    );
    assert_eq!(
        kv, 192,
        "the 191 closure deps + the class.preorder_def registration all KV; s110344 is the reject"
    );
    let dumped = std::fs::read_to_string(&dump).unwrap_or_default();
    let _ = std::fs::remove_file(&dump);
    let sig = dumped
        .lines()
        .find(|l| l.contains("110344"))
        .unwrap_or_else(|| panic!("s110344 must be the reject; dump was:\n{dumped}"));
    // The reported (last-mode) signature is the erased `preorder_class got=True`;
    // the load-bearing Real-mode blocker is the `polyinst.class.preorder` flavor
    // desync (ISA_DUMP_MODES). Either confirms the #106 routing gap.
    assert!(
        sig.contains("preorder"),
        "s110344's reject is the class.preorder membership/flavor seam; got: {sig}"
    );
}

/// **s110344 fully KernelVerifies — both blockers cleared (the §9 sentinel pin
/// AND the §10 OfClass→membership projection).** Replaying s110344's full 192-line
/// proof closure now verifies 192/192 (0 rejected): the residual
/// `expected=isabelle.def.Orderings.preorder_class got=True` seam §9.4 isolated is
/// discharged by projecting the `preorder_class α le lt` superclass membership out
/// of the in-scope `order_class α le lt` hypothesis via `And.left`
/// (`conjunctionD1`) — instead of the vacuous `True.intro`. See
/// [`Ctx::project_ofclass_membership`].
///
/// The A/B second half is the LOAD-BEARING check for BOTH landed fixes:
/// disabling the projection ([`super::set_ofclass_proj_enabled(false)`]) reverts
/// EXACTLY s110344 to a reject (191/1), and its kernel-reject signature is the
/// residual `preorder_class` membership seam — NOT `contains-free-var`, proving
/// the sentinel pin is still intact (a pin revert would surface
/// `contains-free-var` again). So this one test guards the pin, the projection,
/// and their independence.
#[test]
fn kernel_verifies_s110344_via_pin_and_ofclass_projection() {
    let thms = parse_closure(S110344_CLOSURE);
    assert_eq!(thms.len(), 192, "the s110344 closure is 192 lines");

    // (1) Projection ON (production): the whole closure KVs.
    let (kv_on, rej_on) = kv_counts(&thms);
    assert_eq!(
        kv_on, 192,
        "s110344 + its 191 closure deps all KV via the pin + OfClass projection"
    );
    assert_eq!(rej_on, 0, "no rejects with the projection");

    // (2) A/B load-bearing: disable the projection -> exactly s110344 reverts to a
    // reject, its signature the residual `preorder_class` seam (pin intact).
    let dump = std::env::temp_dir().join(format!(
        "isa_s110344_reject_{}_{}.txt",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map(|d| d.as_nanos())
            .unwrap_or(0)
    ));
    let _replay_lock = replay_guard();
    let _ = std::fs::remove_file(&dump);
    // Already holding REPLAY_LOCK — lock-free `kv_counts_raw` (see above).
    let (kv_off, rej_off) = crate::process_env::with_serialized_env_vars(
        &[("ISA_DUMP_REJECTS", &dump.to_string_lossy())],
        || {
            let prev = super::set_ofclass_proj_enabled(false);
            let r = kv_counts_raw(&thms);
            super::set_ofclass_proj_enabled(prev);
            r
        },
    );
    assert_eq!(
        kv_off, 191,
        "without the projection s110344 is the lone reject (191 KV)"
    );
    assert_eq!(rej_off, 1, "s110344 is the lone reject when the arm is off");

    let dumped = std::fs::read_to_string(&dump).unwrap_or_default();
    let _ = std::fs::remove_file(&dump);
    let sig = dumped
        .lines()
        .find(|l| l.contains("110344"))
        .unwrap_or_else(|| panic!("s110344 reject not found in dump:\n{dumped}"));
    assert!(
        !sig.contains("contains-free-var"),
        "the §9 sentinel pin must still be intact (leak gone); signature: {sig}"
    );
    assert!(
        sig.contains("preorder_class"),
        "the projection-off residual is the OfClass->preorder_class membership seam; signature: {sig}"
    );
}

/// **Two MORE family members flip.** s163466 (`ab_semigroup_add_class ⟹ …`) and
/// s164374 (`ab_semigroup_mult_class ⟹ …`) — same `contains-free-var` Orderings
/// OfClass→membership co-blocked family as s110344 — each flips 191→192 through
/// the superclass projection. The A/B OFF run reverts each seed to a reject
/// (load-bearing: the projection is what closes them).
#[test]
fn kernel_verifies_ofclass_family_s163466_s164374() {
    for (serial, closure) in [(163466i64, S163466_CLOSURE), (164374i64, S164374_CLOSURE)] {
        let thms = parse_closure(closure);
        let n = thms.len();

        let prev = super::set_ofclass_proj_enabled(true);
        let (kv_on, rej_on) = kv_counts(&thms);
        super::set_ofclass_proj_enabled(false);
        let (kv_off, _rej_off) = kv_counts(&thms);
        super::set_ofclass_proj_enabled(prev);

        assert_eq!(
            kv_on, n,
            "s{serial} closure ({n} lines) fully KVs with the OfClass projection"
        );
        assert_eq!(rej_on, 0, "s{serial}: no rejects with the projection");
        assert!(
            kv_off < n,
            "s{serial} seed reverts to a reject without the projection (load-bearing): kv_off={kv_off} n={n}"
        );
    }
}

/// **No-preemption A/B.** For four NON-Orderings anchors from the pin round's
/// 12-closure zero-regression set, the OfClass→membership projection must leave
/// the `(KernelVerified, rejected)` counts IDENTICAL with the arm ON vs OFF — it
/// only ever flips the co-blocked family, never a byte of an unrelated proof
/// (`True.intro` at a real-membership expectation was always a guaranteed reject,
/// so no verified line ever reaches the arm). Directly proves the arm is strictly
/// additive.
#[test]
fn ofclass_projection_no_preemption_anchors() {
    for (serial, closure) in [
        (76216i64, S76216_CLOSURE),
        (132338i64, S132338_CLOSURE),
        (132550i64, S132550_CLOSURE),
        (144042i64, S144042_CLOSURE),
    ] {
        let thms = parse_closure(closure);

        let prev = super::set_ofclass_proj_enabled(false);
        let off = kv_counts(&thms);
        super::set_ofclass_proj_enabled(true);
        let on = kv_counts(&thms);
        super::set_ofclass_proj_enabled(prev);

        assert_eq!(
            on, off,
            "s{serial}: the OfClass projection must not change (KV, rejected) — on={on:?} off={off:?}"
        );
    }
}

// ── #107 superclass-conjunct spelling alignment (`ISA_CLASS_OPERAND_ALIGN`) ──
//    the gated additive that flips the corpus-grade Orderings OfClass family. ──

/// Build a corpus-grade closure: the member's proof closure + its desync-trigger
/// superclass-locale registration line, serial-ascending (the streaming replay
/// order).
fn corpus_grade(closure: &str, reg: &str) -> Vec<IsaProvenTheorem> {
    let mut thms = parse_closure(closure);
    thms.push(parse_proven_theorem(reg.trim()).expect("trigger reg line parses"));
    thms.sort_by_key(|t| t.serial);
    thms
}

/// The whole corpus-grade `contains-free-var` Orderings OfClass family
/// (`docs/analysis/zproof-eta-operand-decode.md` §11/§12). Each member
/// `OFCLASS('a, <X>_class) ⟹ class.<X> ops`, in its REGISTRATION-CLOSED corpus
/// context (proof closure + the SUPERCLASS locale `class.<super>_def` every
/// corpus slice carries), is the fail-before anchor the flip-gate `--add`
/// hit (2026-07-19): it REJECTS with the flag OFF (the flavor desync §11.2) and
/// **flips to `KernelVerified` with `ISA_CLASS_OPERAND_ALIGN` ON**.
///
/// For each member the A/B asserts: flag OFF ⇒ `(n-1 KV, 1 rejected)` (the target
/// is the lone reject — the reg line and the 191 proof deps all KV); flag ON ⇒
/// `(n KV, 0 rejected)`. The OFF run is byte-identical to the default (no
/// override) config, asserted once below in
/// [`class_operand_align_off_equals_default`]. The flip is load-bearing (OFF
/// rejects, ON does not), so a regression in the alignment arm reverts the
/// family. The flag defaults OFF in production, so this is a GATED additive: the
/// grand-scale `isabelle-flip-gate --add` under the flag is the corpus validation
/// (§12 lifecycle).
#[test]
fn class_operand_align_flips_corpus_orderings_family() {
    let members: [(i64, &str, &str); 6] = [
        (110344, S110344_CLOSURE, S110344_CLASS_PREORDER_REG),
        (163466, S163466_CLOSURE, SEMIGROUP_ADD_CLASS_REG),
        (164374, S164374_CLOSURE, SEMIGROUP_MULT_CLASS_REG),
        (164998, S164998_CLOSURE, SEMIGROUP_ADD_CLASS_REG),
        (166104, S166104_CLOSURE, SEMIGROUP_MULT_CLASS_REG),
        (167242, S167242_CLOSURE, SEMIGROUP_ADD_CLASS_REG),
    ];
    for (serial, closure, reg) in members {
        let thms = corpus_grade(closure, reg);
        let n = thms.len();

        let off = {
            let _g = super::AlignOverrideGuard::set(false);
            kv_counts(&thms)
        };
        let on = {
            let _g = super::AlignOverrideGuard::set(true);
            kv_counts(&thms)
        };

        assert_eq!(
            off,
            (n - 1, 1),
            "s{serial}: with the flag OFF the corpus-grade closure rejects the target \
             (the desync §11.2) — off={off:?}, n={n}"
        );
        assert_eq!(
            on,
            (n, 0),
            "s{serial}: ISA_CLASS_OPERAND_ALIGN ON flips the whole closure to KV — on={on:?}, n={n}"
        );
    }
}

/// **Byte-identity of the flag-OFF path.** The `ISA_CLASS_OPERAND_ALIGN` guard is
/// `instance_unfold || (flag && is_locale_predicate_const)`, so with the flag OFF
/// the poly-inst arm's guard is exactly the historical `instance_unfold` — every
/// escalation mode is byte-identical to the pre-flag lane. This asserts it
/// directly: the explicit override `Some(false)` produces the IDENTICAL
/// `(KV, rejected)` as the DEFAULT config (no override — the production flag-off
/// state) on the s110344 corpus-grade closure. Together with the whole
/// reject_decode suite passing under the default (flag OFF), this is the landable
/// invariant: flag OFF changes nothing.
#[test]
fn class_operand_align_off_equals_default() {
    let thms = corpus_grade(S110344_CLOSURE, S110344_CLASS_PREORDER_REG);

    // Default (no override installed) — production flag-off; import installs
    // `VerifyConfig::from_env()`, and the test env carries no `ISA_CLASS_OPERAND_ALIGN`.
    let default_counts = kv_counts(&thms);

    let explicit_off = {
        let _g = super::AlignOverrideGuard::set(false);
        kv_counts(&thms)
    };

    assert_eq!(
        default_counts, explicit_off,
        "flag OFF must be byte-identical to the default config — default={default_counts:?} \
         explicit_off={explicit_off:?}"
    );
    // And that shared flag-off verdict is the fail-before: the target rejects.
    assert_eq!(
        default_counts,
        (thms.len() - 1, 1),
        "the s110344 corpus-grade closure is the fail-before anchor with the flag OFF"
    );
}

/// **No-preemption A/B** for `ISA_CLASS_OPERAND_ALIGN`. The four NON-Orderings
/// anchors from §10's zero-regression set carry no locale-predicate class operand
/// the alignment touches, so their `(KernelVerified, rejected)` counts are
/// IDENTICAL with the flag ON vs OFF — the load-bearing proof that the flag flips
/// ONLY the co-blocked family, never a byte of an unrelated verifying proof. (The
/// mission's flag-ON invariant: the §10 four-anchor set's KV count is unchanged
/// under the flag; these are proof closures, not full-KV slices — s76216 carries
/// its two pre-existing non-target rejects either way, which is exactly what
/// "no preemption" means.)
#[test]
fn class_operand_align_no_preemption_anchors() {
    for (serial, closure) in [
        (76216i64, S76216_CLOSURE),
        (132338i64, S132338_CLOSURE),
        (132550i64, S132550_CLOSURE),
        (144042i64, S144042_CLOSURE),
    ] {
        let thms = parse_closure(closure);

        let off = {
            let _g = super::AlignOverrideGuard::set(false);
            kv_counts(&thms)
        };
        let on = {
            let _g = super::AlignOverrideGuard::set(true);
            kv_counts(&thms)
        };

        assert_eq!(
            on, off,
            "s{serial}: ISA_CLASS_OPERAND_ALIGN must not change (KV, rejected) — on={on:?} off={off:?}"
        );
    }
}

/// **#107 align SCALE-PATHOLOGY termination gate**
/// (`docs/analysis/zproof-eta-operand-decode.md` §13/§14). With
/// `ISA_CLASS_OPERAND_ALIGN` ON, a registered LOCALE-PREDICATE class operand
/// embeds via `embed_poly_inst_use`, which re-embeds each op through
/// `embed_element_op`; a nested locale-predicate op re-enters the align arm,
/// DESCENDING the superclass locale-predicate op-DAG. That descent happens
/// entirely inside `embed_term` — it was invisible to the per-line node budget
/// (only `translate_proof` / `translate_proof_expecting` bump), so a class-heavy
/// analysis proof spun ~45 min before the node budget could cut it (the §13 scale
/// pathology that blocked the flag's default-flip). The fix charges each
/// flag-added locale-predicate embed against the SAME per-line budget.
///
/// This exercises the exact mechanism deterministically: a K-deep chain of
/// locale-predicate poly-insts, `c0 → c1 → … → c{K-1}`, embedded flag-ON. Each
/// link re-enters the align arm, so embedding `c0` performs K align-arm entries.
///   - **fail-before proxy** — with NO budget the align recursion runs to full
///     depth (unbounded, exactly the pre-fix behaviour the node budget never
///     charged);
///   - **pass-after** — with a per-line budget `B < K` the recursion is CUT to a
///     bounded `BudgetExceeded` reject (fast, terminating);
///   - **byte-identical flag-OFF** — with the SAME small budget but the flag OFF
///     the align arm never fires (no `instance_unfold`), so the recursion — and
///     its budget bumps — never happen and the embed completes: the bound is
///     specifically the flag-added align path, and flag-OFF is untouched.
///
/// Load-bearing: deleting the `bump_translate_steps` guard in the align arm makes
/// the flag-ON `B < K` embed complete (`is_ok`) instead of `BudgetExceeded`,
/// failing the pass-after assertion.
#[test]
fn class_operand_align_recursion_is_node_budget_bounded() {
    use super::super::isabelle_pure::{IsaTerm, IsaType};

    let tau = IsaType::TFree {
        n: "'a".to_string(),
    };
    // A K-deep chain of locale predicates (names carry ".class." so
    // `is_locale_predicate_const` holds), each registered as a poly-inst whose
    // single op is the next link — so `embed_poly_inst_use(cᵢ)` re-embeds `cᵢ₊₁`
    // and re-enters the align arm. Embedding `c0` thus does K align-arm entries.
    const K: usize = 200;
    let mut registry: super::PolyInstRegistry = std::collections::BTreeMap::new();
    for i in 0..K {
        let ops = if i + 1 < K {
            vec![(format!("Test.class.c{}", i + 1), tau.clone())]
        } else {
            Vec::new()
        };
        registry.insert(
            format!("Test.class.c{i}"),
            super::PolyInstInfo {
                def_name: format!("test.polyinst.c{i}"),
                fn_ty: tau.clone(),
                obj_tvars: Vec::new(),
                extra_type_consts: Vec::new(),
                ops,
                arg_vars: Vec::new(),
                conjuncts: Vec::new(),
                alias_of: None,
            },
        );
    }
    let c0 = IsaTerm::Const {
        n: "Test.class.c0".to_string(),
        t: tau.clone(),
    };

    let embed = |budget: Option<u64>, align: bool| -> Result<(), super::TranslateError> {
        let cfg = crate::hol::isabelle_verify_config::VerifyConfig {
            translate_node_budget: budget,
            class_operand_align: align,
            ..Default::default()
        };
        let _g = cfg.install();
        super::reset_translate_steps();
        let mut ctx = super::Ctx {
            poly_inst_registry: registry.clone(),
            ..Default::default()
        };
        let mut binders: Vec<super::Binder> = Vec::new();
        ctx.embed_term(&c0, &mut binders).map(|_| ())
    };

    // fail-before proxy: unbounded (no budget) — the align recursion runs full depth.
    assert!(
        embed(None, true).is_ok(),
        "flag-ON with no budget embeds the whole K-deep chain (the unbounded pre-fix shape)"
    );
    // pass-after: a per-line budget < K CUTS the align recursion to a bounded reject.
    let cut = embed(Some((K / 2) as u64), true);
    assert!(
        matches!(cut, Err(super::TranslateError::BudgetExceeded(_))),
        "flag-ON with budget {} must bound the align recursion to BudgetExceeded; got {cut:?}",
        K / 2
    );
    // byte-identical / load-bearing: flag-OFF with the SAME small budget does NOT
    // cut — the align arm never fires, so no bump, no recursion.
    assert!(
        embed(Some((K / 2) as u64), false).is_ok(),
        "flag-OFF must be byte-identical: the align arm never fires, so no budget cut"
    );
}

// ── v3.2 reject-frontier census anchors (agent `v32-reject-census`) ─────────
//
// Fail-before anchors for the TOP-3 addressable v3.2 kernel-reject families
// (see `docs/analysis/zproof-v32-reject-census.md`). Each is the VERBATIM corpus
// line (extracted by serial via the `main_v32` `.idx` seek-read); the tests pin
// the decode signature and assert the empty-closure decline, so the next arm
// round starts from an exact reproduction. The cascade weights below are
// reverse-reachability counts over the v3.2 corpus dependency graph
// (`examples/reject_census.rs cascade`).

/// **F1 — the DOMINANT v3.2 kernel-reject family** (`contains-free-var |
/// head=axm:Pure.equal_elim | node=AbsP`, 707 of 859 kernel-rejects). s280734 is
/// its #1 mega-hub: a set-membership congruence (`… ⟹ x ∈ S`) proved by a Pure
/// congruence tower whose `equal_elim` rewrite leaks a free (type) var. Reverse-
/// reachability: **197,815** transitive dependents — s280734 + s280892 alone gate
/// 200,146 of the entire 202,531-line reject cascade (98.8%). Fix hypothesis:
/// interior-node expectation propagation on the Pure congruence tower (generalize
/// `translate_proof_expecting` from proof roots to interior `equal_elim` nodes;
/// `docs/analysis/zproof-reject-census.md` §6). 626/707 use a SINGLE `equal_elim`.
const S280734: &str = include_str!(
    "../../../tests/fixtures/isabelle/reject_decode/s280734_member_equalelim_freevar.jsonl"
);

/// s280892 — the F1 #2 mega-hub (an order-implication congruence `… ⟹ P` over
/// `less_eq`+`imp`); reverse-reachability **191,718**. Same signature as s280734.
const S280892: &str = include_str!(
    "../../../tests/fixtures/isabelle/reject_decode/s280892_order_imp_equalelim_freevar.jsonl"
);

/// The minimal proof-dependency closures (`include_registrations: false`,
/// extracted by seed serial via the `main_v32` `.idx` seek-read) whose in-process
/// replay reproduces the GRAND-time reject of each F1 mega-hub exactly — the
/// fail-before anchors for the F1 interior-`equal_elim` free-var-leak lever
/// (`docs/analysis/zproof-f1-equalelim-lever.md`). s280734 closure = 149 lines
/// (148 KV + seed), s280892 closure = 222 lines (221 KV + seed).
const S280734_CLOSURE: &str =
    include_str!("../../../tests/fixtures/isabelle/reject_decode/s280734_closure.jsonl");
const S280892_CLOSURE: &str =
    include_str!("../../../tests/fixtures/isabelle/reject_decode/s280892_closure.jsonl");

/// **F4 — the BNF/datatype `mor_*` functorial-congruence family** (`mismatch
/// Pi[1]->Sort got=Pi[1]->Sort | head=thm | node=AbsP` — the datatype-package
/// map/morphism registration equations `mor_list`/`mor_option`/`mor_seq`/…;
/// ~47k cascade). s2734228 is the `mor_list` functor congruence — cascade 26,229.
/// Fix hypothesis: register/hand-model the datatype `mor_<T>` map-functor laws, or
/// interior expectation propagation on the shallow `combination`/`reflexive`
/// congruence (`axms=[Pure.combination, Pure.reflexive]`).
const S2734228: &str = include_str!(
    "../../../tests/fixtures/isabelle/reject_decode/s2734228_mor_list_congruence.jsonl"
);

/// **F5 — the ∀-wrapped-equation `got=True` elided-sort-hyp family** (`mismatch
/// Pi[1]->FVar got=True | head=thm | node=AbsP`, 14 members). s5221628 is a
/// `⋀x. lhs = rhs` congruence whose proof discharges a real sort-membership
/// hypothesis slot as `True.intro` — the same seam the LANDED §10 OfClass
/// `conjunctionD1` projection closes, here on an equation's elided sort hyp. Fix
/// hypothesis: project the real sort-membership instead of minting `True.intro`.
const S5221628: &str = include_str!(
    "../../../tests/fixtures/isabelle/reject_decode/s5221628_forall_eq_got_true.jsonl"
);

/// The head constant's full name of a term (after stripping Trueprop/Pure.prop).
fn concl_head_const(t: &IsaTerm) -> Option<&str> {
    let (h, _) = app_spine(strip_prop_wrappers_counted(t).0);
    match h {
        IsaTerm::Const { n, .. } => Some(n.as_str()),
        _ => None,
    }
}

/// Whether the proof tree references a `PAxm` leaf named `name`.
fn proof_refs_axm(p: &IsaProof, name: &str) -> bool {
    match p {
        IsaProof::Axm { name: n, .. } => n == name,
        IsaProof::AbsP { b, .. } | IsaProof::Abst { b, .. } => proof_refs_axm(b, name),
        IsaProof::AppP { f, a } => proof_refs_axm(f, name) || proof_refs_axm(a, name),
        IsaProof::AppT { f, .. } => proof_refs_axm(f, name),
        _ => false,
    }
}

/// F1 — set-membership `Pure.equal_elim` congruence with a leaked free var.
#[test]
fn decode_s280734_membership_equalelim_freevar() {
    let thm = parse_proven_theorem(S280734).expect("s280734 parses");
    assert_eq!(thm.serial, 280734);
    assert!(matches!(thm.proof, IsaProof::AbsP { .. }), "node=AbsP");
    let (prems, concl) = premises_and_concl(&thm.prop);
    assert!(prems.len() >= 2, "type_class + order/membership premises");
    // Conclusion is a set membership (`x ∈ S`).
    let ch = concl_head_const(concl).expect("concl has a const head");
    assert!(ch.ends_with("member"), "concl is set membership, got {ch}");
    // The leak is on a Pure.equal_elim congruence rewrite (the F1 head).
    assert!(
        proof_refs_axm(&thm.proof, "Pure.equal_elim"),
        "F1 signature: head=axm:Pure.equal_elim"
    );
    let outcomes = drive_all_modes(&thm);
    assert_eq!(outcomes.len(), MODES.len());
}

/// F4 — BNF `mor_list` functorial-congruence equation.
#[test]
fn decode_s2734228_mor_list_functor_congruence() {
    let thm = parse_proven_theorem(S2734228).expect("s2734228 parses");
    assert_eq!(thm.serial, 2734228);
    assert!(matches!(thm.proof, IsaProof::AbsP { .. }), "node=AbsP");
    let (prems, concl) = premises_and_concl(&thm.prop);
    // Conclusion is an object equation.
    let ch = concl_head_const(concl).expect("concl has a const head");
    assert!(
        ch == "HOL.eq" || ch == "Pure.eq",
        "concl is an equation, got {ch}"
    );
    // A premise is the BNF list morphism `mor_list`.
    let mentions_mor_list = prems
        .iter()
        .filter_map(|p| concl_head_const(p))
        .any(|n| n.contains("mor_list"));
    assert!(mentions_mor_list, "F4 signature: mor_list functor premise");
    let outcomes = drive_all_modes(&thm);
    assert_eq!(outcomes.len(), MODES.len());
}

/// F5 — ∀-wrapped equation whose proof leaks a `True.intro` sort-hyp discharge.
#[test]
fn decode_s5221628_forall_eq_got_true_sorthyp() {
    let thm = parse_proven_theorem(S5221628).expect("s5221628 parses");
    assert_eq!(thm.serial, 5221628);
    assert!(matches!(thm.proof, IsaProof::AbsP { .. }), "node=AbsP");
    let (_prems, concl) = premises_and_concl(&thm.prop);
    // Conclusion is a universally-quantified body (`All`/`Pure.all (λ…)`).
    let ch = concl_head_const(concl).expect("concl has a const head");
    assert!(
        ch.ends_with("All") || ch.ends_with("all"),
        "concl is ∀-wrapped, got {ch}"
    );
    let outcomes = drive_all_modes(&thm);
    assert_eq!(outcomes.len(), MODES.len());
}

/// F1 #2 mega-hub decode — order-implication `Pure.equal_elim` congruence.
#[test]
fn decode_s280892_order_imp_equalelim_freevar() {
    let thm = parse_proven_theorem(S280892).expect("s280892 parses");
    assert_eq!(thm.serial, 280892);
    assert!(matches!(thm.proof, IsaProof::AbsP { .. }), "node=AbsP");
    // The leak is on a Pure.equal_elim congruence rewrite (the F1 head).
    assert!(
        proof_refs_axm(&thm.proof, "Pure.equal_elim"),
        "F1 signature: head=axm:Pure.equal_elim"
    );
    let outcomes = drive_all_modes(&thm);
    assert_eq!(outcomes.len(), MODES.len());
}

/// Read the single dumped reject signature for `serial` from an `ISA_DUMP_REJECTS`
/// replay of `closure`, asserting exactly `(kv, rejected) = (n-1, 1)` (only the
/// seed rejects — every proof dep KVs).
fn closure_seed_reject_sig(closure: &str, serial: i64) -> String {
    let thms = parse_closure(closure);
    let n = thms.len();
    let dump = std::env::temp_dir().join(format!(
        "isa_f1_{}_{}_{}.txt",
        serial,
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map(|d| d.as_nanos())
            .unwrap_or(0)
    ));
    let _replay_lock = replay_guard();
    let _ = std::fs::remove_file(&dump);
    std::env::set_var("ISA_DUMP_REJECTS", &dump);
    let (kv, rej) = kv_counts_raw(&thms);
    std::env::remove_var("ISA_DUMP_REJECTS");
    assert_eq!(rej, 1, "s{serial}: exactly the seed rejects on its closure");
    assert_eq!(kv, n - 1, "s{serial}: all {n} lines but the seed KV");
    let dumped = std::fs::read_to_string(&dump).unwrap_or_default();
    let _ = std::fs::remove_file(&dump);
    dumped
        .lines()
        .find(|l| l.contains(&serial.to_string()))
        .map(|l| l.rsplit('\t').next().unwrap_or("").to_string())
        .unwrap_or_else(|| panic!("s{serial} must be the dumped reject; dump:\n{dumped}"))
}

/// **F1 interior-`equal_elim` free-var-leak lever — the pass-after anchor.** Both
/// mega-hubs (s280734 set-membership, s280892 order-implication) reproduce the
/// GRAND-time reject on their minimal proof-dep closures. The lever — restoring
/// the ctx param lists when [`Ctx::apply_thm_expecting_solved`] DECLINES (it was
/// side-effect-registering a `const:` op param whose domain carried an unsolved
/// leading TYPE sentinel, which then pi-wrapped into the theorem type+value) —
/// **closes the `contains-free-var` leak**: the reject signature is no longer
/// `contains-free-var` but the residual `mismatch expected=Eq got=Eq` — the
/// deeper serially-dependent congruence-tower wall underneath (r10 "Root A/B/C";
/// see `docs/analysis/zproof-f1-equalelim-lever.md`). This test pins that the
/// leak is closed on BOTH hubs. It is NOT a full flip to `KernelVerified` — DO
/// NOT `flip-gate --add` these serials until the residual tower wall lands.
#[test]
fn f1_equalelim_leak_closed_on_both_hubs() {
    for (serial, closure) in [(280734i64, S280734_CLOSURE), (280892i64, S280892_CLOSURE)] {
        let sig = closure_seed_reject_sig(closure, serial);
        assert!(
            !sig.contains("contains-free-var"),
            "s{serial}: the interior-equal_elim free-var leak must be CLOSED; got: {sig}"
        );
        assert!(
            sig.contains("expected=Eq got=Eq") && sig.contains("Pure.equal_elim"),
            "s{serial}: residual is the Eq-got-Eq congruence-tower wall; got: {sig}"
        );
    }
}

// ── v3.2 census target #2 — the `*_dict` class-method registration gap ───────
//
// The 1,328 `unmapped-axiom` rejects are dominated by overloaded class-method
// dictionary registrations that do not resolve (`numeral_dict` 356, `power_dict`
// 136, `of_nat_dict` 105, `dvd_dict` 103, `of_int`/`sum`/`prod`/`of_bool`/`min`/
// `max`/… tails). Root cause (`docs/analysis/zproof-v32-reject-census.md` §4): the
// method-registration pre-pass recovered the dictionary equation
// `c_class.method ≡ c.method op₁ … opₙ` ONLY from a legacy `Pure.symmetric % LHS %
// RHS %% …_dict` term-application spine ([`scan_method_dicts`]). In the v3.2 zproof
// encoding the `Pure.symmetric` axiom carries its schematic operands in `tminst`
// (as the derivation box's internal `Free` placeholders, not the equation sides),
// so that recovery finds nothing and every `…_dict` leaf declines as
// `unmapped-axiom`. The dictionary rewrite's two goals are instead carried by the
// enclosing `Pure.equal_elim` axiom's `A`/`B` schematic term arguments — `A` the
// dictionary-form goal, `B` the overloaded-method-form goal — which
// [`scan_method_dicts_zproof`] recovers by structurally diffing the two sides.
//
// Each fixture is the VERBATIM corpus seed line (extracted by serial via the
// `main_v32` `.idx` seek-read). The fixtures below are the four largest families.

const S1432612_NUMERAL_DICT: &str =
    include_str!("../../../tests/fixtures/isabelle/reject_decode/s1432612_numeral_dict.jsonl");
const S1572512_POWER_DICT: &str =
    include_str!("../../../tests/fixtures/isabelle/reject_decode/s1572512_power_dict.jsonl");
const S721842_OF_NAT_DICT: &str =
    include_str!("../../../tests/fixtures/isabelle/reject_decode/s721842_of_nat_dict.jsonl");
const S366392_DVD_DICT: &str =
    include_str!("../../../tests/fixtures/isabelle/reject_decode/s366392_dvd_dict.jsonl");

/// **The `*_dict` registration flip — fail-before → registered-after, kernel-
/// checked.** For each of the four largest dictionary families (numeral / power /
/// of_nat / dvd) the seed is a real corpus `…_dict` consumer whose method never
/// registered under the legacy spine recovery. This pins both halves of the flip:
///
///   - **fail-before**: the legacy [`scan_method_dicts`] (`Pure.symmetric`-spine)
///     recovers NOTHING for the method — the zproof encoding hides the equation
///     from it (so the `…_dict` leaf declined as `unmapped-axiom`, exactly the
///     census §4 state);
///   - **pass-after**: the new [`scan_method_dicts_zproof`] `A`/`B` `equal_elim`
///     diff recovers the dictionary equation with the correct dictionary-form impl
///     const (`c_class.method` → `c.method`, [`dict_impl_name`]) and bare-`Const`
///     class operations, and [`register_method_defs`] builds a method `Definition`
///     the KERNEL ACCEPTS — a real, faithful registration (`add_decl` re-checks
///     `value : type`), not a mere name entry. Once registered, the `…_dict` leaf
///     discharges reflexively (`apply_expecting`'s `dict_sides_registered` gate).
#[test]
fn dict_methods_register_from_zproof_equal_elim_rewrite() {
    // (serial, seed line, overloaded method const, dictionary-form impl const).
    let cases: [(i64, &str, &str, &str); 4] = [
        (
            1432612,
            S1432612_NUMERAL_DICT,
            "Num.numeral_class.numeral",
            "Num.numeral.numeral",
        ),
        (
            1572512,
            S1572512_POWER_DICT,
            "Power.power_class.power",
            "Power.power.power",
        ),
        (
            721842,
            S721842_OF_NAT_DICT,
            "Nat.semiring_1_class.of_nat",
            "Nat.semiring_1.of_nat",
        ),
        (
            366392,
            S366392_DVD_DICT,
            "Rings.dvd_class.dvd",
            "Rings.dvd.dvd",
        ),
    ];
    for (serial, line, method, impl_const) in cases {
        let thm = parse_proven_theorem(line).expect("dict seed parses");
        assert_eq!(thm.serial, serial, "fixture serial");

        // FAIL-BEFORE — the legacy spine recovery is blind to the zproof encoding.
        let mut legacy = Vec::new();
        scan_method_dicts(&thm.proof, &mut legacy);
        assert!(
            !legacy.iter().any(|e| e.method_name == method),
            "s{serial}: legacy `Pure.symmetric`-spine recovery must NOT see {method} \
             (the equation is not on the proof spine in the zproof encoding)"
        );

        // PASS-AFTER (recovery) — the `equal_elim` A/B diff recovers the equation.
        let mut zeqs = Vec::new();
        scan_method_dicts_zproof(&thm.proof, &mut zeqs);
        let eq = zeqs
            .iter()
            .find(|e| e.method_name == method)
            .unwrap_or_else(|| {
                panic!(
                    "s{serial}: zproof recovery must recover {method}; recovered: {:?}",
                    zeqs.iter().map(|e| &e.method_name).collect::<Vec<_>>()
                )
            });
        assert_eq!(
            eq.impl_const.0, impl_const,
            "s{serial}: dictionary-form impl const (`_class.` collapsed to `.`)"
        );
        assert!(
            !eq.ops.is_empty(),
            "s{serial}: at least one class operation recovered for {method}"
        );

        // PASS-AFTER (registration) — the built Definition is KERNEL-ACCEPTED
        // against the driver's base environment (HOL base datatypes `Nat`/`Num`
        // registered, exactly as the streaming driver does before the method
        // pre-pass; the numeral/power/of_nat methods carry those ground types).
        let recovered = register_method_defs(&thm, &BTreeMap::new());
        let (_, decl, _) = recovered
            .iter()
            .find(|(n, _, _)| n == method)
            .unwrap_or_else(|| panic!("s{serial}: register_method_defs must yield {method}"));
        let mut env = Environment::with_prelude();
        super::register_datatype_inductives(&mut env);
        assert!(
            env.add_decl(decl.clone()).is_ok(),
            "s{serial}: the kernel must accept the {method} method Definition (faithful registration)"
        );
    }
}
