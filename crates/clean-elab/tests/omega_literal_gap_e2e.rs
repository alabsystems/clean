// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! End-to-end regression lock: an `omega` proof between two literal bounds
//! costs the same whatever the GAP between them.
//!
//! ## The defect (measured 2026-09-30, `clean check`, killed past 4 GB RSS)
//!
//! ```text
//! theorem s {v : Nat} (h : v < 10)      : v < 1000       := by omega  -- OK, 0.3 GB
//! theorem s {v : Nat} (h : v < 10)      : v < 100000     := by omega  -- > 4 GB after 26 s
//! theorem s {v : Nat} (h : v < 10)      : v < 1000000    := by omega  -- > 4 GB in 0.6 s
//! theorem s {v : Nat} (h : v < 1114112) : v < 4294967296 := by omega  -- > 4 GB
//! theorem s {v : Nat} (h : v < 1114112) : v < 1114113    := by omega  -- OK, 0.06 GB
//! ```
//!
//! `omega`'s direct Nat reconstruction weakened `h` by one `Nat.le.step` per
//! unit of the gap. It blocked `TrustIr/Basic.lean`'s `validChar_lt_two_pow_32`
//! (`v < 0x110000 ⊢ v < 2 ^ 32`, a gap of 4,293,853,184), and with it 51 of the
//! 57 files of `trust_ir-semantics`, which all import that module. The term is
//! now one literal comparison the kernel decides by its `Nat.ble` fold.
//!
//! Every PASS gate drives the pipeline `clean check` drives: the theorem must
//! register (the kernel re-checks the assembled proof) with an axiom closure
//! within `propext` / `Quot.sound` / `Classical.choice` — no `sorry`, no
//! trust marker, no domain axiom. The cost gate is the proof's TREE SIZE — deterministic,
//! unlike a clock — plus a generous wall-clock bound. ORDER MATTERS: the size
//! is first compared across two gaps small enough to stay cheap with the
//! defect back, so a regression fails there instead of building a
//! four-billion-node term on a shared machine.
//!
//! Follow-ups locked here: `norm_num`'s ground Nat comparison witness had the
//! same unary shape (capped at a 4096 gap); linarith's contradiction closer
//! read a STRICT hypothesis as a `≤` between the same endpoints; and omega's
//! replay took every in-scope hypothesis as part of the refutation. The last
//! two left `validChar_of_lt_256` and `not_validChar_above_max` unproved. Each
//! has a negative control that must be refused.

use std::collections::BTreeSet;
use std::time::{Duration, Instant};

use clean_kernel::env::Environment;
use clean_kernel::expr::ExprKind;
use clean_kernel::{Expr, Name};

use clean_elab::{elaborate_decl_and_register, preprocess_decl_with_context, FileContext};
use clean_parser::parse_file;

/// A proof of one of these theorems is two binders and a handful of constants.
/// The old proof of the smallest gap here (990) had tens of thousands of nodes.
const MAX_PROOF_NODES: usize = 200;

/// Generous bound for elaborating one small theorem in a debug build on a
/// loaded machine. The 2^32-gap proof used to never finish.
const MAX_ELAB_TIME: Duration = Duration::from_secs(20);

fn try_elaborate_into(env: &mut Environment, source: &str) -> Result<(), String> {
    let mut file_ctx = FileContext::new();
    let decls = parse_file(source).map_err(|e| format!("parse error: {e:?}"))?;
    for decl in &decls {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        elaborate_decl_and_register(env, &processed).map_err(|e| e.to_string())?;
    }
    Ok(())
}

/// Nodes of `e` counted as a tree — what every kernel walk over it pays.
fn tree_size(e: &Expr) -> usize {
    let mut stack: Vec<&Expr> = vec![e];
    let mut n = 0usize;
    while let Some(cur) = stack.pop() {
        n += 1;
        match cur.kind() {
            ExprKind::App(f, a) => stack.extend([f.as_ref(), a.as_ref()]),
            ExprKind::Lam(_, t, b) | ExprKind::Pi(_, t, b) => {
                stack.extend([t.as_ref(), b.as_ref()]);
            }
            ExprKind::Let(_, t, v, b, _) => stack.extend([t.as_ref(), v.as_ref(), b.as_ref()]),
            ExprKind::Proj(_, _, x) | ExprKind::MData(_, x) => stack.push(x.as_ref()),
            _ => {}
        }
    }
    n
}

/// The axioms in `name`'s transitive closure that are NOT the kernel's
/// foundation.
///
/// `Environment::axiom_deps` drops exactly the kernel's canonical foundational
/// declarations — structurally named AND with the exact canonical statement:
/// `propext`, `Quot.sound`, `Classical.choice`, plus the `Quot` primitives,
/// which Lean 4 counts as kernel built-ins (`QuotVal`), not axioms. Trust
/// markers (`sorry`, `sorryAx`, `trustedArith`, `trustedAy`) are never
/// foundational and stay in the set. So an EMPTY answer is the CLAUDE.md
/// "prove" rule: the closure lies within `propext` / `Quot.sound` /
/// `Classical.choice`.
fn non_foundational_axioms(env: &Environment, name: &str) -> BTreeSet<Name> {
    env.axiom_deps(&Name::from_string(name))
        .unwrap_or_else(|| panic!("`{name}` must have an axiom closure"))
        .into_iter()
        .collect()
}

/// Elaborate `source` (defining `name` last) into a fresh prelude environment
/// and assert it registers, PROVED (closure within the foundational axioms,
/// [`non_foundational_axioms`]), within the time bound. Returns the tree size
/// of `name`'s proof.
fn proof_size(name: &str, source: &str) -> usize {
    let mut env = Environment::with_prelude();
    let start = Instant::now();
    try_elaborate_into(&mut env, source)
        .unwrap_or_else(|e| panic!("`{name}` must elaborate and kernel-check: {e}"));
    let elapsed = start.elapsed();
    assert!(
        elapsed < MAX_ELAB_TIME,
        "`{name}` took {elapsed:?} (bound {MAX_ELAB_TIME:?})"
    );
    let info = env
        .get_const(&Name::from_string(name))
        .unwrap_or_else(|| panic!("`{name}` must be registered"));
    let proof = info
        .value
        .as_ref()
        .unwrap_or_else(|| panic!("`{name}` must carry a proof value"));
    let domain = non_foundational_axioms(&env, name);
    assert!(
        domain.is_empty(),
        "`{name}` must be proved from propext / Quot.sound / Classical.choice alone; its \
         axiom closure also reaches {domain:?}"
    );
    let nodes = tree_size(proof);
    eprintln!("{name}: {elapsed:?}, {nodes} proof nodes");
    nodes
}

fn bound_theorem(lo: &str, hi: &str) -> String {
    format!("theorem s {{v : Nat}} (h : v < {lo}) : v < {hi} := by\n  omega\n")
}

/// The canary every large-gap test runs first.
fn assert_gap_independent_on_small_gaps() -> usize {
    let small = proof_size("s", &bound_theorem("10", "1000"));
    let double = proof_size("s", &bound_theorem("10", "2000"));
    assert_eq!(
        small, double,
        "the omega proof grew with the literal gap (990 → {small} nodes, 1990 → {double}): \
         the unary weakening is back"
    );
    assert!(
        small <= MAX_PROOF_NODES,
        "the omega proof for gap 990 has {small} nodes (bound {MAX_PROOF_NODES})"
    );
    small
}

#[test]
fn literal_gap_repros_elaborate_with_gap_independent_proofs() {
    let baseline = assert_gap_independent_on_small_gaps();
    for (lo, hi) in [
        ("10", "100000"),
        ("10", "1000000"),
        ("1114112", "4294967296"),
        ("1114112", "1114113"),
        ("4294967296", "4294967297"),
        ("0x110000", "2 ^ 32"),
    ] {
        let nodes = proof_size("s", &bound_theorem(lo, hi));
        assert!(
            nodes <= MAX_PROOF_NODES,
            "(h : v < {lo}) ⊢ v < {hi}: {nodes} proof nodes (bound {MAX_PROOF_NODES}, \
             gap-990 proof {baseline})"
        );
    }
}

/// The other reconstruction shapes that carried the same unary term, each
/// blowing a 4 GB cap within 3 s before the fix. `{}` is the literal that
/// sets the gap. Each family is size-compared at 1000 and 2000 (cheap with
/// the defect back) before it runs at 1000000.
#[test]
fn other_literal_gap_shapes_elaborate_with_gap_independent_proofs() {
    let families: [(&str, fn(&str) -> String); 6] = [
        // Symbolic upper bound weakened from a hypothesis.
        ("symbolic core", |k| {
            format!("theorem s {{v w : Nat}} (h : v ≤ w + 3) : v ≤ w + {k}3 := by\n  omega\n")
        }),
        // Goal-only literal comparison.
        ("literal goal", |k| {
            format!("theorem s : 5 ≤ {k} := by\n  omega\n")
        }),
        // Goal-only shared symbolic core.
        ("shared core goal", |k| {
            format!("theorem s {{n : Nat}} : n ≤ n + {k} := by\n  omega\n")
        }),
        // Offset hypothesis with a shifted goal LHS.
        ("shifted lhs", |k| {
            format!("theorem s {{v : Nat}} (h : v < 10) : v + 5 < {k} := by\n  omega\n")
        }),
        // Symbolic contradiction `n + k ≤ n`.
        ("symbolic contradiction", |k| {
            format!("theorem s {{n : Nat}} (h : n + {k} ≤ n) : False := by\n  omega\n")
        }),
        // `≠` past a bound: substitutes `v := 1k` into `h` and refutes the
        // false literal bound `1k < k` (the old refuter peeled `k` layers).
        ("ne past bound", |k| {
            format!("theorem s {{v : Nat}} (h : v < {k}) : v ≠ 1{k} := by\n  omega\n")
        }),
    ];
    for (family, source) in families {
        let small = proof_size("s", &source("1000"));
        let double = proof_size("s", &source("2000"));
        assert_eq!(
            small, double,
            "{family}: the omega proof grew with the literal ({small} → {double} nodes)"
        );
        let large = proof_size("s", &source("1000000"));
        assert_eq!(
            large, small,
            "{family}: the omega proof grew with the literal ({small} → {large} nodes)"
        );
    }
}

/// The closure gate in [`proof_size`] can fail: a theorem that rests on a
/// declared axiom reaches it, while one that rests on `propext` alone (or on
/// nothing) passes.
#[test]
fn closure_gate_admits_only_the_foundational_axioms() {
    let mut env = Environment::with_prelude();
    try_elaborate_into(
        &mut env,
        "axiom ax : (1 : Nat) = 1\n\n\
         theorem rests_on_ax : (1 : Nat) = 1 := ax\n\n\
         theorem rests_on_propext (a b : Prop) (h : a ↔ b) : a = b := propext h\n\n\
         theorem rests_on_nothing : (1 : Nat) = 1 := rfl\n",
    )
    .unwrap_or_else(|e| panic!("the closure-gate fixture must elaborate: {e}"));
    assert_eq!(
        non_foundational_axioms(&env, "rests_on_ax"),
        BTreeSet::from([Name::from_string("ax")]),
        "a theorem resting on a declared axiom must fail the closure gate"
    );
    let foundational: Option<BTreeSet<Name>> = env
        .foundational_axiom_deps(&Name::from_string("rests_on_propext"))
        .map(|deps| deps.into_iter().collect());
    assert_eq!(
        foundational,
        Some(BTreeSet::from([Name::from_string("propext")])),
        "`propext h` must reach the kernel's own `propext`"
    );
    for name in ["rests_on_propext", "rests_on_nothing"] {
        let domain = non_foundational_axioms(&env, name);
        assert!(
            domain.is_empty(),
            "`{name}` must pass the closure gate, reaches {domain:?}"
        );
    }
}

/// `validChar` and the four theorems about it, VERBATIM from
/// `~/trust-ir/lean/trust_ir-semantics/TrustIr/Basic.lean:417-450` (trust-ir
/// 2b829b76). `validChar_of_lt_256` and `not_validChar_above_max` CLEAR the
/// conjunct they do not need with the rcases pattern `-`;
/// `irrelevant_hypothesis_does_not_block_the_refutation` covers the `_`
/// spelling, which keeps it in scope.
const TRUST_IR_VALID_CHAR_THEOREMS: [(&str, &str); 4] = [
    (
        "validChar_of_lt_256",
        "theorem validChar_of_lt_256 {v : Nat} (h : v < 256) : validChar v := by\n  \
         refine ⟨by omega, ?_⟩\n  rintro ⟨hlo, -⟩\n  omega\n",
    ),
    (
        "not_validChar_surrogate",
        "theorem not_validChar_surrogate : ¬ validChar 0xD800 := by\n  \
         rintro ⟨-, hsur⟩\n  exact hsur ⟨by omega, by omega⟩\n",
    ),
    (
        "not_validChar_above_max",
        "theorem not_validChar_above_max : ¬ validChar 0x110000 := by\n  \
         rintro ⟨hlt, -⟩\n  omega\n",
    ),
    (
        "validChar_lt_two_pow_32",
        "theorem validChar_lt_two_pow_32 {v : Nat} (h : validChar v) : v < 2 ^ 32 := by\n  \
         have := h.1\n  omega\n",
    ),
];

/// The `TrustIr/Basic.lean` declarations that hit the defect, verbatim
/// ([`TRUST_IR_VALID_CHAR_THEOREMS`]). Before the fix
/// `validChar_lt_two_pow_32` never finished and `not_validChar_surrogate`'s
/// two `omega` goals (`0xD800 ≤ 0xD800`, `0xD800 ≤ 0xDFFF`) took 12 s and
/// 1.6 GB; `validChar_of_lt_256` and `not_validChar_above_max` were refused
/// (`strict_chain_contradictions_close`,
/// `strict_lone_hypothesis_contradictions_close`).
#[test]
fn trust_ir_valid_char_theorems_elaborate() {
    assert_gap_independent_on_small_gaps();
    for (name, body) in TRUST_IR_VALID_CHAR_THEOREMS {
        let nodes = proof_size(name, &format!("{VALID_CHAR}{body}"));
        assert!(
            nodes <= 2 * MAX_PROOF_NODES,
            "`{name}`: {nodes} proof nodes (bound {})",
            2 * MAX_PROOF_NODES
        );
    }
    // Negative controls, in the verbatim `-` spelling: `v = 0xD800` satisfies
    // `v < 0xD801` and is no `validChar`; `0x10FFFF` is the last valid code
    // point; `0xD7FF` is below the surrogate range.
    assert_refused(
        "validChar_of_lt_bad",
        &valid_char_of_lt("validChar_of_lt_bad", "0xD801", "-"),
    );
    assert_refused(
        "not_validChar_max",
        &not_valid_char_by_range("not_validChar_max", "0x10FFFF", "-"),
    );
    assert_refused(
        "not_validChar_below_surrogates",
        &format!(
            "{VALID_CHAR}theorem not_validChar_below_surrogates : ¬ validChar 0xD7FF := by\n  \
             rintro ⟨-, hsur⟩\n  exact hsur ⟨by omega, by omega⟩\n"
        ),
    );
}

/// Elaborate `source` (defining `name` last) and assert it is REFUSED: the
/// elaboration fails and no proof of `name` is registered.
fn assert_refused(name: &str, source: &str) {
    let mut env = Environment::with_prelude();
    let result = try_elaborate_into(&mut env, source);
    assert!(
        result.is_err(),
        "the FALSE `{name}` must be refused:\n{source}"
    );
    assert!(
        env.get_const(&Name::from_string(name))
            .and_then(|info| info.value.clone())
            .is_none(),
        "no proof of the FALSE `{name}` may be registered:\n{source}"
    );
}

/// Negative controls: the fix must not make a FALSE bound provable. `v =
/// 100000` satisfies `h` and violates each goal.
#[test]
fn false_literal_gap_twins_are_refused() {
    for (lo, hi) in [("100001", "100000"), ("4294967297", "4294967296")] {
        assert_refused("s", &bound_theorem(lo, hi));
    }
}

/// `validChar` exactly as `TrustIr/Basic.lean` states it.
const VALID_CHAR: &str =
    "def validChar (v : Nat) : Prop :=\n  v < 0x110000 ∧ ¬(0xD800 ≤ v ∧ v ≤ 0xDFFF)\n\n";

/// `TrustIr/Basic.lean`'s `validChar_of_lt_256` over the bound `h : v <
/// {bound}`, with `{second}` the rcases pattern for the conjunct `v ≤
/// 0xDFFF`. The source's `-` clears it; `_` keeps it in scope as an
/// irrelevant hypothesis.
fn valid_char_of_lt(name: &str, bound: &str, second: &str) -> String {
    format!(
        "{VALID_CHAR}theorem {name} {{v : Nat}} (h : v < {bound}) : validChar v := by\n  \
         refine ⟨by omega, ?_⟩\n  rintro ⟨hlo, {second}⟩\n  omega\n"
    )
}

/// `TrustIr/Basic.lean`'s `not_validChar_above_max` at the code point
/// `{point}`, with `{second}` the rcases pattern for the surrogate conjunct
/// (the source's `-` clears it, `_` keeps it).
fn not_valid_char_by_range(name: &str, point: &str, second: &str) -> String {
    format!(
        "{VALID_CHAR}theorem {name} : ¬ validChar {point} := by\n  \
         rintro ⟨hlt, {second}⟩\n  omega\n"
    )
}

/// A STRICT linarith chain is refuted as the `≤` it is by definition.
///
/// `validChar_of_lt_256`'s last `omega` refutes `hlo : 0xD800 ≤ v` against `h :
/// v < 256`. The row here spells the second conjunct `_`, so `v ≤ 0xDFFF`
/// stays in scope (the subject of
/// `irrelevant_hypothesis_does_not_block_the_refutation`); the source's `-`
/// clears it ([`TRUST_IR_VALID_CHAR_THEOREMS`]). linarith chains
/// them into a proof of `0xD800 < 256` and handed it to
/// the `≤` contradiction closer as if it proved `0xD800 ≤ 256`, so the
/// `False` term applied a `Nat.lt` proof where `Nat.le 0xD800 256` was due and
/// the kernel refused it (`expected 55296 ≤ 256, got 55296 < 256`). Lean
/// 4.8.0 defines `Nat.lt n m := Nat.le (succ n) m` (`Init/Prelude.lean:1643`),
/// so the same proof is closed at `Nat.succ 0xD800 ≤ 256`; the symbolic case
/// at `Nat.succ (n + 5) ≤ n + 3`.
#[test]
fn strict_chain_contradictions_close() {
    for (name, source) in [
        (
            "validChar_of_lt_256",
            valid_char_of_lt("validChar_of_lt_256", "256", "_"),
        ),
        (
            "s",
            "theorem s {v : Nat} (h : v < 256) (hlo : 0xD800 ≤ v) : False := by\n  omega\n".into(),
        ),
        (
            "s",
            "theorem s {n v : Nat} (h1 : n + 5 ≤ v) (h2 : v < n + 3) : False := by\n  omega\n"
                .into(),
        ),
    ] {
        let nodes = proof_size(name, &source);
        assert!(
            nodes <= 2 * MAX_PROOF_NODES,
            "`{name}`: {nodes} proof nodes (bound {})",
            2 * MAX_PROOF_NODES
        );
    }
    // Negative controls: `v = 0xD800` (resp. `v = n + 3`) satisfies each
    // hypothesis set.
    assert_refused(
        "validChar_of_lt_bad",
        &valid_char_of_lt("validChar_of_lt_bad", "0xD801", "_"),
    );
    assert_refused(
        "s",
        "theorem s {v : Nat} (hlo : 0xD800 ≤ v) (h : v < 0xD801) : False := by\n  omega\n",
    );
    assert_refused(
        "s",
        "theorem s {n v : Nat} (h1 : n + 3 ≤ v) (h2 : v < n + 4) : False := by\n  omega\n",
    );
}

/// A LONE strict hypothesis is refuted as the `≤` it is by definition.
///
/// `not_validChar_above_max` leaves `hlt : 0x110000 < 0x110000` (the row here
/// spells the surrogate conjunct `_`, keeping it in scope; the source's `-`
/// clears it, [`TRUST_IR_VALID_CHAR_THEOREMS`]). linarith's single-hypothesis closer read it as
/// `0x110000 ≤ 0x110000`, found nothing to refute, and returned `hlt` itself as
/// the proof of `False`. Read as `0x110000 + 1 ≤ 0x110000` it refutes, and so
/// do the symbolic `n < n` and `n + 5 < n + 3`.
#[test]
fn strict_lone_hypothesis_contradictions_close() {
    for (name, source) in [
        (
            "not_validChar_above_max",
            not_valid_char_by_range("not_validChar_above_max", "0x110000", "_"),
        ),
        (
            "s",
            "theorem s (h : (0x110000 : Nat) < 0x110000) : False := by\n  omega\n".into(),
        ),
        (
            "s",
            "theorem s {n : Nat} (h : n < n) : False := by\n  omega\n".into(),
        ),
        (
            "s",
            "theorem s {n : Nat} (h : n + 5 < n + 3) : False := by\n  omega\n".into(),
        ),
    ] {
        let nodes = proof_size(name, &source);
        assert!(
            nodes <= 2 * MAX_PROOF_NODES,
            "`{name}`: {nodes} proof nodes (bound {})",
            2 * MAX_PROOF_NODES
        );
    }
    // Negative controls: `0x10FFFF` is the last valid code point.
    assert_refused(
        "not_validChar_max",
        &not_valid_char_by_range("not_validChar_max", "0x10FFFF", "_"),
    );
    assert_refused(
        "s",
        "theorem s (h : (0x10FFFF : Nat) < 0x110000) : False := by\n  omega\n",
    );
    assert_refused(
        "s",
        "theorem s {n : Nat} (h : n + 3 < n + 5) : False := by\n  omega\n",
    );
}

/// An irrelevant hypothesis in scope does not block the refutation.
///
/// When mathverse's equality / `≤` solver refutes a system it flags EVERY
/// hypothesis, so `validChar_of_lt_256` spelled `rintro ⟨hlo, _⟩` (the
/// source's `-` clears `v ≤ 0xDFFF`) handed the proof builders `{h, hlo, v ≤
/// 0xDFFF}`: no chain, no contradictory sum. The replay now retries on a
/// smaller core, here `{h, hlo}`.
#[test]
fn irrelevant_hypothesis_does_not_block_the_refutation() {
    for source in [
        "theorem s {v : Nat} (h1 : v ≤ 3) (h2 : 5 ≤ v) (h3 : v ≤ 100) : False := by\n  omega\n",
        "theorem s {v : Nat} (h : v < 256) (hlo : 0xD800 ≤ v) (hhi : v ≤ 0xDFFF) : False := by\n  \
         omega\n",
    ] {
        let nodes = proof_size("s", source);
        assert!(
            nodes <= 2 * MAX_PROOF_NODES,
            "{nodes} proof nodes (bound {}):\n{source}",
            2 * MAX_PROOF_NODES
        );
    }
    // Negative controls: `v = 5` (resp. `v = 0xD800`) satisfies every hypothesis.
    assert_refused(
        "s",
        "theorem s {v : Nat} (h1 : v ≤ 5) (h2 : 5 ≤ v) (h3 : v ≤ 100) : False := by\n  omega\n",
    );
    assert_refused(
        "s",
        "theorem s {v : Nat} (h : v < 0xD801) (hlo : 0xD800 ≤ v) (hhi : v ≤ 0xDFFF) : False := \
         by\n  omega\n",
    );
}

/// `≥` and `>` hypotheses are read with their operands reversed, as Lean
/// 4.8.0 defines them (`GE.ge a b := LE.le b a`, `GT.gt a b := LT.lt b a`,
/// `Init/Prelude.lean:1115-1117`). In surface order `h : 3 ≥ 5` was the
/// consistent `3 ≤ 5` (`expected False, got Nat.le 5 3`) and `256 > v`,
/// `v ≥ 0xD800` did not chain (`expected 256 < v, got 256 > v`).
#[test]
fn ge_gt_hypotheses_are_read_reversed() {
    for source in [
        "theorem s (h : (3:Nat) ≥ 5) : False := by\n  omega\n",
        "theorem s (h : (5:Nat) > 5) : False := by\n  omega\n",
        "theorem s {v : Nat} (h : 256 > v) (hlo : v ≥ 0xD800) : False := by\n  omega\n",
        "theorem s {n : Nat} (h : n + 3 > n + 5) : False := by\n  omega\n",
    ] {
        let nodes = proof_size("s", source);
        assert!(
            nodes <= 2 * MAX_PROOF_NODES,
            "{nodes} proof nodes (bound {}):\n{source}",
            2 * MAX_PROOF_NODES
        );
    }
    // Negative controls: each hypothesis set is satisfiable (`v = 0xD800`,
    // any `n`).
    for source in [
        "theorem s (h : (5:Nat) ≥ 3) : False := by\n  omega\n",
        "theorem s {v : Nat} (h : 0xD801 > v) (hlo : v ≥ 0xD800) : False := by\n  omega\n",
        "theorem s {n : Nat} (h : n + 5 > n + 3) : False := by\n  omega\n",
    ] {
        assert_refused("s", source);
    }
}

/// A strict hypothesis enters a SUM as the `≤` it is by definition. `a + b <
/// 3`, `5 ≤ a` share no core to cancel and do not chain; summed as `Nat.succ
/// (a + b) + 5 ≤ 3 + a` they are refuted with `0 ≤ b`. The strict hypothesis
/// used to enter the sum as `a + b ≤ 3` (`expected Nat.le (a + b) 3, got a + b
/// < 3`).
///
/// The offset chain `a + k < b`, `b ≤ a` and the cycle `a < b`, `b < a` stay
/// under the file's absolute bound (135 nodes at every `k` here, and 49;
/// measured 2026-10-08). The cross-atom sum does not: its refutation goes
/// through the Farkas core's linear-equality proof, a permutation proof over
/// the sum's leaves, sorted by their printed form, so the literal VALUES move
/// the permutation. Measured in the same run: 4221 nodes at `k = 3`, 4333 at
/// `k = 3000`, `30000` and `3000000`. Its gate is growth: no size past twice
/// the `k = 3` size ([`CROSS_ATOM_SUM_NODES_AT_3`], itself held to twice its
/// measurement), checked in increasing `k`, so a gap-proportional term fails
/// at `k = 30000` (at least 30000 extra nodes) before `k = 3000000` is built.
#[test]
fn strict_sum_contradictions_close() {
    let cross_atom_sum = |k: u64| {
        format!(
            "theorem s {{a b : Nat}} (h1 : a + b < {k}) (h2 : {} ≤ a) : False := by\n  omega\n",
            k + 2
        )
    };
    let at_3 = proof_size("s", &cross_atom_sum(3));
    assert!(
        at_3 <= 2 * CROSS_ATOM_SUM_NODES_AT_3,
        "cross-atom sum at k = 3: {at_3} proof nodes (measured {CROSS_ATOM_SUM_NODES_AT_3})"
    );
    for k in [3000, 30_000, 3_000_000] {
        let nodes = proof_size("s", &cross_atom_sum(k));
        assert!(
            nodes <= 2 * at_3,
            "cross-atom sum: the omega proof grew with the literal ({at_3} nodes at k = 3, \
             {nodes} at k = {k})"
        );
    }
    let mut bounded: Vec<String> = [3, 3000, 3_000_000]
        .into_iter()
        .map(|k| {
            format!(
                "theorem s {{a b : Nat}} (h1 : a + {k} < b) (h2 : b ≤ a) : False := by\n  omega\n"
            )
        })
        .collect();
    bounded.push(
        "theorem s {a b : Nat} (h1 : a < b) (h2 : b < a) : False := by\n  omega\n".to_string(),
    );
    for source in &bounded {
        let nodes = proof_size("s", source);
        assert!(
            nodes <= 2 * MAX_PROOF_NODES,
            "{nodes} proof nodes (bound {}):\n{source}",
            2 * MAX_PROOF_NODES
        );
    }
    // Negative controls: `a = 5, b = 0` and `a = 0, b = 3` satisfy them.
    for source in [
        "theorem s {a b : Nat} (h1 : a + b < 6) (h2 : 5 ≤ a) : False := by\n  omega\n",
        "theorem s {a b : Nat} (h1 : a + 2 < b) (h2 : b ≤ a + 3) : False := by\n  omega\n",
    ] {
        assert_refused("s", source);
    }
}

/// The cross-atom sum's proof size at `k = 3`, measured 2026-10-08
/// ([`strict_sum_contradictions_close`]).
const CROSS_ATOM_SUM_NODES_AT_3: usize = 4221;

/// A strict Int hypothesis is `a + 1 ≤ b` by definition (Lean 4.8.0
/// `Init/Data/Int/Basic.lean:180`), refuted by the concrete Int closer. No
/// strict Int closer was wired, and the closer could not read the source
/// numeral `@OfNat.ofNat Int 5 _`.
#[test]
fn strict_int_contradictions_close() {
    for source in [
        "theorem s (h : (5:Int) < 3) : False := by\n  omega\n",
        "theorem s {v : Int} (h : v < 3) (h2 : 5 ≤ v) : False := by\n  omega\n",
    ] {
        let nodes = proof_size("s", source);
        assert!(
            nodes <= 2 * MAX_PROOF_NODES,
            "{nodes} proof nodes (bound {}):\n{source}",
            2 * MAX_PROOF_NODES
        );
    }
    // Negative controls: `2 < 3` is true; `v = 5` satisfies the pair.
    for source in [
        "theorem s (h : (2:Int) < 3) : False := by\n  omega\n",
        "theorem s {v : Int} (h : v < 6) (h2 : 5 ≤ v) : False := by\n  omega\n",
    ] {
        assert_refused("s", source);
    }
}

fn norm_num_theorem(lhs: &str, rel: &str, rhs: &str) -> String {
    format!("theorem s : ({lhs} : Nat) {rel} {rhs} := by\n  norm_num\n")
}

/// `norm_num` states a ground Nat comparison by one `Nat.ble` fold.
///
/// Its witness was `Nat.le.refl` lifted by one `Nat.le.step` per unit of the
/// gap, refused past 4096 steps (the goal then fell through to `decide`).
#[test]
fn norm_num_literal_comparisons_have_gap_independent_proofs() {
    let small = proof_size("s", &norm_num_theorem("5", "≤", "1000"));
    let double = proof_size("s", &norm_num_theorem("5", "≤", "2000"));
    assert_eq!(
        small, double,
        "the norm_num proof grew with the literal gap (995 → {small} nodes, 1995 → {double})"
    );
    for (lhs, rel, rhs) in [
        ("5", "≤", "1000000"),
        ("3", "<", "4294967296"),
        ("4294967296", "≥", "7"),
        ("4294967296", ">", "4294967295"),
    ] {
        let nodes = proof_size("s", &norm_num_theorem(lhs, rel, rhs));
        assert_eq!(
            nodes, small,
            "({lhs} : Nat) {rel} {rhs}: {nodes} proof nodes, gap-995 proof {small}"
        );
    }
    for (lhs, rel, rhs) in [
        ("1000001", "≤", "1000000"),
        ("4294967296", "<", "4294967296"),
        ("7", "≥", "4294967296"),
    ] {
        assert_refused("s", &norm_num_theorem(lhs, rel, rhs));
    }
}
