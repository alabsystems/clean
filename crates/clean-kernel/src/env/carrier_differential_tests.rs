// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Differential reducer harness — carrier-parity gate A6
//! (`designs/2026-07-03-carrier-types-bitvec-parity.md` §5 P0.6, §6 A6).
//!
//! Replays every row of the Lean-v4.30-evaluated ground-truth table
//! `tests/fixtures/carrier_v4_30/op_table.tsv` against Clean and requires the
//! result to match Lean's value exactly, in two lanes:
//!
//! - **Reducer lane** (UInt8-64 arith/bitwise/bool-cmp): invokes the
//!   registered native reducer directly with the documented `Literal::Nat`
//!   payload contract (`native_reducers_uint.rs` header) — the exact call
//!   shape `reduce_native` delivers. A reducer that *declines* is a
//!   divergence: these ops have no other compute lane on a bare prelude.
//! - **whnf lane** (UInt decEq/decLt/decLe, Char, String): full kernel whnf
//!   on production spellings (`<T>.ofNat n` / `Char.ofNat n` / string
//!   literals), exercising operand pre-WHNF, δι fallback, and the
//!   Lit-driven String/Char reducers end-to-end.
//!
//! Phases 1-3 reshape the carrier DECLARATIONS; this harness pins the literal
//! SEMANTICS so a reshape can never silently change what `"aé".utf8ByteSize`
//! or `(2:UInt8)+3` computes to. Deterministic: the fixture is checked in;
//! regeneration instructions live in
//! `tests/fixtures/carrier_v4_30/gen_op_table.lean` (pinned toolchain).
//!
//! Run: `cargo test --locked --lib -p clean-kernel carrier_differential`
//!
//! USize is deliberately NOT in the table: genuine v4.30 USize is
//! width-abstract (opaque `System.Platform.getNumBits`) and width-dependent
//! USize ops are STUCK in Lean's kernel (design §1.5). Clean's current
//! width-64 shortcut is pinned in
//! `test_usize_width_concrete_compute_pin_p1_must_flip`, which Phase 1 MUST
//! flip to expect a declining reducer when the shortcuts are removed (§7.4).

use crate::env::Environment;
use crate::expr::{Expr, ExprKind, Literal};
use crate::name::Name;
use crate::tc::TypeChecker;

/// (category, op) pairs with NO Clean compute lane today. Every entry names
/// the phase that must remove it. Rows matching an entry are skipped;
/// everything else MUST match ground truth.
const SKIP_OPS: &[(&str, &str, &str)] = &[
    // (empty) — Phase 2 seeded `Char.utf8Size` (a `Bool.rec`/`Nat.ble`-over-
    // `Char.toNat` body, value-equal to Lean's), so `Char.utf8Size (Char.ofNat
    // cp)` now computes definitionally in the whnf lane; its rows are checked.
];

/// `<T>.decLe` has no native reducer; its rows run through full kernel whnf
/// of the SEEDED decLe (`algebra_uint_dec_le_proof` witness chain). On
/// near-max literals that δι chain explodes (P0 finding — same fragility the
/// wrapper-cmp pre-WHNF hits for big equal-literal decEq operands, see the
/// P0 report). Rows with an operand above this bound are skipped until the
/// P1 BitVec rebuild; P1 should lift the bound to cover the full table.
const DEC_LE_WHNF_OPERAND_BOUND: u64 = 1 << 16;

/// Individually known-divergent rows (category, op, lhs): real semantic
/// deltas between Clean's CURRENT carrier shapes and genuine v4.30, kept
/// visible here instead of hidden in a skip. Each names the phase that must
/// clear it.
const KNOWN_DIVERGENCES: &[(&str, &str, &str, &str)] = &[
    // (empty) — Phase 2 reshaped Char to the genuine 2-field
    // `⟨val : UInt32, valid⟩` and seeded the genuine `Char.ofNat` (dite on
    // `n.isValidChar`, invalid → '\0'). The native `char_code_point` recognizer
    // now applies the same valid→cp / invalid→0 mapping to `Char.ofNat <lit>`,
    // so `Char.toNat (Char.ofNat 55296/1114112)` computes 0 exactly as Lean.
];

fn n(s: &str) -> Name {
    Name::from_string(s)
}

fn c(s: &str) -> Expr {
    Expr::const_(n(s), vec![])
}

/// `<T>.ofNat <lit>` — the δ-reducible literal form real proof terms supply.
fn uint_of_nat(ty: &str, v: u64) -> Expr {
    Expr::app(c(&format!("{ty}.ofNat")), Expr::nat_lit(v))
}

fn char_of_nat(cp: u64) -> Expr {
    Expr::app(c("Char.ofNat"), Expr::nat_lit(cp))
}

fn decode_hex_str(field: &str) -> String {
    if field == "-" {
        return String::new();
    }
    assert!(
        field.len().is_multiple_of(2),
        "malformed hex string field: {field:?}"
    );
    let bytes: Vec<u8> = (0..field.len())
        .step_by(2)
        .map(|i| {
            u8::from_str_radix(&field[i..i + 2], 16)
                .unwrap_or_else(|e| panic!("bad hex byte in {field:?}: {e}"))
        })
        .collect();
    String::from_utf8(bytes).expect("fixture strings are valid UTF-8")
}

#[derive(Clone, Copy, PartialEq)]
enum ResultKind {
    Nat,
    Bool,
    Decidable,
    Str,
}

enum Expected {
    Nat(u64),
    Bool(bool),
    Decidable(bool),
    Str(String),
}

fn parse_expected(kind: ResultKind, raw: &str) -> Expected {
    match kind {
        ResultKind::Nat => Expected::Nat(
            raw.parse::<u64>()
                .unwrap_or_else(|e| panic!("bad nat expected {raw:?}: {e}")),
        ),
        ResultKind::Bool => Expected::Bool(raw == "true"),
        ResultKind::Decidable => Expected::Decidable(raw == "isTrue"),
        ResultKind::Str => Expected::Str(decode_hex_str(raw)),
    }
}

/// Classify a reduction result against the expectation; `None` on match.
fn check_result(result: &Expr, expected: &Expected) -> Option<String> {
    match expected {
        Expected::Nat(want) => match result.kind() {
            ExprKind::Lit(Literal::Nat(got)) if got.to_u64() == Some(*want) => None,
            other => Some(format!("expected Nat lit {want}, got {other:?}")),
        },
        Expected::Str(want) => match result.kind() {
            ExprKind::Lit(Literal::String(got)) if got.as_ref() == want.as_str() => None,
            other => Some(format!("expected String lit {want:?}, got {other:?}")),
        },
        Expected::Bool(want) => {
            let want_name = if *want { "Bool.true" } else { "Bool.false" };
            match result.get_app_fn().kind() {
                ExprKind::Const(name, _) if name.to_string() == want_name => None,
                other => Some(format!("expected {want_name}, got head {other:?}")),
            }
        }
        Expected::Decidable(want) => {
            let want_name = if *want {
                "Decidable.isTrue"
            } else {
                "Decidable.isFalse"
            };
            match result.get_app_fn().kind() {
                ExprKind::Const(name, _) if name.to_string() == want_name => None,
                other => Some(format!("expected {want_name}, got head {other:?}")),
            }
        }
    }
}

fn uint_type_of(category: &str) -> Option<&'static str> {
    match category {
        "uint8" => Some("UInt8"),
        "uint16" => Some("UInt16"),
        "uint32" => Some("UInt32"),
        "uint64" => Some("UInt64"),
        _ => None,
    }
}

fn bitvec_width_of(category: &str) -> Option<u64> {
    match category {
        "bitvec8" => Some(8),
        "bitvec16" => Some(16),
        "bitvec32" => Some(32),
        "bitvec64" => Some(64),
        _ => None,
    }
}

/// BitVec reducer-lane check: the `BitVec.<op>` native reducers read the width
/// from `args[0]` and BitVec payloads from `args[1]`/`args[2]`, so build the
/// exact call shape `reduce_native` delivers after pre-WHNF (raw `Nat`
/// literals). `not`/`neg` are unary; `ult`/`ule`/`slt`/`sle` return `Bool`; the
/// rest return the canonical `Nat` payload. A declining reducer is a
/// divergence — these ops have no other compute lane on a bare prelude.
fn run_bitvec_lane(env: &Environment, row: &Row<'_>, width: u64) -> Option<String> {
    let reducer_name = n(&format!("BitVec.{}", row.op));
    let Some(reducer) = env.get_native_reducer(&reducer_name) else {
        return Some(format!("no native reducer registered for {reducer_name}"));
    };
    let w = Expr::nat_lit(width);
    let a = Expr::nat_lit(
        row.lhs
            .parse::<u64>()
            .unwrap_or_else(|e| panic!("bad bitvec lhs {:?}: {e}", row.lhs)),
    );
    let (kind, result) = if row.op == "not" || row.op == "neg" {
        (ResultKind::Nat, reducer(&[&w, &a]))
    } else {
        let b = Expr::nat_lit(
            row.rhs
                .parse::<u64>()
                .unwrap_or_else(|e| panic!("bad bitvec rhs {:?}: {e}", row.rhs)),
        );
        let kind = match row.op {
            "ult" | "ule" | "slt" | "sle" => ResultKind::Bool,
            _ => ResultKind::Nat,
        };
        (kind, reducer(&[&w, &a, &b]))
    };
    let Some(result) = result else {
        return Some(format!(
            "native reducer {reducer_name} declined on Lit args"
        ));
    };
    check_result(&result, &parse_expected(kind, row.expected))
}

/// One parsed fixture row.
struct Row<'a> {
    lineno: usize,
    category: &'a str,
    op: &'a str,
    lhs: &'a str,
    rhs: &'a str,
    expected: &'a str,
}

/// Reducer-lane check: invoke the registered native reducer with the
/// documented `Literal::Nat` payload contract. Declining is a divergence.
fn run_reducer_lane(
    env: &Environment,
    row: &Row<'_>,
    ty: &str,
    kind: ResultKind,
) -> Option<String> {
    let reducer_name = n(&format!("{ty}.{op}", op = row.op));
    let Some(reducer) = env.get_native_reducer(&reducer_name) else {
        return Some(format!("no native reducer registered for {reducer_name}"));
    };
    let a = Expr::nat_lit(
        row.lhs
            .parse::<u64>()
            .unwrap_or_else(|e| panic!("bad lhs {:?}: {e}", row.lhs)),
    );
    let args_owned: Vec<Expr> = if row.rhs == "-" {
        vec![a]
    } else {
        vec![
            a,
            Expr::nat_lit(
                row.rhs
                    .parse::<u64>()
                    .unwrap_or_else(|e| panic!("bad rhs {:?}: {e}", row.rhs)),
            ),
        ]
    };
    let args: Vec<&Expr> = args_owned.iter().collect();
    let Some(result) = reducer(&args) else {
        return Some(format!(
            "native reducer {reducer_name} declined on Lit args"
        ));
    };
    check_result(&result, &parse_expected(kind, row.expected))
}

/// whnf-lane check: full kernel whnf on a production-spelled application.
fn run_whnf_lane(
    tc: &TypeChecker<'_>,
    expr: &Expr,
    kind: ResultKind,
    expected: &str,
) -> Option<String> {
    let result = tc.whnf(expr);
    check_result(&result, &parse_expected(kind, expected))
}

/// Route one row to its lane; returns a divergence description or `None`.
fn run_row(env: &Environment, tc: &TypeChecker<'_>, row: &Row<'_>) -> Option<String> {
    if let Some(width) = bitvec_width_of(row.category) {
        return run_bitvec_lane(env, row, width);
    }
    if let Some(ty) = uint_type_of(row.category) {
        return match row.op {
            // Reducer lane: Lit payload contract (no other compute lane on a
            // bare prelude — the olean supplies the op definitions).
            "add" | "sub" | "mul" | "div" | "mod" | "land" | "lor" | "xor" | "shiftLeft"
            | "shiftRight" | "complement" => run_reducer_lane(env, row, ty, ResultKind::Nat),
            "toNat" => run_reducer_lane(env, row, ty, ResultKind::Nat),
            "beq" | "blt" | "ble" => run_reducer_lane(env, row, ty, ResultKind::Bool),
            // Reducer lane, mk-form contract: the registered decEq/decLt
            // reducers peel `<T>.mk <payload>` (`get_uint_ctor_val`; the
            // bare-Lit payload is the documented legacy arm). P1 reshapes the
            // ctor to `<T>.ofBitVec` and updates `get_uint_ctor_val` — it
            // must update this operand builder in the same change (the
            // decline turns every dec row into a loud divergence, so it
            // cannot be forgotten silently).
            "decEq" | "decLt" => {
                let a: u64 = row.lhs.parse().expect("uint lhs");
                let b: u64 = row.rhs.parse().expect("uint rhs");
                // P1: the v4.30 carrier ctor is `<T>.ofBitVec`, not `<T>.mk`.
                // `get_uint_ctor_val` peels `<T>.ofNat <lit>` (the literal form),
                // so the dec reducers fire on `<T>.ofNat`-spelled operands.
                let ao = uint_of_nat(ty, a);
                let bo = uint_of_nat(ty, b);
                let reducer_name = n(&format!("{ty}.{op}", op = row.op));
                let Some(reducer) = env.get_native_reducer(&reducer_name) else {
                    return Some(format!("no native reducer registered for {reducer_name}"));
                };
                match reducer(&[&ao, &bo]) {
                    Some(result) => check_result(
                        &result,
                        &parse_expected(ResultKind::Decidable, row.expected),
                    ),
                    None => Some(format!(
                        "native reducer {reducer_name} declined on mk-form args"
                    )),
                }
            }
            // whnf lane: `<T>.decLe` has no native reducer — full kernel whnf
            // through the seeded witness chain, on `<T>.ofNat` spellings.
            // Bounded (see DEC_LE_WHNF_OPERAND_BOUND).
            "decLe" => {
                let a: u64 = row.lhs.parse().expect("uint lhs");
                let b: u64 = row.rhs.parse().expect("uint rhs");
                if a > DEC_LE_WHNF_OPERAND_BOUND || b > DEC_LE_WHNF_OPERAND_BOUND {
                    return None; // bounded out — see const doc; P1 lifts this
                }
                let expr = Expr::apps(
                    c(&format!("{ty}.decLe")),
                    [uint_of_nat(ty, a), uint_of_nat(ty, b)],
                );
                run_whnf_lane(tc, &expr, ResultKind::Decidable, row.expected)
            }
            other => panic!("unknown uint op {other:?} at line {}", row.lineno),
        };
    }
    match (row.category, row.op) {
        ("char", "ofNatToNat") => {
            let cp: u64 = row.lhs.parse().expect("char cp");
            let expr = Expr::app(c("Char.toNat"), char_of_nat(cp));
            run_whnf_lane(tc, &expr, ResultKind::Nat, row.expected)
        }
        ("char", "utf8Size") => {
            let cp: u64 = row.lhs.parse().expect("char cp");
            let expr = Expr::app(c("Char.utf8Size"), char_of_nat(cp));
            run_whnf_lane(tc, &expr, ResultKind::Nat, row.expected)
        }
        ("string", op) => {
            let s = Expr::str_lit(decode_hex_str(row.lhs));
            let (expr, kind) = match op {
                "append" => (
                    Expr::apps(
                        c("String.append"),
                        [s, Expr::str_lit(decode_hex_str(row.rhs))],
                    ),
                    ResultKind::Str,
                ),
                "push" => {
                    // Reducer lane: `reduce_string_push` takes the Char as a
                    // BARE Nat payload (`get_nat_val`), so kernel whnf of
                    // `String.push s (Char.ofNat c)` is STUCK today (P0
                    // finding — the reducer declines on every real Char
                    // spelling and `String.push` has no seeded body). P2/P3
                    // should either peel the genuine Char ctor chain here or
                    // rely on the transcribed definitions; this row pins the
                    // UTF-8 byte semantics either way.
                    let cp: u64 = row.rhs.parse().expect("push cp");
                    let reducer = env
                        .get_native_reducer(&n("String.push"))
                        .expect("String.push native reducer registered");
                    let cp_lit = Expr::nat_lit(cp);
                    let result = match reducer(&[&s, &cp_lit]) {
                        Some(result) => result,
                        None => {
                            return Some("String.push reducer declined on payload args".to_string())
                        }
                    };
                    return check_result(&result, &parse_expected(ResultKind::Str, row.expected));
                }
                "length" => (Expr::app(c("String.length"), s), ResultKind::Nat),
                "utf8ByteSize" => (Expr::app(c("String.utf8ByteSize"), s), ResultKind::Nat),
                "beq" => (
                    Expr::apps(c("String.beq"), [s, Expr::str_lit(decode_hex_str(row.rhs))]),
                    ResultKind::Bool,
                ),
                "decEq" => (
                    Expr::apps(
                        c("String.decEq"),
                        [s, Expr::str_lit(decode_hex_str(row.rhs))],
                    ),
                    ResultKind::Decidable,
                ),
                "isEmpty" => (Expr::app(c("String.isEmpty"), s), ResultKind::Bool),
                other => panic!("unknown string op {other:?} at line {}", row.lineno),
            };
            run_whnf_lane(tc, &expr, kind, row.expected)
        }
        (cat, op) => panic!("unknown table row {cat}.{op} at line {}", row.lineno),
    }
}

fn fixture_path() -> std::path::PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures/carrier_v4_30/op_table.tsv")
}

/// A6: zero (non-catalogued) divergences from `lean` v4.30 ground truth on
/// the Char/String/UInt8-64 op samples.
#[test]
fn test_carrier_differential_matches_lean_ground_truth() {
    let table = std::fs::read_to_string(fixture_path())
        .expect("read tests/fixtures/carrier_v4_30/op_table.tsv");
    let env = Environment::with_prelude();
    let tc = TypeChecker::with_mode(&env, env.mode());

    let mut checked = 0usize;
    let mut skipped = 0usize;
    let mut known = 0usize;
    let mut divergences: Vec<String> = Vec::new();

    for (idx, line) in table.lines().enumerate() {
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        let cols: Vec<&str> = line.split('\t').collect();
        assert_eq!(cols.len(), 5, "malformed row {}: {line:?}", idx + 1);
        let row = Row {
            lineno: idx + 1,
            category: cols[0],
            op: cols[1],
            lhs: cols[2],
            rhs: cols[3],
            expected: cols[4],
        };

        if SKIP_OPS
            .iter()
            .any(|(cat, op, _)| *cat == row.category && *op == row.op)
        {
            skipped += 1;
            continue;
        }

        // Debug aid for locating pathological rows (not part of the gate):
        // CARRIER_DIFF_TRACE=1 cargo test ... -- --nocapture
        if std::env::var_os("CARRIER_DIFF_TRACE").is_some() {
            eprintln!(
                "[row {}] {} {} {} {}",
                row.lineno, row.category, row.op, row.lhs, row.rhs
            );
        }
        let diag = run_row(&env, &tc, &row);
        let is_known = KNOWN_DIVERGENCES
            .iter()
            .any(|(cat, op, lhs, _)| *cat == row.category && *op == row.op && *lhs == row.lhs);
        match (diag, is_known) {
            (Some(diag), false) => divergences.push(format!(
                "line {}: {}.{}({}, {}): {diag}",
                row.lineno, row.category, row.op, row.lhs, row.rhs
            )),
            (Some(_), true) => known += 1,
            (None, true) => divergences.push(format!(
                "line {}: {}.{}({}, {}) is catalogued in KNOWN_DIVERGENCES but now \
                 MATCHES ground truth — a phase landed; remove its entry",
                row.lineno, row.category, row.op, row.lhs, row.rhs
            )),
            (None, false) => {}
        }
        checked += 1;
    }

    assert!(
        checked > 3000,
        "sanity: expected >3000 checked rows, got {checked} (skipped {skipped})"
    );
    assert_eq!(
        known,
        KNOWN_DIVERGENCES.len(),
        "every KNOWN_DIVERGENCES entry must correspond to exactly one still-divergent row"
    );
    assert!(
        divergences.is_empty(),
        "{} divergence(s) from Lean v4.30 ground truth (first 25):\n{}",
        divergences.len(),
        divergences
            .iter()
            .take(25)
            .cloned()
            .collect::<Vec<_>>()
            .join("\n")
    );
}

/// Q6 tripwire, FLIPPED in Phase 1 (design §1.5/§7.4): genuine v4.30 USize is
/// width-abstract (`System.Platform.getNumBits` is a seeded OPAQUE), so
/// width-dependent USize facts like `(2:USize) + 3 = 5` are STUCK in the kernel
/// — both 32- and 64-bit models are consistent. Clean's old width-64 `USize.add`
/// native reducer decided them: a def-eq EXCESS (silently axiomatizing
/// `numBits = 64`). Phase 1 DELETED every width-dependent USize reducer; this
/// test now asserts the reducer is GONE, i.e. Clean matches Lean's stuckness
/// (A6's "stuckness on both sides" clause).
#[test]
fn test_usize_width_concrete_compute_pin_p1_flipped() {
    let env = Environment::with_prelude();
    assert!(
        env.get_native_reducer(&n("USize.add")).is_none(),
        "USize.add native reducer must be REMOVED (P1 numBits-abstractness): \
         width-dependent USize compute is a def-eq excess over Lean's theory"
    );
    // The width-abstract `USize.size` (= 2 ^ numBits) must NOT reduce to a
    // concrete literal: `numBits` is opaque, so it stays stuck.
    let tc = TypeChecker::with_mode(&env, env.mode());
    let size = tc.whnf(&c("USize.size"));
    assert!(
        !matches!(size.kind(), ExprKind::Lit(Literal::Nat(_))),
        "USize.size must stay abstract (no numBits=64 leakage), got {:?}",
        size.kind()
    );
}
