// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The generalized-split recursion audit refuses the shape that computed the
//! measured wrong answer and leaves the faithful recursions alone.

use std::path::PathBuf;

use crate::native_build::emit_entry_c_with_type;

fn emit(source: &str) -> anyhow::Result<String> {
    let dir = tempfile::tempdir().expect("tempdir");
    let file: PathBuf = dir.path().join("rec_split_fixture.lean");
    std::fs::write(&file, source).expect("write fixture");
    emit_entry_c_with_type(&file, "main", 0).map(|(c, _)| c)
}

/// The value the elaborator produced for `recFirst` until 0ffcbd885, written
/// out: `fun p n => P2.casesOn p (fun x y => Nat.rec (fun _ => x)
/// (fun _ ih _ => ih ⟨y, x⟩) n p)` -- the split of `p` sits OUTSIDE the
/// recursor, so every level reads the original `x`, `y` and the value handed
/// to the recursive call is dropped (`recFirst ⟨3, 4⟩ 1` printed 3; Lean 4).
///
/// The elaborator no longer emits this shape (the decreasing column is lowered
/// outermost, and `check_recursive_minors_closed` refuses a minor that reads an
/// outer split), so no source program reaches it any more and the audit is
/// tested on the value itself. It stays as the native path's second line.
#[test]
fn test_rec_split_audit_generalized_split_argument_is_refused() {
    use clean_kernel::{BinderInfo, Expr, Level, Name};
    let mut env = clean_kernel::Environment::with_prelude();
    let mut ctx = clean_elab::FileContext::new();
    for decl in
        clean_parser::parse_file("structure P2 where\n  a : Nat\n  b : Nat\n").expect("parse P2")
    {
        let processed = clean_elab::preprocess_decl_with_context(&decl, &mut ctx);
        clean_elab::elaborate_decl_and_register(&mut env, &processed).expect("register P2");
    }
    let c = |n: &str| Expr::const_(Name::from_string(n), Vec::<Level>::new());
    let one = Level::succ(Level::zero());
    let (nat, p2) = (c("Nat"), c("P2"));
    let lam = |ty: &Expr, body: Expr| Expr::lam(BinderInfo::Default, ty.clone(), body);
    // Binder levels: p 0, n 1, x 2, y 3 (inside the minor, depth 4).
    let zero_minor = lam(&p2, Expr::bvar(2)); // fun _ => x          (depth 5)
    let succ_minor = lam(
        &nat,
        lam(
            &Expr::arrow(p2.clone(), nat.clone()),
            lam(
                &p2,
                // ih ⟨y, x⟩ at depth 7: ih 5 -> 1, y 3 -> 3, x 2 -> 4
                Expr::app(
                    Expr::bvar(1),
                    Expr::apps(c("P2.mk"), [Expr::bvar(3), Expr::bvar(4)]),
                ),
            ),
        ),
    );
    let recursion = Expr::apps(
        Expr::const_(Name::from_string("Nat.rec"), vec![one.clone()]),
        [
            lam(&nat, Expr::arrow(p2.clone(), nat.clone())),
            zero_minor,
            succ_minor,
            Expr::bvar(2), // n
            Expr::bvar(3), // p: the generalized argument, over-applied
        ],
    );
    let split = Expr::apps(
        Expr::const_(Name::from_string("P2.casesOn"), vec![one]),
        [
            lam(&p2, nat.clone()),
            Expr::bvar(1), // p, at depth 2
            lam(&nat, lam(&nat, recursion)),
        ],
    );
    let value = lam(&p2, lam(&nat, split));
    let err = super::check_recursion_split(&env, &Name::from_string("recFirst"), &value)
        .expect_err("the generalized-split recursion must be refused");
    let msg = err.to_string();
    assert!(msg.contains("native-recursion-split"), "{msg}");
    assert!(msg.contains("`recFirst`"), "{msg}");
}

/// `recFirst` itself now elaborates with the split inside the recursion, so
/// the native path compiles it (its printed values are pinned byte-for-byte
/// against Lean by the native battery's `q14_recfirst`).
#[test]
fn test_rec_split_audit_recfirst_as_elaborated_now_compiles() {
    emit(
        "structure P2 where\n  a : Nat\n  b : Nat\n\
         def recFirst : P2 → Nat → Nat\n  \
         | ⟨x, _⟩, 0 => x\n  \
         | ⟨x, y⟩, n + 1 => recFirst ⟨y, x⟩ n\n\
         def main : IO Unit := IO.println (toString (recFirst ⟨3, 4⟩ 1))\n",
    )
    .expect("recFirst's elaborated value splits inside the recursion and compiles");
}

/// The audit itself stays live: the shape the elaborator used to produce,
/// written out by hand with `P2.casesOn` and `Nat.rec`, is still refused
/// through the production emit path. For this HAND-WRITTEN term the refusal is
/// stricter than Lean (pinned Lean runs it and prints `3`, which is that
/// term's own value), so it is recorded as an over-refusal, never a wrong
/// answer; this arm fails loudly the day the audit is narrowed or retired.
#[test]
fn test_rec_split_audit_hand_written_source_split_outside_the_recursor_is_refused() {
    let err = emit(
        "structure P2 where\n  a : Nat\n  b : Nat\n\
         def recFirstH (p : P2) (n : Nat) : Nat :=\n  \
         P2.casesOn (motive := fun _ => Nat) p (fun x y =>\n    \
         Nat.rec (motive := fun _ => P2 → Nat) (fun _ => x) (fun _ ih _ => ih ⟨y, x⟩) n p)\n\
         def main : IO Unit := IO.println (toString (recFirstH ⟨3, 4⟩ 1))\n",
    )
    .expect_err("the split-outside-the-recursor shape must still be refused, not compiled");
    let msg = format!("{err:#}");
    assert!(msg.contains("native-recursion-split"), "{msg}");
    assert!(msg.contains("`recFirstH`"), "{msg}");
}

/// Accumulator recursions whose changing arguments are NOT split before the
/// recursor compile (and were measured byte-identical to Lean: `3`, `4`, `6`).
#[test]
fn test_rec_split_audit_unsplit_changing_arguments_compile() {
    emit(
        "def len : List Nat → Nat → Nat\n  \
         | [], acc => acc\n  \
         | _ :: xs, acc => len xs (acc + 1)\n\
         def swapAcc : Nat → Nat → Nat → Nat\n  \
         | a, _, 0 => a\n  \
         | a, b, n + 1 => swapAcc b a n\n\
         def main : IO Unit := do\n  \
         IO.println (toString (len [1, 2, 3] 0))\n  \
         IO.println (toString (swapAcc 3 4 1))\n",
    )
    .expect("recursions that split nothing outside the recursor are faithful");
}
