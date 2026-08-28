// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! MEASUREMENT PROBE — not a fix, not a regression pin. Prints the verbatim
//! refusal for a missing instance so the diagnostic defect can be quoted.

use clean_elab::{
    elaborate_decl_and_register, preprocess_decl_with_context, ElabResult, FileContext,
};
use clean_kernel::env::Environment;
use clean_kernel::{Expr, TypeChecker};
use clean_parser::parse_file;

fn elaborate_file(source: &str) -> Result<Vec<(String, Expr)>, String> {
    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();
    let decls = parse_file(source).map_err(|e| format!("parse error: {e:?}"))?;
    let mut values = Vec::new();
    for decl in &decls {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        let result =
            elaborate_decl_and_register(&mut env, &processed).map_err(|e| e.to_string())?;
        if let ElabResult::Definition { name, ty, val, .. } = &result {
            let tc = TypeChecker::new(&env);
            tc.check_type(val, ty)
                .map_err(|e| format!("kernel rejected {name}: {e}"))?;
            values.push((name.to_string(), val.clone()));
        }
    }
    Ok(values)
}

fn outcome(source: &str) -> String {
    match elaborate_file(source) {
        Ok(v) => format!("OK  {:?}", v.last().map(|(n, _)| n.clone())),
        Err(e) => format!("ERR {e}"),
    }
}

#[test]
fn probe_uint_binops() {
    let mut lines = Vec::new();
    for carrier in ["UInt64", "UInt32", "UInt8", "Nat", "Int"] {
        for op in ["+", "-", "*", "%", "/", "&&&", "|||", "^^^"] {
            let src = format!("def v (a b : {carrier}) : {carrier} := a {op} b");
            lines.push(format!("{carrier:>7} {op:>4} : {}", outcome(&src)));
        }
    }
    println!("\n=== two-variable binop matrix ===\n{}", lines.join("\n"));
}

#[test]
fn probe_missing_user_instance() {
    let mut lines = Vec::new();

    // (1) A user class with NO instance at all, used at a rigid known type.
    lines.push(format!(
        "user class, rigid arg   : {}",
        outcome(
            "class Fooable (a : Type) where\n  foo : a -> a\n\ndef useit (n : Nat) : Nat := Fooable.foo n\n"
        )
    ));

    // (2) A user class with NO instance, argument type left open (a numeral).
    lines.push(format!(
        "user class, numeral arg : {}",
        outcome(
            "class Fooable (a : Type) where\n  foo : a -> a\n\ndef useit : Nat := Fooable.foo 3\n"
        )
    ));

    // (3) A user class WITH an instance — control.
    lines.push(format!(
        "user class, has instance: {}",
        outcome(
            "class Fooable (a : Type) where\n  foo : a -> a\n\ninstance : Fooable Nat where\n  foo n := n\n\ndef useit (n : Nat) : Nat := Fooable.foo n\n"
        )
    ));

    // (4) Missing instance on a PRELUDE class at a user type.
    lines.push(format!(
        "prelude class, user type: {}",
        outcome(
            "structure Widget where\n  w : Nat\n\ndef useit (x y : Widget) : Widget := x + y\n"
        )
    ));

    println!(
        "\n=== missing-instance comparison ===\n{}",
        lines.join("\n")
    );
}

/// Discriminator for the B104 `homogeneous` gate (`infer/elab_app.rs:3219`).
///
/// `%` `/` `&&&` are `homogeneous: true` in `hetero_binop_homogenize_slots`
/// (elab_app.rs:1011-1013) so a ground unsatisfiable goal RETRIES with slot
/// pinning suppressed, and the retry's goal is no longer ground.
/// `^` `<<<` `>>>` are `homogeneous: false` (elab_app.rs:1023) so they never
/// take the retry — if they refuse LOUDLY at a carrier with no instance, the
/// retry is the discriminator, not the binop path as such.
#[test]
fn probe_homogeneous_gate_discriminator() {
    let mut lines = Vec::new();
    for (label, src) in [
        (
            "UInt64 &&& (homog)",
            "def v (a b : UInt64) : UInt64 := a &&& b",
        ),
        (
            "UInt64 <<< (non-h)",
            "def v (a b : UInt64) : UInt64 := a <<< b",
        ),
        (
            "UInt64 ^   (non-h)",
            "def v (a b : UInt64) : UInt64 := a ^ b",
        ),
        ("Int    &&& (homog)", "def v (a b : Int) : Int := a &&& b"),
        ("Int    <<< (non-h)", "def v (a b : Int) : Int := a <<< b"),
        ("UInt64 % no ascript", "def v (a b : UInt64) := a % b"),
        (
            "UInt64 % Nat (hetero)",
            "def v (a : UInt64) (b : Nat) : UInt64 := a % b",
        ),
    ] {
        lines.push(format!("{label:>22} : {}", outcome(src)));
    }
    println!(
        "\n=== homogeneous-gate discriminator ===\n{}",
        lines.join("\n")
    );
}

#[test]
fn probe_uint_mod_verbatim() {
    let src = "def v (a b : UInt64) : UInt64 := a % b";
    println!("\n=== VERBATIM ===\n{src}\n-->\n{}\n", outcome(src));
}
