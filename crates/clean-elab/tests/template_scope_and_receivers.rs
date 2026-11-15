// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Name resolution follows Lean 4.8.0 where the round-25 verifier of
//! b0a40ede2 measured false theorems (2026-09-26), every one accepted by
//! 3f45fb7c6, e3f696689, c565a700a and b0a40ede2 unless noted:
//!
//! * A notation template's free names resolve where the template was
//!   DECLARED (Lean pre-resolves a quotation's identifiers there): after
//!   `section open A notation "KK" => k end open B`, `KK` is `A.k`.
//! * A notation's operands are substituted INTO its template, as Lean
//!   expands a notation, so an operand is elaborated under the template's
//!   binders and against the type the template gives it.
//! * A `where`/`let rec` auxiliary declaration is skipped for `B.f` when
//!   `B` ALONE is a global too, not only when `B.f` is.
//! * Under `open M` / `export M (Zed.x)`, `Zed.x` names `M.Zed.x`, even a
//!   `protected` one; an atomic name passes over a `protected` namespace
//!   member; a dotted name with a root declaration names that one.
//! * A local receiver whose type is still a metavariable is projected, never
//!   read as the namespace of a global `foo.x`; `(N.Foo).x` projects.
//! * A section variable spelled like a notation's global head (`Eq` of `=`)
//!   is not a use of that variable (accepted from e3f696689 on).
//! * A Lean core constant Clean models without declaring it (`xor` is
//!   `Bool.xor`, `cond` a fallback, `And.elim` a recognizer's) cannot be
//!   redeclared.
//!
//! Every `T` statement is accepted by Lean 4.8.0 and every `F` statement is
//! refused by it (both measured); each `F` is the value a build before this
//! change computed. The setup of every case is checked to elaborate on its
//! own, so each refusal is the statement's.
//!
//! The header-first batch (`clean_elab::module_batch`, the driver of Trust's
//! Clean islands) must give a template the same meaning. Its plan declares
//! each template before any declaration of the batch exists and before any
//! `open` is applied, and every use read the pre-resolution made there, so a
//! template naming a declaration of the batch named nothing: Trust 0.11.0,
//! with Clean ed11049a09f, reported `Unknown identifier: Satisfies` at every
//! use of `⊨` in astream-broker's islands (2026-10-18). The `⊨` statements
//! below were measured on Lean 4.8.0 like the others; their `F` is what a
//! template resolved at the use, against the root decoy, computes.

use clean_elab::module_batch::{
    elaborate_module as batch_elaborate, BatchOptions, SourceUnit, UnitId,
};
use clean_elab::{
    elaborate_decl_and_register_with_context, preprocess_decl_with_context, ElabResult, FileContext,
};
use clean_kernel::env::Environment;
use clean_kernel::Name;
use clean_parser::parse_file;

fn collect_failures(result: &ElabResult, out: &mut Vec<String>) {
    match result {
        ElabResult::Multiple(results) => {
            for r in results {
                collect_failures(r, out);
            }
        }
        ElabResult::Failed { name, error, .. } => out.push(format!("{name}: {error}")),
        _ => {}
    }
}

/// Parse, elaborate, kernel-check and register `source` with ONE file
/// context (the `clean check` driver contract).
fn elaborate_module(source: &str) -> Result<Environment, String> {
    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();
    let decls = parse_file(source).map_err(|e| format!("parse error: {e:?}"))?;
    for decl in &decls {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        let result = elaborate_decl_and_register_with_context(&mut env, &processed, &mut file_ctx)
            .map_err(|e| format!("elaborate/kernel-check error: {e}"))?;
        let mut failures = Vec::new();
        collect_failures(&result, &mut failures);
        if !failures.is_empty() {
            return Err(failures.join("\n"));
        }
    }
    Ok(env)
}

/// [`elaborate_module`] through the header-first batch, the whole source as
/// ONE unit.
fn elaborate_batch(source: &str) -> Result<Environment, String> {
    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();
    let decls = parse_file(source).map_err(|e| format!("parse error: {e:?}"))?;
    let units = [SourceUnit {
        id: UnitId(0),
        decls: &decls,
    }];
    let outcome = batch_elaborate(&mut env, &mut file_ctx, &units, BatchOptions::islands());
    if !outcome.is_clean() {
        return Err(format!("rejected: {}", outcome.render_rejections()));
    }
    if !outcome.committed {
        return Err("rejected: the batch was not committed".to_string());
    }
    Ok(env)
}

/// A checker of `(holds, decidable, statement)` cases over a setup.
type Check = fn(&str, &[(bool, bool, &str)]);

/// `(holds, decidable, statement)` over `setup`: a statement that holds is
/// proved axiom-free by `rfl`; one that does not is refused by `rfl` (and by
/// `decide` when decidable).
fn check(setup: &str, cases: &[(bool, bool, &str)]) {
    check_with(elaborate_module, setup, cases);
}

/// [`check`] through the header-first batch.
fn check_batch(setup: &str, cases: &[(bool, bool, &str)]) {
    check_with(elaborate_batch, setup, cases);
}

fn check_with(
    elaborate_module: fn(&str) -> Result<Environment, String>,
    setup: &str,
    cases: &[(bool, bool, &str)],
) {
    elaborate_module(setup).unwrap_or_else(|e| panic!("setup must elaborate: {e}\n{setup}"));
    for (id, (holds, decidable, statement)) in cases.iter().enumerate() {
        if *holds {
            let name = format!("case_true_{id}");
            let env = elaborate_module(&format!("{setup}\ntheorem {name} : {statement} := rfl\n"))
                .unwrap_or_else(|e| panic!("{statement} must hold: {e}"));
            let deps = env
                .axiom_deps(&Name::from_string(&name))
                .expect("registered theorem");
            assert!(deps.is_empty(), "{statement}: depends on axioms: {deps:?}");
            continue;
        }
        let proofs: &[&str] = if *decidable {
            &["rfl", "by decide"]
        } else {
            &["rfl"]
        };
        for proof in proofs {
            let name = format!("case_false_{id}");
            let error = match elaborate_module(&format!(
                "{setup}\ntheorem {name} : {statement} := {proof}\n"
            )) {
                Ok(_) => panic!("FALSE theorem accepted: {statement} := {proof}"),
                Err(error) => error,
            };
            assert!(
                !error.contains("parse error"),
                "negative must parse: {error}"
            );
        }
    }
}

#[test]
fn notation_free_names_resolve_where_the_notation_is_declared() {
    check_declaration_sites(check);
}

#[test]
fn notation_free_names_resolve_where_the_notation_is_declared_in_a_header_first_batch() {
    check_declaration_sites(check_batch);
}

/// The templates of [`notation_free_names_resolve_where_the_notation_is_declared`],
/// each checked by `check`.
fn check_declaration_sites(check: Check) {
    let ab = "namespace A\ndef k : Nat := 1\nend A\nnamespace B\ndef k : Nat := 2\nend B\n";
    // Declared in a section that opens `A`, used under `open B`.
    check(
        &format!("{ab}section\nopen A\nnotation \"KK\" => k\nend\nopen B\n"),
        &[(true, true, "KK = 1"), (false, true, "KK = 2")],
    );
    // Declared under `open A in`.
    check(
        &format!("{ab}open A in\nnotation \"KO\" => k\nopen B\n"),
        &[(true, true, "KO = 1"), (false, true, "KO = 2")],
    );
    // Declared at the root, where the root `k` is meant.
    check(
        "def k : Nat := 1\nnamespace B\ndef k : Nat := 2\nend B\nnotation \"KR\" => k\nopen B\n",
        &[(true, true, "KR = 1"), (false, true, "KR = 2")],
    );
    // Declared inside `namespace A`, used from `namespace B`.
    check(
        &format!("{ab}namespace A\nnotation \"KN\" => k\nend A\nopen B\n"),
        &[(true, true, "KN = 1"), (false, true, "KN = 2")],
    );
    // An operand-taking notation and an `infixl` declared under `open A`.
    check(
        &format!(
            "{ab}section\nopen A\nnotation \"K1 \" x => k + x\ninfixl:65 \" +k+ \" => fun x y => k * 100 + x + y\nend\nopen B\n"
        ),
        &[
            (true, true, "(K1 5) = 6"),
            (false, true, "(K1 5) = 7"),
            (true, true, "(3 +k+ 4) = 107"),
            (false, true, "(3 +k+ 4) = 207"),
        ],
    );
}

/// A template naming a declaration of its own namespace, written as
/// astream's TLA+ islands write it (`notation:50 M " ⊨ " F:50 => Satisfies M
/// F` in astream-broker, `infix:50 " ⊨ " => Satisfies` in astream-engine). The
/// root `Satisfies` is a decoy, read by a template resolved at the use.
#[test]
fn a_template_names_a_declaration_of_its_namespace_in_either_driver() {
    let notation = "def Satisfies (m f : Nat) : Nat := 0\n\
         namespace Skin\n\
         def Satisfies (m f : Nat) : Nat := m * 10 + f\n\
         notation:50 M \" ⊨ \" F:50 => Satisfies M F\n\
         theorem in_namespace : (2 ⊨ 3) = 23 := rfl\n\
         end Skin\n";
    let infix = "def Satisfies (m f : Nat) : Nat := 0\n\
         namespace Durable\n\
         def Satisfies (m f : Nat) : Nat := m * 100 + f\n\
         infix:50 \" ⊨ \" => Satisfies\n\
         theorem in_namespace : (2 ⊨ 3) = 203 := rfl\n\
         end Durable\n";
    let checks: [Check; 2] = [check, check_batch];
    for check in checks {
        check(
            notation,
            &[(true, true, "(2 ⊨ 3) = 23"), (false, true, "(2 ⊨ 3) = 0")],
        );
        check(
            infix,
            &[(true, true, "(2 ⊨ 3) = 203"), (false, true, "(2 ⊨ 3) = 0")],
        );
    }
}

/// A template one header-first batch declares means the same in a later batch
/// on the same environment and file context: the context the first batch
/// left held the pre-resolution its plan made, which named nothing (the
/// source measured with Lean 4.8.0 as one file).
#[test]
fn a_template_keeps_its_meaning_in_a_later_header_first_batch() {
    let source = "namespace Skin\n\
         def Satisfies (m f : Nat) : Nat := m * 10 + f\n\
         notation:50 M \" ⊨ \" F:50 => Satisfies M F\n\
         end Skin\n\
         theorem later : (2 ⊨ 3) = 23 := rfl\n";
    let decls = parse_file(source).expect("fixture parses");
    assert_eq!(decls.len(), 2, "the namespace block, then the theorem");
    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();
    for (id, decls) in [(0, &decls[..1]), (1, &decls[1..])] {
        let units = [SourceUnit {
            id: UnitId(id),
            decls,
        }];
        let outcome = batch_elaborate(&mut env, &mut file_ctx, &units, BatchOptions::islands());
        assert!(
            outcome.is_clean() && outcome.committed,
            "batch {id} rejected: {}",
            outcome.render_rejections()
        );
    }
    let deps = env
        .axiom_deps(&Name::from_string("later"))
        .expect("registered theorem");
    assert!(deps.is_empty(), "depends on axioms: {deps:?}");
}

#[test]
fn notation_operands_are_elaborated_inside_the_template() {
    check(
        "notation \"DD \" x => (x : Int) - 10\ndef d1 : Int := DD (3 - 5)\n",
        &[(true, true, "d1 = -12"), (false, true, "d1 = -10")],
    );
    check(
        "notation \"LI \" x => (fun (inst : Inhabited Nat) => x) ⟨7⟩\n\
         def t1 : Nat := LI (default : Nat)\n\
         def t3 : Nat := LI (inferInstance : Inhabited Nat).default\n",
        &[
            (true, true, "t1 = 7"),
            (false, true, "t1 = 0"),
            (true, true, "t3 = 7"),
            (false, true, "t3 = 0"),
        ],
    );
    // Hygiene is kept: the template's own binder never captures an operand.
    check(
        "def y : Nat := 100\nnotation \"NN \" x => let y := 1; x + y\n\
         notation \"NF \" x => (fun y => x + y) 1\ndef u2 (y : Nat) : Nat := NN y\n",
        &[
            (true, true, "(NN y) = 101"),
            (false, true, "(NN y) = 2"),
            (true, true, "(NF y) = 101"),
            (false, true, "(NF y) = 2"),
            (true, true, "u2 5 = 6"),
            (false, true, "u2 5 = 2"),
        ],
    );
}

#[test]
fn auxiliary_declaration_is_skipped_when_its_base_is_a_global() {
    check(
        "structure S where\n  x : Nat\ndef Foo : S := ⟨5⟩\n\
         def q1 : Nat := Foo.x\nwhere Foo : S := ⟨9⟩\n\
         def q2 : Nat :=\n  let rec Foo : S := ⟨9⟩\n  Foo.x\n\
         def q4 : Nat := (Foo).x\nwhere Foo : S := ⟨9⟩\n\
         namespace N\ndef Bar : S := ⟨6⟩\ndef q6 : Nat := Bar.x\nwhere Bar : S := ⟨9⟩\nend N\n",
        &[
            (true, true, "q1 = 5"),
            (false, true, "q1 = 9"),
            (true, true, "q2 = 5"),
            (false, true, "q2 = 9"),
            (true, true, "q4 = 9"),
            (true, true, "N.q6 = 6"),
            (false, true, "N.q6 = 9"),
        ],
    );
    check(
        "def w1 (a : Nat) : Nat := true.toNat + a\nwhere true : Bool := false\n\
         def w4 (a : Nat) : Nat :=\n  let rec true : Bool := false\n  true.toNat + a\n",
        &[
            (true, true, "w1 0 = 1"),
            (false, true, "w1 0 = 0"),
            (true, true, "w4 0 = 1"),
            (false, true, "w4 0 = 0"),
        ],
    );
}

#[test]
fn dotted_names_reached_through_open_and_export() {
    let setup = "structure S where\n  x : Nat\ndef Zed : S := ⟨5⟩\nnamespace M\ndef Zed.x : Nat := 4\nend M\n";
    check(
        &format!("{setup}open M\n"),
        &[(true, true, "Zed.x = 4"), (false, true, "Zed.x = 5")],
    );
    check(
        &format!("{setup}export M (Zed.x)\n"),
        &[(true, true, "Zed.x = 4"), (false, true, "Zed.x = 5")],
    );
    // `protected` hides only an ATOMIC spelling: the dotted `Zed.x` still
    // reaches a protected `M.Zed.x` under `open M` ...
    check(
        "structure S where\n  x : Nat\ndef Zed : S := ⟨20⟩\n\
         namespace M\nprotected def Zed.x : Nat := 40\nend M\nopen M\n",
        &[(true, true, "Zed.x = 40"), (false, true, "Zed.x = 20")],
    );
    // ... while inside `namespace P` an atomic `w` passes over a protected
    // `P.w` to the root one.
    check(
        "def w : Nat := 5\nnamespace P\nprotected def w : Nat := 1\ndef t : Nat := w\n\
         protected def Q.v : Nat := 7\ndef t2 : Nat := Q.v\nend P\n",
        &[
            (true, true, "P.t = 5"),
            (false, true, "P.t = 1"),
            (true, true, "P.t2 = 7"),
        ],
    );
    // A dotted spelling with a root declaration names that one alone (Lean's
    // `resolveExact`), not an opened `M.Function.comp` of the same spelling.
    check(
        "namespace M\ndef Function.comp : (Nat → Nat) → (Nat → Nat) → Nat → Nat := \
         fun _ _ x => x + 7\nend M\nopen M\n\
         def fc (a : Nat) : Nat := Function.comp (· + 1) (· * 2) a\n",
        &[(true, true, "fc 3 = 7"), (false, true, "fc 3 = 10")],
    );
}

#[test]
fn a_local_receiver_is_projected_whatever_its_type_state() {
    check(
        "structure S where\n  x : Nat\ndef foo.x : Nat := 9\n\
         def k1 : S → Nat := fun foo => foo.x\n\
         def k4 : S → Nat := fun foo => (foo).x\n\
         def k5 : S → Nat\n  | foo => foo.x\n\
         def k6 : S → Nat := fun (foo : _) => foo.x\n\
         def c6 : List Nat := ([⟨5⟩] : List S).map (fun foo => foo.x)\n",
        &[
            (true, true, "k1 ⟨5⟩ = 5"),
            (false, true, "k1 ⟨5⟩ = 9"),
            (false, false, "∀ s : S, k1 s = 9"),
            (true, true, "k4 ⟨5⟩ = 5"),
            (false, true, "k4 ⟨5⟩ = 9"),
            (true, true, "k5 ⟨5⟩ = 5"),
            (false, true, "k5 ⟨5⟩ = 9"),
            (true, true, "k6 ⟨5⟩ = 5"),
            (false, true, "k6 ⟨5⟩ = 9"),
            (true, true, "c6 = [5]"),
            (false, true, "c6 = [9]"),
        ],
    );
    check(
        "structure S where\n  x : Nat\nnamespace N\ndef Foo : S := ⟨5⟩\ndef Foo.x : Nat := 11\nend N\n",
        &[
            (true, true, "(N.Foo).x = 5"),
            (false, true, "(N.Foo).x = 11"),
            (true, true, "N.Foo.x = 11"),
        ],
    );
}

#[test]
fn a_notation_head_is_no_use_of_a_section_variable_of_its_spelling() {
    check(
        "section S\nvariable (Eq : Nat → Nat → Prop)\n\
         def sg (a b : Nat) : Nat := (if a = b then 1 else 0) + a\nend S\n",
        &[(true, true, "sg 1 1 = 2"), (true, true, "sg 1 2 = 1")],
    );
    // `sg` takes the two `Nat`s only.
    assert!(elaborate_module(
        "section S\nvariable (Eq : Nat → Nat → Prop)\n\
         def sg (a b : Nat) : Nat := (if a = b then 1 else 0) + a\nend S\n\
         theorem sg_extra : sg (fun _ _ => True) 1 1 = 2 := rfl\n"
    )
    .is_err());
}

#[test]
fn a_lean_core_constant_cannot_be_redeclared() {
    for (decl, statement) in [
        (
            "def xor : Bool → Bool → Bool := fun _ _ => true",
            "xor false false = true",
        ),
        ("def cond : Nat := 3", "cond = 3"),
        ("def not : Nat := 3", "not = 3"),
        (
            "def And.elim : Nat → Nat := fun n => n + 7",
            "And.elim 1 = 8",
        ),
    ] {
        let error = match elaborate_module(&format!("{decl}\n")) {
            Ok(_) => panic!("Lean 4.8.0 refuses `{decl}` (already declared)"),
            Err(error) => error,
        };
        assert!(error.contains("already been declared"), "{decl}: {error}");
        assert!(
            elaborate_module(&format!("{decl}\ntheorem t : {statement} := rfl\n")).is_err(),
            "FALSE theorem accepted: {statement}"
        );
    }
    // Lean core's own meaning stays available.
    check(
        "",
        &[
            (true, true, "xor false false = false"),
            (false, true, "xor false false = true"),
        ],
    );
    // Not a core constant in Lean 4.8.0: a user declaration stays legal.
    elaborate_module("def getElem! : Nat := 3\ndef compare : Nat := 3\n")
        .expect("Lean 4.8.0 accepts these declarations");
}
