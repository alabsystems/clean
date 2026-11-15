// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The pre-landing review of integ/r6 (24f74254b, findings X1-X11): every
//! negative control below is refused by BOTH pinned Leans (4.8.0 and
//! 4.30.0-rc2, exit 1; measured 2026-10-23 with `bin/lean` of each release,
//! the first error line quoted per test) and was accepted by Clean at
//! 24f74254b (its release binary, built at dd098b6e7, which differs only in
//! `.olean` import code). Every positive control is accepted by both Leans.
//! The front door's exit codes for the same files are pinned in
//! `crates/clean/tests/lean_front_door_review_r6.rs`.
//!
//! Known gaps the fixes leave in the SAFE direction (Clean refuses what Lean
//! accepts) are pinned as refusals that say so, so they fail loudly the day
//! they close.

use crate::lean_compile_checks::FrontDoorScope;
use crate::module_driver::{DeclVerdict, ModuleReport, VerdictKind};
use crate::tests_do_lane_r5_lift::{assert_passed, assert_refused_with, check_module, verdict};

/// [`check_module`] as `clean lean` runs it: with the front door's refusals
/// (`crate::lean_compile_checks`) on.
fn check_front_door(source: &str) -> ModuleReport {
    let _front_door = FrontDoorScope::enter(true);
    check_module(source)
}

/// Some verdict (a command's, which has no declaration name) is refused with
/// every one of `needles` in its detail.
fn assert_some_refused_with(report: &ModuleReport, needles: &[&str]) {
    let found = report.verdicts.iter().any(|v: &DeclVerdict| {
        v.kind != VerdictKind::Passed
            && needles
                .iter()
                .all(|needle| v.detail.as_deref().unwrap_or_default().contains(needle))
    });
    assert!(
        found,
        "a verdict must be refused with {needles:?}: {report:#?}"
    );
}

fn assert_all_passed(report: &ModuleReport) {
    for v in &report.verdicts {
        assert_eq!(
            v.kind,
            VerdictKind::Passed,
            "`{}` must pass: {v:#?}",
            v.name
        );
    }
}

// ---------------------------------------------------------------------------
// X9: a body-less `opaque` needs an inhabited type (R134)
// ---------------------------------------------------------------------------

#[test]
fn test_opaque_of_uninhabited_type_is_refused_x9() {
    // Lean 4.8.0: "failed to synthesize Inhabited False"; 4.30.0-rc2: "failed
    // to synthesize 'Inhabited' or 'Nonempty' instance for False". At
    // 24f74254b Clean registered `o : False` as an axiom and proved `oops`.
    for (source, opaque) in [
        ("opaque o : False\ntheorem oops : False := o\n", "o"),
        ("opaque o : Empty\ntheorem oops : False := nomatch o\n", "o"),
        ("opaque o (n : Nat) : Fin n\n", "o"),
    ] {
        let report = check_module(source);
        assert_refused_with(&report, opaque, &["Inhabited or Nonempty"]);
        assert!(
            report
                .verdicts
                .iter()
                .filter(|v| v.name == "oops")
                .all(|v| v.kind != VerdictKind::Passed),
            "nothing may be proved from an uninhabited opaque: {report:#?}"
        );
    }
}

#[test]
fn test_opaque_of_inhabited_type_passes_x9() {
    // Both Leans accept each of these.
    for source in [
        "opaque o : Nat\ntheorem ok : True := True.intro\n",
        "opaque g : Nat → Nat\n",
        "opaque f (α : Type) [Inhabited α] : α\n",
        "structure S where\n  x : Nat\ninstance : Nonempty S := ⟨⟨0⟩⟩\nnoncomputable opaque s : S\n",
    ] {
        assert_all_passed(&check_module(source));
    }
}

#[test]
fn test_computable_opaque_of_nonempty_only_type_is_refused_x9() {
    // Both Leans: "failed to compile definition, consider marking it as
    // 'noncomputable' because it depends on 'Classical.ofNonempty'".
    let report = check_module(
        "structure S where\n  x : Nat\ninstance : Nonempty S := ⟨⟨0⟩⟩\nopaque s : S\n",
    );
    assert_refused_with(&report, "s", &["noncomputable", "Classical.ofNonempty"]);
}

#[test]
fn test_opaque_fin_succ_passes_x9() {
    // Both Leans accept through `Inhabited (Fin (no_index (n+1)))`, which
    // Clean's prelude lacks and both Leans' `Init` has (fix round).
    assert_all_passed(&check_module("opaque f (n : Nat) : Fin (n+1)\n"));
}

#[test]
fn test_partial_def_reads_its_binders_as_locals_x9() {
    // The shared guard opens the binders: `[Inhabited α]` serves `α` (both
    // Leans accept); `partial def bad : False` stays refused.
    assert_all_passed(&check_module(
        "partial def f (α : Type) [Inhabited α] (a : α) : α := f α a\n",
    ));
    let report = check_module("partial def bad : False := bad\n");
    assert_ne!(verdict(&report, "bad").kind, VerdictKind::Passed);
}

// ---------------------------------------------------------------------------
// X11 and X1: what `#eval` will not run, everywhere (R134)
// ---------------------------------------------------------------------------

#[test]
fn test_eval_of_sorry_dependent_term_is_refused_x11() {
    // 4.30.0-rc2: "Aborting evaluation since the expression depends on the
    // 'sorry' axiom"; 4.8.0: "cannot evaluate code because 'x' uses 'sorry'".
    for source in [
        "def x : Nat := sorry\n#eval x\n",
        "#eval (sorry : Nat)\n",
        "#eval (sorry : Nat) + 1\n",
    ] {
        assert_some_refused_with(&check_module(source), &["sorry"]);
    }
}

#[test]
fn test_eval_of_noncomputable_term_is_refused_x11_x1() {
    // Both versions refuse the dependency. Modern Lean reports runtime
    // axioms with backticks; 4.8 uses the older noncomputable wording.
    for (source, culprit) in [
        ("noncomputable def x : Nat := 1\n#eval x\n", "'x'"),
        (
            "#eval (Classical.ofNonempty : Nat)\n",
            "'Classical.ofNonempty'",
        ),
        (
            "#eval (Classical.choice ⟨(0:Nat)⟩ : Nat)\n",
            "Classical.choice",
        ),
    ] {
        assert_some_refused_with(&check_module(source), &["noncomputable", culprit]);
    }
}

#[test]
fn test_eval_of_function_is_refused_x11() {
    // 4.30.0-rc2: "could not synthesize a `Repr` or `ToString` instance";
    // 4.8.0: "could not synthesize a 'Lean.Eval' instance".
    assert_some_refused_with(&check_module("#eval fun (x : Nat) => x\n"), &["Repr"]);
}

#[test]
fn test_eval_of_closed_value_still_runs_x11() {
    // Both Leans print `2`.
    assert_all_passed(&check_module("#eval (1 : Nat) + 1\n"));
}

// ---------------------------------------------------------------------------
// X1: computable definitions with no code, at the front door (R134, R135)
// ---------------------------------------------------------------------------

#[test]
fn test_front_door_refuses_computable_def_without_code_x1() {
    for (source, name, culprit) in [
        (
            "def x : Nat := Classical.ofNonempty\n",
            "x",
            "'Classical.ofNonempty'",
        ),
        (
            "def y : Nat := Classical.choice ⟨0⟩\n",
            "y",
            "Classical.choice",
        ),
        (
            "inductive T | a : Nat → T deriving Nonempty\ndef z : T := Classical.ofNonempty\n",
            "z",
            "'Classical.ofNonempty'",
        ),
    ] {
        assert_refused_with(&check_front_door(source), name, &["noncomputable", culprit]);
    }
}

#[test]
fn test_front_door_admits_what_lean_does_not_compile_x1() {
    // Both Leans accept: a `noncomputable` definition, a derived `Nonempty`,
    // and a `Prop` / proof that mentions `Classical.choice`.
    for source in [
        "noncomputable def x : Nat := Classical.ofNonempty\n",
        "inductive T | a : Nat → T deriving Nonempty\n",
        "def p : Prop := ∃ n : Nat, n = Classical.choice ⟨0⟩\ntheorem t : (Classical.choice ⟨(0:Nat)⟩ : Nat) = Classical.choice ⟨0⟩ := rfl\n",
    ] {
        assert_all_passed(&check_front_door(source));
    }
}

#[test]
fn test_computability_is_checked_at_the_front_door_only_x1() {
    // `clean check` keeps its own contract (no code generator; R134 records
    // why the door alone refuses).
    assert_all_passed(&check_module("def x : Nat := Classical.ofNonempty\n"));
}

// ---------------------------------------------------------------------------
// X10: the safe context, at the front door (R135)
// ---------------------------------------------------------------------------

#[test]
fn test_front_door_refuses_safe_use_of_unsafe_constant_x10() {
    // Both Leans: "(kernel) invalid declaration, it uses unsafe declaration".
    for (source, name, culprit) in [
        (
            "unsafe def u : Nat := 1\ntheorem t : u = 1 := rfl\n",
            "t",
            "'u'",
        ),
        ("unsafe def u : Nat := 1\ndef s : Nat := u\n", "s", "'u'"),
        (
            "unsafe axiom ax : False\ntheorem f : False := ax\n",
            "f",
            "'ax'",
        ),
    ] {
        assert_refused_with(
            &check_front_door(source),
            name,
            &["unsafe declaration", culprit],
        );
    }
}

#[test]
fn test_front_door_admits_unsafe_and_partial_uses_lean_admits_x10() {
    // Both Leans accept: an unsafe body using an unsafe constant, and a safe
    // use of a `partial def` (its constant is an opaque, as in Lean).
    for source in [
        "unsafe def u : Nat := 1\nunsafe def s : Nat := u\n",
        "partial def p (n : Nat) : Nat := p n\ndef q : Nat := p 0\ntheorem r : q = q := rfl\n",
    ] {
        assert_all_passed(&check_front_door(source));
    }
}

#[test]
fn test_unsafe_theorem_is_refused_everywhere_x10() {
    // Both Leans: "'unsafe' theorems are not allowed".
    let report = check_module("unsafe theorem t : True := True.intro\n");
    assert_some_refused_with(&report, &["'unsafe' theorems are not allowed"]);
}

// ---------------------------------------------------------------------------
// X2: `(default : T)` resolves at `T`, not at its reduct
// ---------------------------------------------------------------------------

const DEFAULT_T: &str = "def T := Nat\ninstance : Inhabited T := ⟨(5 : Nat)⟩\n";

#[test]
fn test_default_at_a_def_type_uses_its_instance_x2() {
    // Both Leans refuse `= 0` (4.8.0 "type mismatch"; 4.30.0-rc2 "Not a
    // definitional equality") and accept `= 5`.
    let report = check_module(&format!(
        "{DEFAULT_T}theorem bad : (default : T) = (0 : Nat) := rfl\n\
         def z : T := Inhabited.default\ntheorem zv : z = (0 : Nat) := rfl\n\
         theorem good : (default : T) = (5 : Nat) := rfl\n"
    ));
    assert_ne!(
        verdict(&report, "bad").kind,
        VerdictKind::Passed,
        "{report:#?}"
    );
    assert_ne!(
        verdict(&report, "zv").kind,
        VerdictKind::Passed,
        "{report:#?}"
    );
    assert_passed(&report, "good");
}

#[test]
fn test_default_without_an_instance_at_the_def_type_is_refused_x2() {
    // Both Leans: "failed to synthesize instance Inhabited T".
    let report = check_module("def T := Nat\ndef x : T := default\n");
    assert_ne!(
        verdict(&report, "x").kind,
        VerdictKind::Passed,
        "{report:#?}"
    );
}

#[test]
fn test_class_method_at_a_def_type_uses_its_instance_x2() {
    // Both Leans accept; at 24f74254b Clean asked for `C Nat`.
    let report = check_module(
        "def T := Nat\nclass C (α : Type) where\n  c : α\ninstance : C T := ⟨(5 : Nat)⟩\n\
         def y : T := C.c\ntheorem yv : y = (5 : Nat) := rfl\n",
    );
    assert_passed(&report, "y");
    assert_passed(&report, "yv");
}

// ---------------------------------------------------------------------------
// X6: `deriving Inhabited` never silently takes a later constructor (R137)
// ---------------------------------------------------------------------------

#[test]
fn test_derive_inhabited_refuses_rather_than_skip_a_constructor_x6() {
    // Lean finds `Inhabited UInt8` / `Inhabited True` and takes `p`; both
    // Leans refuse `= W.q` (4.8.0 "type mismatch"). Clean lacks those
    // instances, and at 24f74254b silently took `q`.
    for (source, theorem) in [
        (
            "inductive W | p (x : UInt8) | q deriving Inhabited\ntheorem w : (default : W) = W.q := rfl\n",
            "w",
        ),
        (
            "inductive W | p (x : True) | q deriving Inhabited\ntheorem w : (default : W) = W.q := rfl\n",
            "w",
        ),
        (
            "inductive P (α : Type) | a (x : UInt8) | b (y : α) deriving Inhabited\ntheorem w : (default : P Nat) = P.b 0 := rfl\n",
            "w",
        ),
    ] {
        let report = check_module(source);
        assert_ne!(verdict(&report, theorem).kind, VerdictKind::Passed, "{report:#?}");
    }
}

#[test]
fn test_derive_inhabited_moves_on_where_lean_does_x6() {
    // Both Leans accept each `rfl`.
    for source in [
        "inductive T2 | node (l r : T2) | leaf deriving Inhabited\ntheorem w : (default : T2) = T2.leaf := rfl\n",
        "inductive W | p (s : String) | q deriving Inhabited\ntheorem w : (default : W) = W.p \"\" := rfl\n",
        "inductive P (α : Type) | a (y : α) | b deriving Inhabited\ntheorem w : (default : P Nat) = P.b := rfl\n",
        "inductive W | p (x : UInt8) | q deriving Nonempty\n",
    ] {
        assert_all_passed(&check_module(source));
    }
}

// ---------------------------------------------------------------------------
// X7: `@[match_pattern]` and `n + k` patterns are typed (R138)
// ---------------------------------------------------------------------------

#[test]
fn test_match_pattern_def_of_the_wrong_type_is_refused_x7() {
    // Both Leans: "type mismatch" (`pr b : Option Nat` at `Option Bool`).
    let report = check_module(
        "@[match_pattern] def pr (a : Nat) : Option Nat := some a\n\
         def h (o : Option Bool) : Bool := match o with\n  | pr b => b\n  | _ => false\n",
    );
    assert_refused_with(&report, "h", &["match_pattern"]);
}

#[test]
fn test_nat_match_pattern_at_int_is_refused_x7() {
    // Both Leans accept `g` (a coercion) and refuse `g 5 = 0`; Clean refuses
    // `g` (no coercion in a pattern; safe direction) instead of an arm that
    // never matches.
    let report = check_module(
        "@[match_pattern] def sNat (n : Nat) : Nat := n + 1\n\
         def g (i : Int) : Int := match i with\n  | sNat k => k\n  | _ => 0\n\
         theorem g5 : g 5 = 0 := rfl\n",
    );
    assert_ne!(
        verdict(&report, "g").kind,
        VerdictKind::Passed,
        "{report:#?}"
    );
    assert!(
        report
            .verdicts
            .iter()
            .filter(|v| v.name == "g5")
            .all(|v| v.kind != VerdictKind::Passed),
        "{report:#?}"
    );
}

#[test]
fn test_numeral_add_pattern_at_int_is_refused_x7() {
    // Both Leans: "`k` is an explicit pattern variable, but it only occurs in
    // positions that are inaccessible to pattern matching".
    let report =
        check_module("def g2 (i : Int) : Int := match i with\n  | k + 1 => k\n  | _ => 0\n");
    assert_refused_with(&report, "g2", &["inaccessible"]);
}

#[test]
fn test_well_typed_match_patterns_pass_x7() {
    // Both Leans accept.
    for source in [
        "@[match_pattern] def pr (a : Nat) : Option Nat := some a\n\
         def h (o : Option Nat) : Nat := match o with\n  | pr b => b\n  | _ => 0\n\
         theorem h1 : h (some 3) = 3 := rfl\n",
        "@[match_pattern] def sNat (n : Nat) : Nat := n + 1\n\
         def g (i : Nat) : Nat := match i with\n  | sNat k => k\n  | _ => 0\n\
         theorem g5 : g 5 = 4 := rfl\n",
    ] {
        assert_all_passed(&check_module(source));
    }
}

// ---------------------------------------------------------------------------
// X3: `cases` decides without a `have` local's value (R136)
// ---------------------------------------------------------------------------

const G_NAT: &str = "def g : Nat → Nat\n  | 0 => 1\n  | n+1 => n\n\n";

#[test]
fn test_cases_does_not_unfold_a_have_x3() {
    // Both Leans: "dependent elimination failed, failed to solve equation".
    let report = check_module(&format!(
        "theorem h4 (f : Nat → Nat) (a : Nat) (H : ∀ x, f x = f a) : True := by\n  have b : Nat := a\n  have h := H b\n  cases h\n  trivial\n\n\
         {G_NAT}theorem h5 (H : ∀ x, g x = 0) : False := by\n  have b : Nat := 0\n  have h := H b\n  cases h\n"
    ));
    assert_refused_with(&report, "h4", &["dependent elimination failed"]);
    assert_ne!(
        verdict(&report, "h5").kind,
        VerdictKind::Passed,
        "{report:#?}"
    );
}

#[test]
fn test_cases_without_a_value_still_solves_x3() {
    // Both Leans accept `p1`; both refuse `c4` (no value to unfold).
    let report = check_module(
        "theorem p1 (f : Nat → Nat) (a : Nat) (H : ∀ x, f x = f a) : True := by\n  have h := H a\n  cases h\n  trivial\n\n\
         theorem c4 (f : Nat → Nat) (a b : Nat) (H : ∀ x, f x = f a) : True := by\n  have h := H b\n  cases h\n  trivial\n",
    );
    assert_passed(&report, "p1");
    assert_ne!(
        verdict(&report, "c4").kind,
        VerdictKind::Passed,
        "{report:#?}"
    );
}

#[test]
fn test_cases_through_a_let_unfolds_its_value_x3() {
    // Both Leans accept `l4` and `l5`: a `let` local's value IS unfolded by
    // `cases`, where a `have` local's is not (`h4`, `h5` above). Only the
    // `have`-marked values are dropped (R136, over R127's mark).
    let report = check_module(&format!(
        "theorem l4 (f : Nat → Nat) (a : Nat) (H : ∀ x, f x = f a) : True := by\n  let b : Nat := a\n  have h := H b\n  cases h\n  trivial\n\n\
         {G_NAT}theorem l5 (H : ∀ x, g x = 0) : False := by\n  let b : Nat := 0\n  have h := H b\n  cases h\n"
    ));
    assert_passed(&report, "l4");
    assert_passed(&report, "l5");
}

// ---------------------------------------------------------------------------
// X4: an auxiliary declaration that names a consumed local goes with it
// ---------------------------------------------------------------------------

#[test]
fn test_aux_decl_naming_an_eliminated_local_is_out_of_scope_x4() {
    // Both Leans: "unknown identifier 'helper'" (t1, t2, t4) and "clear
    // failed, variable 'helper' depends on 'h'" (t5).
    for (source, name) in [
        ("theorem w4 (n : Nat) (h : n = 0) : (fun _ : Nat => True) 0 := by subst h; exact helper\nwhere helper : (fun _ : Nat => True) n := True.intro\n", "w4"),
        ("theorem w5 (n m : Nat) (h : n = m) : (fun _ : Nat => True) n := by cases h; exact helper\nwhere helper : (fun _ : Nat => True) m := True.intro\n", "w5"),
        ("theorem w7 (n : Nat) : True := by\n  cases n\n  · exact helper\n  · exact helper\nwhere\n  helper : (fun _ : Nat => True) n := True.intro\n", "w7"),
        ("theorem w8 (n : Nat) (h : n = 0) : True := by\n  clear h\n  exact helper\nwhere\n  helper : (fun _ : n = 0 => True) h := True.intro\n", "w8"),
    ] {
        let report = check_module(source);
        assert_ne!(verdict(&report, name).kind, VerdictKind::Passed, "{report:#?}");
    }
}

#[test]
fn test_aux_decl_not_naming_an_eliminated_local_stays_x4() {
    // Both Leans accept.
    for source in [
        "theorem w3 (n : Nat) (h : n = 0) : (fun _ : Nat => True) 0 := by subst h; exact helper\nwhere helper : (fun _ : Nat => True) 1 := True.intro\n",
        "theorem w9 (n : Nat) (h : n = 0) : (fun _ : Nat => True) 0 := by\n  subst h\n  exact helper\nwhere\n  helper : True := True.intro\n",
        "theorem w3 (n m : Nat) (h : n = m) (p : n = 0) : m = 0 := by\n  cases h\n  exact helper\nwhere\n  helper : n = 0 := p\n",
    ] {
        assert_all_passed(&check_module(source));
    }
}

// ---------------------------------------------------------------------------
// X5: `subst` / `cases` see dependence through a local's type
// ---------------------------------------------------------------------------

#[test]
fn test_subst_refuses_a_replacement_naming_a_dependent_x5() {
    // Both Leans refuse each: "failed to create binder due to failure when
    // reverting variable dependencies" (o1, p2, p6), "dependent elimination
    // failed" (o2, o4), "'x' occurs at" (o3), "did not find equation for
    // eliminating 'n'" (v6).
    for (source, name) in [
        ("theorem o1 (x : Nat) (y : Fin (x+1)) (f : Fin (x+1) → Nat) (h : x = f y) : True := by\n  subst h\n  exact True.intro\n", "o1"),
        ("theorem o2 (x : Nat) (y : Fin (x+1)) (f : Fin (x+1) → Nat) (h : f y = x) : True := by\n  cases h\n  exact True.intro\n", "o2"),
        ("theorem o3 (x : Nat) (y : Fin (x+1)) (h : x = y.val) : True := by\n  subst h\n  exact True.intro\n", "o3"),
        ("theorem o4 (x : Nat) (y : Fin (x+1)) (h : y.val = x) : True := by\n  cases h\n  exact True.intro\n", "o4"),
        ("theorem v6 (n : Nat) (y : Fin (n+1)) (h : n = y.val) : True := by\n  subst n\n  exact True.intro\n", "v6"),
        ("theorem p2 (n : Nat) (y : Fin (n+1)) (f : Fin (n+1) → Nat) (h1 : n = f y) (h2 : n = 3) : True := by\n  subst n\n  exact True.intro\n", "p2"),
        ("theorem p6 (x : Nat) (y : Fin (x+1)) (f : Fin (x+1) → Nat) (h : f y = x) : True := by\n  subst h\n  exact True.intro\n", "p6"),
    ] {
        let report = check_module(source);
        assert_ne!(verdict(&report, name).kind, VerdictKind::Passed, "{report:#?}");
    }
}

#[test]
fn test_subst_still_eliminates_where_lean_does_x5() {
    // Both Leans accept: `p3` skips `h1` (its `@Fin.val (n+1) y` names `n`)
    // and uses `h2`; `p5` and `v5` substitute a variable no dependent blocks.
    for source in [
        "theorem p3 (n : Nat) (y : Fin (n+1)) (h1 : n = y.val) (h2 : n = 3) : True := by\n  subst n\n  exact True.intro\n",
        "theorem p5 (x z : Nat) (y : Fin (x+1)) (h : x = z) : True := by\n  subst h\n  exact True.intro\n",
        "theorem v5 (x y : Nat) (h : x = y) : True := by\n  subst h\n  exact True.intro\n",
    ] {
        assert_all_passed(&check_module(source));
    }
}

// ---------------------------------------------------------------------------
// X8: a `return` in a statement-position `match` falls through (KNOWN GAP)
// ---------------------------------------------------------------------------

#[test]
fn test_do_return_inside_statement_match_falls_through_known_gap_x8() {
    // KNOWN GAP, WRONG OUTPUT (ledger class (169)): in Lean `r4 0 = .ok ()`
    // (both Leans prove it by `rfl` and refuse `.error "after"`). Clean lowers
    // the arm's `return ()` to `pure ()` and runs the rest of the block. This
    // pin asserts today's WRONG verdicts so it fails the day the gap closes;
    // flip both assertions then.
    let report = check_module(
        "def r4 (a : Nat) : Except String Unit := do\n  match a with\n  | 0 => return ()\n  | _ => pure ()\n  throw \"after\"\n\n\
         theorem wrong : r4 0 = .error \"after\" := rfl\n\
         theorem right : r4 0 = .ok () := rfl\n",
    );
    assert_passed(&report, "wrong");
    assert_ne!(
        verdict(&report, "right").kind,
        VerdictKind::Passed,
        "{report:#?}"
    );
}

// ---------------------------------------------------------------------------
// The fix round's false refusals, each accepted by both pinned Leans
// (measured 2026-10-24, `bin/lean` of 4.8.0 and 4.30.0-rc2), and the
// refusals beside them that both Leans make too.
// ---------------------------------------------------------------------------

#[test]
fn test_front_door_noncomputable_section_marks_instead_of_refusing() {
    // Lean marks what its compiler cannot compile inside a `noncomputable
    // section`; a later computable use of it is refused, as both Leans refuse.
    for source in [
        "noncomputable section\ndef pick : Nat := Classical.choice ⟨0⟩\nend\n",
        "noncomputable section Foo\ndef pick : Nat := Classical.choice ⟨0⟩\nend Foo\n",
        "noncomputable section\ndef pick (α : Type) [h : Nonempty α] : α := Classical.choice h\nend\n",
        "noncomputable section\ninstance myInst : Inhabited Nat := ⟨Classical.choice ⟨0⟩⟩\nend\n",
        "noncomputable def base : Nat := Classical.choice ⟨0⟩\nnoncomputable section\ndef derived : Nat := base + 1\nend\n",
        "noncomputable section\ndef three : Nat := 3\nend\n#eval three\n",
    ] {
        assert_all_passed(&check_front_door(source));
    }
    let report = check_front_door(
        "noncomputable section\ndef pick : Nat := Classical.choice ⟨0⟩\nend\ndef use : Nat := pick + 1\n",
    );
    assert_refused_with(&report, "use", &["noncomputable", "pick"]);
    let report = check_front_door(
        "noncomputable section\ndef pick : Nat := Classical.choice ⟨0⟩\nend\n#eval pick\n",
    );
    assert_some_refused_with(&report, &["pick"]);
}

#[test]
fn test_front_door_admits_foreign_code_over_a_noncomputable_value() {
    // Lean compiles the `implemented_by` target or calls the `extern` symbol,
    // never the value.
    for source in [
        "def pickImpl (xs : List Nat) : Nat := xs.headD 0\n@[implemented_by pickImpl] def pick (xs : List Nat) : Nat := Classical.choice ⟨xs.length⟩\n",
        "@[extern \"lean_my_hash\"] def myHash (n : Nat) : Nat := Classical.choice ⟨n⟩\n",
    ] {
        assert_all_passed(&check_front_door(source));
    }
}

const NONCOMPUTABLE_N: &str = "noncomputable def N : Nat := Classical.choice ⟨5⟩\n";

#[test]
fn test_front_door_erases_types_proofs_and_parameters() {
    // A noncomputable constant inside a type, a proof, or a constructor's,
    // projection's or matcher's parameter is erased by Lean's compiler.
    for body in [
        "def zero : Fin (N+1) := ⟨0, Nat.zero_lt_succ N⟩\n",
        "def toNat2 (x : Fin (N+1)) : Nat := Fin.val x\n",
        "def getV (x : Fin (N+1)) : Nat := match x with\n  | ⟨v, _⟩ => v\n",
        "def k (n : Nat) : Nat := have h : N = N := rfl; n + 1\n",
        "def k (n : Nat) : Nat := let h : N = N := rfl; n + 1\n",
        "def use (g : (n : Nat) → N = N → Nat) : Nat := g 0 rfl\n",
    ] {
        assert_all_passed(&check_front_door(&format!("{NONCOMPUTABLE_N}{body}")));
    }
    assert_all_passed(&check_front_door(
        "def x : Nat := (fun (_ : True) => 0) (id (Classical.choice ⟨True.intro⟩))\n",
    ));
    // The relevant use stays refused (both Leans: "depends on 'N'").
    let report = check_front_door(&format!("{NONCOMPUTABLE_N}def bad : Nat := N + 1\n"));
    assert_refused_with(&report, "bad", &["noncomputable", "N"]);
}

#[test]
fn test_opaque_of_types_lean_init_inhabits_passes() {
    // Clean's prelude lacks these instances; both Leans' `Init` has them.
    for source in [
        "opaque o : Int\n",
        "opaque o : Char\n",
        "opaque o : UInt8\n",
        "opaque hash : String → UInt64\n",
        "opaque o : Float\n",
        "opaque o : Array Nat\n",
        "opaque o : Nat × Nat\n",
        "opaque o : True\n",
        "opaque T : Type\n",
        "universe u\nopaque o : Sort u\n",
        "opaque st : StateM Nat Unit\n",
    ] {
        assert_all_passed(&check_module(source));
    }
}

#[test]
fn test_opaque_takes_header_and_section_instances() {
    // A section variable's instance and a class-typed explicit binder are
    // local instances, as every class-typed local is in Lean; a `Nonempty`
    // proposition has nothing to compile.
    for source in [
        "variable {α : Type} [Inhabited α]\nopaque o : α\n",
        "opaque o (α : Type) (inst : Inhabited α) : α\n",
        "opaque o (p : Prop) [Nonempty p] : p\n",
    ] {
        assert_all_passed(&check_module(source));
    }
}

#[test]
fn test_opaque_with_foreign_code_over_nonempty_passes() {
    // Lean's FFI pattern: the inhabitant is `Classical.ofNonempty`, never
    // compiled, because the extern symbol or the target is the code.
    for source in [
        "structure Ptr where\n  addr : Nat\ninstance : Nonempty Ptr := ⟨⟨0⟩⟩\n@[extern \"alloc_ptr\"] opaque alloc : Nat → Ptr\n",
        "structure Ptr where\n  addr : Nat\ninstance : Nonempty Ptr := ⟨⟨0⟩⟩\ndef allocImpl (n : Nat) : Ptr := ⟨n⟩\n@[implemented_by allocImpl] opaque alloc : Nat → Ptr\n",
    ] {
        assert_all_passed(&check_module(source));
    }
}

#[test]
fn test_unsafe_opaque_needs_no_inhabitant_at_the_front_door() {
    // Lean's `unsafe opaque` falls back to `sorry`; the front door refuses
    // every safe use of it. `clean check` admits safe uses of unsafe
    // constants, so there it still asks for an inhabitant (fail-closed).
    assert_all_passed(&check_front_door("unsafe opaque o : False\n"));
    let report = check_module("unsafe opaque o : False\n");
    assert_refused_with(&report, "o", &["Inhabited or Nonempty"]);
    let report = check_front_door("unsafe opaque o : False\ntheorem t : False := o\n");
    assert_refused_with(&report, "t", &["unsafe declaration"]);
}

#[test]
fn test_opaque_does_not_open_the_binders_of_its_type() {
    // Both Leans: "failed to synthesize Inhabited ((α : Type) → [inst :
    // Inhabited α] → α)" and the like: only header binders are introduced.
    for (source, name) in [
        ("opaque o : ∀ (α : Type) [Inhabited α], α\n", "o"),
        ("opaque o : Nat → [Inhabited Empty] → Empty\n", "o"),
        ("opaque o : (α : Type) → [Inhabited α] → Nat → α\n", "o"),
        ("opaque o : ∀ (n : Nat) [Inhabited (Fin n)], Fin n\n", "o"),
        (
            "noncomputable opaque o : ∀ (α : Type) [Nonempty α], α\n",
            "o",
        ),
    ] {
        let report = check_module(source);
        assert_refused_with(&report, name, &["Inhabited or Nonempty"]);
    }
}

#[test]
fn test_derive_inhabited_moves_past_fields_lean_cannot_fill_either() {
    // Both Leans take the later constructor: no instance exists for a type
    // the file declared without one, a proposition, a function into the type
    // itself, `Fin n`, or a parameter product before hypotheses.
    for source in [
        "inductive BinOp\n  | add | sub | mul\ninductive MyExpr\n  | bin (op : BinOp) (l r : MyExpr)\n  | lit (n : Nat)\n  | var (name : String)\n  deriving Inhabited\ntheorem t : (default : MyExpr) = MyExpr.lit 0 := rfl\n",
        "inductive Color\n  | red | green\ninductive Px\n  | colored (c : Color)\n  | blank\n  deriving Inhabited\ntheorem t : (default : Px) = Px.blank := rfl\n",
        "inductive B\n  | byte (n : Nat) (h : n < 256)\n  | eof\n  deriving Inhabited\ntheorem t : (default : B) = B.eof := rfl\n",
        "inductive W\n  | sup (f : Nat → W)\n  | leaf\n  deriving Inhabited\ntheorem t : (default : W) = W.leaf := rfl\n",
        "inductive F\n  | mk (n : Nat) (i : Fin n)\n  | none\n  deriving Inhabited\ntheorem t : (default : F) = F.none := rfl\n",
        "inductive Entry (α : Type)\n  | kv (p : α × Nat)\n  | empty\n  deriving Inhabited\ntheorem t : (default : Entry Nat) = Entry.empty := rfl\n",
    ] {
        assert_all_passed(&check_module(source));
    }
}

#[test]
fn test_default_at_a_prelude_transformer_keeps_lean_s_instance_x2() {
    // Both Leans pick `ExceptT`'s own instance (`throw default`): `= .error
    // ""` holds and `= .ok 0` is refused. X2's written carrier reached the
    // generic `instInhabitedOfMonad` here; a prelude head keeps its reduct.
    let report = check_module(
        "theorem good : (default : ExceptT String Id Nat) = (Except.error \"\" : Except String Nat) := rfl\n\
         theorem bad : (default : ExceptT String Id Nat) = (Except.ok 0 : Except String Nat) := rfl\n",
    );
    assert_passed(&report, "good");
    assert_ne!(
        verdict(&report, "bad").kind,
        VerdictKind::Passed,
        "{report:#?}"
    );
}

#[test]
fn test_default_at_option_t_follows_4_30_known_divergence_x2() {
    // KNOWN DIVERGENCE (release-dependent): `(default : OptionT Id Nat)` is
    // `none` in Lean 4.30.0-rc2 (OptionT's own instance) and `some 0` in
    // 4.8.0 (the generic monad instance). Clean answers `none` under both.
    let report =
        check_module("theorem t : (default : OptionT Id Nat) = (none : Option Nat) := rfl\n");
    assert_passed(&report, "t");
}
