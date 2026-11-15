// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The selection rules of [`super::select_section_binders`], read off the
//! binders `preprocess_decl_with_context` prepends. Every expectation is the
//! telescope the pinned v4.30.0-rc2 `lean` prints with `#check @…` for the
//! same text (measured 2026-09-12).

use crate::infer::section_prune::{PruneRule, SectionPruneRequest};
use crate::{preprocess_decl_with_context, FileContext};
use clean_parser::{parse_file, SurfaceBinder, SurfaceBinderInfo, SurfaceDecl, SurfaceExpr};

/// A binder as Lean prints it in a telescope: its name, or `[Class Arg …]`
/// for an anonymous instance binder.
fn render(binder: &SurfaceBinder) -> String {
    fn atom(e: &SurfaceExpr) -> String {
        match e {
            SurfaceExpr::Ident(_, n) => n.to_string(),
            SurfaceExpr::App(_, f, args) => {
                let mut out = atom(f);
                for a in args {
                    out.push(' ');
                    out.push_str(&atom(&a.expr));
                }
                out
            }
            other => format!("{other:?}"),
        }
    }
    if binder.info == SurfaceBinderInfo::Instance && binder.name.is_unescaped_component("_") {
        let ty = binder.ty.as_deref().map(atom).unwrap_or_default();
        return format!("[{ty}]");
    }
    binder.name.to_string()
}

/// The binders the value declaration `name` carries after preprocessing.
fn binders_of(code: &str, name: &str) -> Vec<String> {
    let decls = parse_file(code).expect("fixture parses");
    let mut fc = FileContext::new();
    for decl in &decls {
        let processed = preprocess_decl_with_context(decl, &mut fc);
        let found = match &processed {
            SurfaceDecl::Theorem {
                name: n, binders, ..
            }
            | SurfaceDecl::Def {
                name: n, binders, ..
            } if n.to_string() == name => Some(binders),
            _ => None,
        };
        if let Some(binders) = found {
            return binders.iter().map(render).collect();
        }
    }
    panic!("no declaration `{name}` in the fixture");
}

/// `withHeaderSecVars`: a theorem proved `by` keeps the section variables its
/// HEADER uses. The surface scan cannot see into a tactic block, and it used
/// to answer that with every section variable — `β`, `γ` and `f` too, which
/// nothing at a use site could ever solve (`kby` in the RC-K replica:
/// `unsolved metavariables ?[2, 3, 4]`). Lean: `@tby : ∀ {α : Sort u_1}
/// (x : α), x = x`.
#[test]
fn test_select_section_binders_theorem_with_tactic_proof_takes_header_variables() {
    let code = "variable {α β γ : Sort _} {f : α → β}\n\
                theorem tby (x : α) : x = x := by exact rfl\n";
    assert_eq!(binders_of(code, "tby"), ["α", "x"]);
}

/// The proof is never consulted, whatever it contains — a dependent `if` in
/// a term proof is the same wall as a `by` block. Lean:
/// `@forall_or_left' : ∀ {α : Sort u_1} {q : Prop} {p : α → Prop}
/// [Decidable q], …` — the section `p`, shadowed by the theorem's own, and
/// the unused `β` are both left out.
#[test]
fn test_select_section_binders_theorem_dependent_if_in_proof_is_not_scanned() {
    let code = "variable {α β : Sort _} {p : α → Prop}\n\
                theorem forall_or_left' {q : Prop} {p : α → Prop} [Decidable q] :\n\
                \x20   (∀ x, q ∨ p x) ↔ q ∨ ∀ x, p x :=\n\
                \x20 ⟨fun h ↦ if hq : q then Or.inl hq else\n\
                \x20   Or.inr fun x ↦ Or.resolve_left (h x) hq, fun h x => Or.elim h Or.inl (fun h2 => Or.inr (h2 x))⟩\n";
    assert_eq!(
        binders_of(code, "forall_or_left'"),
        ["α", "q", "p", "[Decidable q]"]
    );
}

/// The section variables `select_section_binders` hands the declaration
/// `name` (its own binders not included), with the pruning it arms.
fn selection_of(code: &str, name: &str) -> (Vec<String>, Option<SectionPruneRequest>) {
    let decls = parse_file(code).expect("fixture parses");
    let mut fc = FileContext::new();
    for decl in &decls {
        if crate::preprocess_ext::decl_name(decl).is_some_and(|n| n.to_string() == name) {
            let selection = super::select_section_binders(
                fc.current_variables(),
                decl,
                Some(fc.macro_ctx()),
                fc.included_variables(),
            );
            return (
                selection.binders.iter().map(render).collect(),
                selection.prune,
            );
        }
        let _ = preprocess_decl_with_context(decl, &mut fc);
    }
    panic!("no declaration `{name}` in the fixture");
}

/// The instance rule of `withHeaderSecVars` needs EVERY variable the
/// instance's type mentions to be kept (`.all`, `MutualDef.lean:484`) — in
/// the ELABORATED header. `[Inhabited γ]` mentions only `γ`, which the header
/// does not, so it stays out, and `[Inhabited Nat]` — whose type mentions no
/// variable at all — is kept. `[C2 α β]` the surface cannot decide: the header
/// names `α`, and could name `β` through the instance (were `β` an
/// `outParam`), so `β` and `[C2 α β]` are prepended too and the rule is armed
/// for the elaborated statement, where it drops both. Lean:
/// `@tonly : ∀ {α : Type} [Inhabited Nat] (a : α), a = a` — the arity
/// `tests_section_variable_inclusion` pins end to end.
#[test]
fn test_select_section_binders_theorem_partially_mentioned_instance_defers_to_elaboration() {
    let code = "class C2 (α β : Type) where\n  x : Nat\n\
                variable {α β : Type} [C2 α β] [Inhabited Nat] {γ : Type} [Inhabited γ]\n\
                theorem tonly (a : α) : a = a := by exact rfl\n";
    assert_eq!(
        binders_of(code, "tonly"),
        ["α", "β", "[C2 α β]", "[Inhabited Nat]", "a"]
    );
    let (selected, prune) = selection_of(code, "tonly");
    assert_eq!(selected, ["α", "β", "[C2 α β]", "[Inhabited Nat]"]);
    let prune =
        prune.expect("an undecidable instance rule must be armed for the elaborated header");
    assert_eq!(prune.section_names.len(), 4, "{prune:?}");
    assert_eq!(
        prune.rule,
        PruneRule::Header {
            forced: vec![false; 4]
        }
    );
}

/// The `outParam` shape the deferral exists for: the header names `F`, and
/// Lean keeps `β` and `[Get F β]` because `Get.get f` elaborates to
/// `@Get.get F β inst f` (`@get_congr : ∀ {F β : Type} [inst : Get F β]
/// [Inhabited β] (f g : F), f = g → Get.get f = Get.get g`). `[Inhabited β]`
/// and `[C2 F γ]` ride along to the elaborated rule, which keeps the first and
/// drops the second with `γ`.
#[test]
fn test_select_section_binders_theorem_out_param_instance_defers_to_elaboration() {
    let code = "class Get (F : Type) (β : outParam Type) where\n  get : F → β\n\
                class C2 (α β : Type) where\n  x : Nat\n\
                variable {F β : Type} [Get F β] [Inhabited β] {γ : Type} [C2 F γ]\n\
                theorem get_congr (f g : F) (h : f = g) : Get.get f = Get.get g := by rw [h]\n";
    let (selected, prune) = selection_of(code, "get_congr");
    assert_eq!(
        selected,
        ["F", "β", "[Get F β]", "[Inhabited β]", "γ", "[C2 F γ]"]
    );
    assert!(
        matches!(
            prune,
            Some(SectionPruneRequest {
                rule: PruneRule::Header { .. },
                ..
            })
        ),
        "{prune:?}"
    );
}

/// No deferral when the surface decides the rule: every instance's variables
/// are kept or none of them is.
#[test]
fn test_select_section_binders_theorem_decided_instance_rule_arms_nothing() {
    let code = "variable {α : Type} [Inhabited α] {β : Type} [Inhabited β]\n\
                theorem tby (x : α) : x = x := by exact rfl\n";
    let (selected, prune) = selection_of(code, "tby");
    assert_eq!(selected, ["α", "[Inhabited α]"]);
    assert!(prune.is_none(), "{prune:?}");
}

/// The instance rule still activates on a kept variable: `[Inhabited α]` is
/// kept once `α` is. Lean: `@tby : ∀ {α : Type} [Inhabited α] (x : α), x = x`
/// (with the `unusedSectionVars` linter naming `[Inhabited α]`).
#[test]
fn test_select_section_binders_theorem_instance_over_kept_variable_is_kept() {
    let code = "variable {α : Type} [Inhabited α] {β : Type}\n\
                theorem tby (x : α) : x = x := by exact rfl\n";
    assert_eq!(binders_of(code, "tby"), ["α", "[Inhabited α]", "x"]);
}

/// `include` belongs to the theorem rule only: a `def` keeps what it uses.
/// Lean: `include h` then `def dinc : Nat := 0` gives `dinc : Nat`.
#[test]
fn test_select_section_binders_def_ignores_include() {
    let code = "variable {α : Type} (h : α)\ninclude h\ndef dinc : Nat := 0\n";
    assert_eq!(binders_of(code, "dinc"), Vec::<String>::new());
}

/// A `where` helper's parameters bind inside its body, so a section variable
/// of the same name is not "used" by it. Lean: `@f : Nat → Nat`.
#[test]
fn test_select_section_binders_where_helper_parameter_shadows_section_variable() {
    let code = "variable {n : Nat}\n\
                def f (x : Nat) : Nat := g x\nwhere\n  g (n : Nat) : Nat := n\n";
    assert_eq!(binders_of(code, "f"), ["x"]);
}

/// An anonymous instance binder is never reached by NAME: every one is
/// called `_`, so a name-keyed closure that activated `[Inhabited α]` also
/// pulled in `[Inhabited β]` and the unused `β`. Lean: `@dflt : {α : Type} →
/// [Inhabited α] → α → α`.
#[test]
fn test_select_section_binders_def_anonymous_instance_does_not_reach_another() {
    let code = "variable {α : Type} [Inhabited α] {β : Type} [Inhabited β]\n\
                def dflt (x : α) : α := default\n";
    assert_eq!(binders_of(code, "dflt"), ["α", "[Inhabited α]", "x"]);
}

/// A `def` that scans completely still defers to the elaborated term once an
/// instance was ACTIVATED rather than named: `[DecidableEq α]` is prepended —
/// the value might resolve through it — and `removeUnusedVars` is armed to
/// drop it when the value does not. Lean: `@konst : {α : Type} → α → α`.
#[test]
fn test_select_section_binders_def_activated_instance_arms_the_used_rule() {
    let code = "variable {α : Type} [DecidableEq α] {β : Type} [Inhabited β]\n\
                def konst (a : α) : α := a\n";
    let (selected, prune) = selection_of(code, "konst");
    assert_eq!(selected, ["α", "[DecidableEq α]"]);
    let prune = prune.expect("an activated instance is decided on the elaborated term");
    assert_eq!(prune.rule, PruneRule::Used);
    assert_eq!(prune.section_names.len(), 2, "{prune:?}");
}

/// Nothing is armed when the named closure is the whole selection: no
/// instance was activated, so the surface already gives Lean's answer.
#[test]
fn test_select_section_binders_def_named_variables_only_arms_nothing() {
    let code = "variable {α : Type} {β : Type} [Inhabited β]\n\
                def konst (a : α) : α := a\n";
    let (selected, prune) = selection_of(code, "konst");
    assert_eq!(selected, ["α"]);
    assert!(prune.is_none(), "{prune:?}");
}

/// A telescope binds left to right: a binder type that names `a` BEFORE the
/// declaration's own `a` is bound names the section variable, which Lean then
/// includes; one that names it after does not. Lean (pinned v4.30.0-rc2,
/// 2026-09-20): `@late : ∀ (a : Nat), a = a → ∀ (a : Bool), a = a` and
/// `@early : ∀ (a : Bool), a = a → a = a`. Own-binder names used to be struck
/// from the used set wherever they were mentioned, so `late` lost the section
/// `a` and its `h` named an auto-bound variable instead.
#[test]
fn test_select_section_binders_mention_before_own_binder_keeps_the_section_variable() {
    let code = "variable (a : Nat) (b : Nat)\n\
                theorem late (h : a = a) (a : Bool) : a = a := rfl\n\
                theorem early (a : Bool) (h : a = a) : a = a := rfl\n\
                def late_def (n : Nat := a) (a : Bool) : Bool := a\n";
    assert_eq!(binders_of(code, "late"), ["a", "h", "a"]);
    assert_eq!(binders_of(code, "early"), ["a", "h"]);
    assert_eq!(binders_of(code, "late_def"), ["a", "n", "a"]);
}
