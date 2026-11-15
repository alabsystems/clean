// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! An instance-implicit binder of a simp lemma that the left-hand side does
//! not determine is filled by typeclass synthesis in the goal's scope, as
//! Lean's `synthesizeArgs` (`Rewrite.lean:57-100`) fills it — a global
//! instance, a local one, a `Prop`-valued class, and a universe-polymorphic
//! lemma alike — and a `scoped instance` answers only where its namespace is
//! open. Clean skipped every non-`Prop` slot and never ran synthesis, so these
//! rewrites made no progress (measured 2026-09-12: `Unique.bijective`'s
//! `eq_iff_true_of_subsingleton [Subsingleton α]`,
//! `Decidable.forall_or_left [Decidable q]`).
//!
//! Every fixture was ground-truthed on the pinned v4.30.0-rc2 `lean` binary
//! (2026-09-12): each accepted declaration elaborates there as written, and
//! `unopened` fails there with "`simp` made no progress".

use crate::{
    elaborate_decl_and_register_with_context, preprocess_decl_with_context, ElabResult, FileContext,
};
use clean_kernel::Environment;
use clean_parser::parse_file;

/// `(name, Ok | Err(rendering))` per leaf declaration, in file order, run
/// through the preprocess-then-elaborate loop `clean check` runs (namespace
/// and `open` state persist across declarations).
fn run(src: &str) -> Vec<(String, Result<(), String>)> {
    let decls = parse_file(src).unwrap_or_else(|e| panic!("fixture must parse: {e:?}"));
    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();
    let mut verdicts = Vec::new();
    for decl in &decls {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        match elaborate_decl_and_register_with_context(&mut env, &processed, &mut file_ctx) {
            Ok(result) => {
                let mut leaves = Vec::new();
                result.leaf_decls(&mut leaves);
                for leaf in leaves {
                    match leaf {
                        ElabResult::Failed { name, error, .. } => {
                            verdicts.push((name.to_string(), Err(format!("{error:?}"))));
                        }
                        ElabResult::Theorem { name, .. } | ElabResult::Definition { name, .. } => {
                            verdicts.push((name.to_string(), Ok(())));
                        }
                        _ => {}
                    }
                }
            }
            Err(e) => verdicts.push((
                crate::preprocess_ext::decl_name(decl)
                    .map_or_else(|| "<decl>".to_string(), ToString::to_string),
                Err(format!("{e:?}")),
            )),
        }
    }
    verdicts
}

fn verdict_of<'a>(
    verdicts: &'a [(String, Result<(), String>)],
    name: &str,
) -> &'a Result<(), String> {
    &verdicts
        .iter()
        .find(|(n, _)| n == name)
        .unwrap_or_else(|| panic!("`{name}` must have a verdict; got {verdicts:?}"))
        .1
}

const CLASSES: &str = "axiom PP {α : Type} : α → Prop\n\
                       class Inh1 (α : Type) where\n\
                       \x20 pt : α\n\
                       instance : Inh1 Nat := ⟨0⟩\n\
                       class NE1 (α : Type) : Prop where\n\
                       \x20 ok : ∃ _ : α, True\n\
                       instance : NE1 Nat := ⟨⟨0, True.intro⟩⟩\n\
                       axiom lemK {α : Type} [Inh1 α] (x : α) : PP x ↔ True\n\
                       axiom lemL {α : Type} [NE1 α] (x : α) : PP x ↔ True\n\
                       axiom lemKe {α : Type} [Inh1 α] (x : α) : PP x = True\n";

/// A class binder the LHS leaves open is synthesized — global or local
/// instance, `Type`- or `Prop`-valued class, `↔` or `=` lemma.
#[test]
fn test_simp_synthesizes_an_undetermined_instance_binder() {
    let src = format!(
        "{CLASSES}\
         theorem tK (n : Nat) : PP n := by simp only [lemK]\n\
         theorem tK_local {{α : Type}} [Inh1 α] (x : α) : PP x := by simp only [lemK]\n\
         theorem tL (n : Nat) : PP n := by simp only [lemL]\n\
         theorem tL_local {{α : Type}} [NE1 α] (x : α) : PP x := by simp only [lemL]\n\
         theorem tKe (n : Nat) : PP n := by simp only [lemKe]\n"
    );
    let verdicts = run(&src);
    for name in ["tK", "tK_local", "tL", "tL_local", "tKe"] {
        if let Err(e) = verdict_of(&verdicts, name) {
            panic!("`{name}`: simp must synthesize the lemma's instance binder as Lean does: {e}");
        }
    }
}

/// The same for a universe-polymorphic lemma: its level is solved by the
/// match, then the instance is synthesized at that level — including through
/// a universe-polymorphic INSTANCE (`instL`), whose level parameter the
/// search instantiates with a level metavariable of its own. That
/// metavariable is drawn from the proof state's level mint: a private counter
/// would spell it `?u_0`, which the name-keyed `MetaState` reads as the
/// declaration's own (rigid) `?u_0`, and the candidate would be refused.
///
/// The instances are declared as axioms because, when this was written, a
/// source `instance` of a universe-polymorphic class registered with its
/// elaborator's universe metavariables as extra level parameters
/// (`instInh3Nat.{?u_0}`), which the synthesis refuses to let escape — a
/// separate defect of `elab_instance`, not of simp. That defect is closed
/// (the instance result sites run `finalize_level_params`); the SOURCE form
/// is pinned by
/// `test_simp_synthesizes_a_source_instance_of_a_universe_polymorphic_class`.
#[test]
fn test_simp_synthesizes_the_instance_binder_of_a_universe_polymorphic_lemma() {
    let src = "class Inh3 (α : Sort u) where\n\
               \x20 pt : α\n\
               axiom instN : Inh3 Nat\n\
               attribute [instance] instN\n\
               @[instance] axiom instL {α : Type u} : Inh3 (List α)\n\
               axiom QQ {α : Sort u} : α → Prop\n\
               axiom lemU {α : Sort u} [Inh3 α] (x : α) : QQ x ↔ True\n\
               theorem tU (n : Nat) : QQ n := by simp only [lemU]\n\
               theorem tUL (l : List Nat) : QQ l := by simp only [lemU]\n\
               theorem tULw {β : Type w} (l : List β) : QQ l := by simp only [lemU]\n\
               theorem tU_local {β : Sort w} [Inh3 β] (b : β) : QQ b := by simp only [lemU]\n";
    let verdicts = run(src);
    for name in ["tU", "tUL", "tULw", "tU_local"] {
        if let Err(e) = verdict_of(&verdicts, name) {
            panic!("`{name}`: simp must synthesize a polymorphic lemma's instance binder: {e}");
        }
    }
}

/// The same with the instances written as SOURCE `instance` declarations —
/// anonymous and named, monomorphic and universe-polymorphic. It used to fail
/// before simp was even reached: the instance registered as
/// `instInh3Nat.{?u_0}` and the synthesis refused to let that level escape.
#[test]
fn test_simp_synthesizes_a_source_instance_of_a_universe_polymorphic_class() {
    let src = "class Inh3 (α : Sort u) where\n\
               \x20 pt : α\n\
               instance : Inh3 Nat := ⟨0⟩\n\
               instance instL {α : Type u} : Inh3 (List α) := ⟨[]⟩\n\
               axiom QQ {α : Sort u} : α → Prop\n\
               axiom lemU {α : Sort u} [Inh3 α] (x : α) : QQ x ↔ True\n\
               theorem tU (n : Nat) : QQ n := by simp only [lemU]\n\
               theorem tUL (l : List Nat) : QQ l := by simp only [lemU]\n\
               theorem tULw {β : Type w} (l : List β) : QQ l := by simp only [lemU]\n";
    let verdicts = run(src);
    for name in ["tU", "tUL", "tULw"] {
        if let Err(e) = verdict_of(&verdicts, name) {
            panic!("`{name}`: a source instance must answer simp's synthesis: {e}");
        }
    }
}

/// A `scoped instance` answers only where its namespace is open — Lean's
/// scoping holds for simp's synthesis as for every other instance query.
#[test]
fn test_simp_instance_synthesis_respects_scoped_instances() {
    let src = "axiom PP {α : Type} : α → Prop\n\
               class Inh1 (α : Type) where\n\
               \x20 pt : α\n\
               namespace Foo\n\
               scoped instance instInhBool : Inh1 Bool := ⟨true⟩\n\
               end Foo\n\
               axiom lemK {α : Type} [Inh1 α] (x : α) : PP x ↔ True\n\
               section\n\
               open Foo\n\
               theorem opened (b : Bool) : PP b := by simp only [lemK]\n\
               end\n\
               theorem unopened (b : Bool) : PP b := by simp only [lemK]\n";
    let verdicts = run(src);
    if let Err(e) = verdict_of(&verdicts, "opened") {
        panic!("with `open Foo` the scoped instance must answer: {e}");
    }
    let err = verdict_of(&verdicts, "unopened")
        .as_ref()
        .expect_err("without `open Foo` Lean's simp makes no progress; so must Clean's");
    assert!(
        err.contains("NoProgress") || err.contains("no progress"),
        "the refusal must be simp's own 'no progress': {err}"
    );
}
