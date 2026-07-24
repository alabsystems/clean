// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Regression: the leads-to temporal relation `F ~> G` (a level-50 custom
//! `infixl` whose token lexes to `Ident("~>")`) must parse, elaborate, and
//! kernel-check as the binary application `LeadsTo F G`, exactly like the
//! tighter `□`/`◇` prefix notations at level 100.
//!
//! This mirrors the shape of Trust's `Trust.Temporal` prelude (namespaced
//! definitions, `_root_.`-anchored notation targets, `□`/`◇`/`~>`/`⊨` declared
//! together, and a `= rfl` unfolding theorem). Before the low-precedence
//! custom-infix band (levels 45–50) was modeled, `~>` (50) and `⊨` (45) sat
//! below `CUSTOM_PREC_FLOOR` (then 60); the use site `(F ~> G)` left the
//! operator unconsumed, the enclosing paren `expect(RParen)` failed, and the
//! theorem collapsed into an error-recovery `RawDecl` — poisoning elaboration
//! of the whole prelude.

use clean_elab::{
    elaborate_decl_and_register_with_context, preprocess_decl_with_context, ElabResult, FileContext,
};
use clean_kernel::env::Environment;
use clean_parser::{parse_file, SurfaceDecl};

/// A self-contained analogue of `Trust/Temporal.lean`: the exact notation
/// declarations and the `~>` unfolding theorem that regressed.
const TEMPORAL_SOURCE: &str = r#"namespace Trust
namespace Temporal

def Behavior (State : Type) := Nat → State
def Formula (State : Type) := Behavior State → Prop

def drop {State : Type} (b : Behavior State) (n : Nat) : Behavior State :=
  fun k => b (n + k)

def Always {State : Type} (F : Formula State) : Formula State :=
  fun b => ∀ n, F (drop b n)

def Eventually {State : Type} (F : Formula State) : Formula State :=
  fun b => ∃ n, F (drop b n)

def LeadsTo {State : Type} (F G : Formula State) : Formula State :=
  Always (fun b => F b → Eventually G b)

structure StateMachine (State : Type) where
  init : State → Prop
  next : State → State → Prop

def Runs {State : Type} (M : StateMachine State) (b : Behavior State) : Prop :=
  M.init (b 0) ∧ ∀ n, M.next (b n) (b (Nat.succ n)) ∨ b (Nat.succ n) = b n

def Satisfies {State : Type} (M : StateMachine State) (F : Formula State) : Prop :=
  ∀ b, Runs M b → F b

prefix:100 "□" => _root_.Trust.Temporal.Always
prefix:100 "◇" => _root_.Trust.Temporal.Eventually
infixl:50 " ~> " => _root_.Trust.Temporal.LeadsTo
infixl:45 " ⊨ " => _root_.Trust.Temporal.Satisfies

theorem box_unfolds {State : Type} (F : Formula State) : (□ F) = Always F := rfl
theorem diamond_unfolds {State : Type} (F : Formula State) : (◇ F) = Eventually F := rfl
theorem leadsto_unfolds {State : Type} (F G : Formula State) :
    (F ~> G) = LeadsTo F G := rfl

end Temporal
end Trust
"#;

/// Flatten nested `namespace` blocks into one list of leaf declarations.
fn flatten<'a>(decls: &'a [SurfaceDecl], out: &mut Vec<&'a SurfaceDecl>) {
    for decl in decls {
        out.push(decl);
        if let SurfaceDecl::Namespace { decls, .. } = decl {
            flatten(decls, out);
        }
    }
}

#[test]
fn leadsto_notation_parses_elaborates_and_kernel_checks() {
    // 1. Parse: no declaration may fall into error recovery.
    let declarations = parse_file(TEMPORAL_SOURCE).expect("temporal prelude must parse");
    let mut flat = Vec::new();
    flatten(&declarations, &mut flat);
    for decl in &flat {
        if let SurfaceDecl::RawDecl { content, .. } = decl {
            panic!("`~>` regressed: declaration fell into error recovery: {content:?}");
        }
    }
    let theorems: Vec<&str> = flat
        .iter()
        .filter_map(|decl| match decl {
            SurfaceDecl::Theorem { name, .. } => Some(name.as_str()),
            _ => None,
        })
        .collect();
    assert!(
        theorems.contains(&"box_unfolds")
            && theorems.contains(&"diamond_unfolds")
            && theorems.contains(&"leadsto_unfolds"),
        "expected box/diamond/leadsto unfolding theorems, got {theorems:?}"
    );

    // 2. Elaborate + register + kernel-check every declaration. Registration
    //    into the kernel environment is a real value typecheck, so a passing
    //    `leadsto_unfolds : (F ~> G) = LeadsTo F G := rfl` proves `F ~> G`
    //    elaborated to exactly `LeadsTo F G` (otherwise `rfl` would not check).
    let mut env = Environment::with_prelude();
    let mut ctx = FileContext::new();
    ctx.disable_external_import_search();
    for declaration in &declarations {
        let processed = preprocess_decl_with_context(declaration, &mut ctx);
        let result = elaborate_decl_and_register_with_context(&mut env, &processed, &mut ctx)
            .unwrap_or_else(|error| panic!("elaboration failed: {error}"));
        let mut leaves = Vec::new();
        result.leaf_decls(&mut leaves);
        if let Some(ElabResult::Failed { name, error, .. }) = leaves
            .into_iter()
            .find(|leaf| matches!(leaf, ElabResult::Failed { .. }))
        {
            panic!("declaration `{name}` failed to elaborate: {error:?}");
        }
    }

    // 3. The `~>` unfolding theorem is in the kernel environment.
    assert!(
        env.get_const(&clean_kernel::name::Name::from_string(
            "Trust.Temporal.leadsto_unfolds"
        ))
        .is_some(),
        "Trust.Temporal.leadsto_unfolds must be registered after kernel checking"
    );
}
