// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! WS6.10 (F-107) — an `instance` closes its universe levels like a `def`.
//!
//! ## The gap (proof program, `STANDALONE.p11_typeclass_instance`)
//!
//! ```lean
//! class Scale (α : Type) where
//!   scale : α → α
//! instance instScaleU64 : Scale UInt64 where
//!   scale := fun (x : UInt64) => x * 3
//! def triple (x : UInt64) : UInt64 := @Scale.scale UInt64 instScaleU64 x
//! ```
//!
//! `clean check` accepted this, but the header-first batch (the path targo's
//! embedded Clean runs) refused the module:
//!
//! ```text
//! error: `instScaleU64` was registered with a different signature than the
//!        one other declarations were elaborated against
//!   note: staged     {} Scale UInt64
//!   note: registered {?u_0, ?u_1, ?u_2} Scale UInt64
//! ```
//!
//! Re-measured at this worktree before the fix (reproduced). Cause: all three
//! instance forms returned the elaborator's whole minted-level vector as the
//! instance's level parameters, so a monomorphic instance registered with three
//! unused levels in the reserved `?u_N` metavariable spelling. The one-at-a-time
//! driver accepted that silently; the batch's header-agreement check, correctly,
//! did not. Instances now close through `finalize_level_params`, as `def` does.

use clean_elab::module_batch::{elaborate_module, BatchOptions, SourceUnit, UnitId};
use clean_elab::{elaborate_decl_and_register, preprocess_decl_with_context, FileContext};
use clean_kernel::env::Environment;
use clean_kernel::Name;
use clean_parser::parse_file;

const P11: &str = "\
class Scale (α : Type) where
  scale : α → α

instance instScaleU64 : Scale UInt64 where
  scale := fun (x : UInt64) => x * 3

def triple (x : UInt64) : UInt64 := @Scale.scale UInt64 instScaleU64 x
";

struct Batch {
    env: Environment,
    committed: bool,
    rejections: String,
}

/// The header-first batch — the module path targo's embedded Clean runs.
fn batch(source: &str) -> Batch {
    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();
    let decls = parse_file(source).expect("fixture must parse");
    let units = [SourceUnit {
        id: UnitId(0),
        decls: &decls,
    }];
    let outcome = elaborate_module(&mut env, &mut file_ctx, &units, BatchOptions::islands());
    Batch {
        committed: outcome.committed,
        rejections: outcome.render_rejections(),
        env,
    }
}

/// The one-declaration-at-a-time driver — the path `clean check` runs.
fn sequential(source: &str) -> Result<Environment, String> {
    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();
    let decls = parse_file(source).map_err(|e| format!("parse error: {e:?}"))?;
    for decl in &decls {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        elaborate_decl_and_register(&mut env, &processed).map_err(|e| e.to_string())?;
    }
    Ok(env)
}

fn level_params(env: &Environment, name: &str) -> Vec<String> {
    env.get_const(&Name::from_string(name))
        .unwrap_or_else(|| panic!("`{name}` must be registered"))
        .level_params
        .iter()
        .map(ToString::to_string)
        .collect()
}

/// Port of the proof-program row `STANDALONE.p11_typeclass_instance`, front-end
/// half: the probe commits through the header-first batch, the instance is
/// registered with NO level parameters (its staged header's), and the program
/// computes — `triple 5 = 15` by `rfl`, in the same batch.
#[test]
fn standalone_p11_typeclass_instance_commits_through_the_header_first_batch() {
    let source = format!("{P11}\ntheorem triple_5 : triple 5 = 15 := rfl\n");
    let checked = batch(&source);
    assert!(
        checked.committed,
        "p11 must commit through the header-first batch, got:\n{}",
        checked.rejections
    );
    assert_eq!(
        level_params(&checked.env, "instScaleU64"),
        Vec::<String>::new()
    );
    assert!(checked
        .env
        .get_const(&Name::from_string("triple_5"))
        .is_some());
}

/// The same instance through `clean check`'s driver: it was ACCEPTED there
/// before, with the three leaked `?u_N` levels. The registered interface is
/// now the same on both paths.
#[test]
fn ws6_10_monomorphic_instance_registers_no_level_params_sequentially() {
    let env = sequential(P11).unwrap_or_else(|e| panic!("p11 must check: {e}"));
    assert_eq!(level_params(&env, "instScaleU64"), Vec::<String>::new());
}

/// Mutation control: finalization drops only levels that do NOT occur. A
/// genuinely polymorphic instance keeps its declared level, and an
/// undetermined level that DOES occur is generalized into the writable `u_N`
/// space — never registered in the reserved `?u_N` spelling. So the fix does
/// not over-refuse, and does not over-strip.
#[test]
fn ws6_10_polymorphic_instance_keeps_the_levels_it_uses() {
    let env = sequential(
        "\
universe u

instance instInhPUnit : Inhabited PUnit.{u+1} := ⟨PUnit.unit⟩

instance instInhSort : Inhabited (Sort _) := ⟨PUnit⟩
",
    )
    .unwrap_or_else(|e| panic!("polymorphic instances must check: {e}"));
    assert_eq!(level_params(&env, "instInhPUnit"), vec!["u".to_string()]);
    let generalized = level_params(&env, "instInhSort");
    assert_eq!(
        generalized.len(),
        1,
        "the `Sort _` level occurs, so it must be generalized, got {generalized:?}"
    );
    assert!(
        !generalized[0].starts_with('?'),
        "a registered level must never carry the reserved `?u_N` spelling, got {generalized:?}"
    );
}

/// Negative twin: p11 with ONE mutation — the instance's method returns a
/// `Bool` where the class demands `UInt64` — is still refused by the batch,
/// with the instance named and NOTHING registered. Closing levels at the
/// instance boundary accepts the well-typed program; it does not accept an
/// ill-typed one.
#[test]
fn ws6_10_ill_typed_p11_twin_is_still_refused() {
    let checked = batch(&P11.replace("=> x * 3", "=> x == 3"));
    assert!(
        !checked.committed,
        "the ill-typed twin must be refused, but the batch committed"
    );
    assert!(
        checked
            .rejections
            .contains("error: `instScaleU64` did not elaborate"),
        "the refusal must name the ill-typed instance, got:\n{}",
        checked.rejections
    );
    for name in ["instScaleU64", "triple"] {
        assert!(
            checked.env.get_const(&Name::from_string(name)).is_none(),
            "`{name}` reached the environment from a REFUSED batch"
        );
    }
}

// --- WS6.10 review: adversarial inputs the implementation was not written against ---

/// All three instance forms — short `:=` anonymous-constructor, structure
/// literal, and an ANONYMOUS `where` — now close through `finish_instance`.
/// The p11 port exercises only the named `where` form, so each of the other
/// two paths, and the minted-name path, is driven here through the
/// header-first batch, and the instances are USED by synthesis and computed
/// by the kernel (`rfl`), wrapping at the carrier width.
const THREE_FORMS: &str = "\
class Scale (α : Type) where
  scale : α → α

instance instScaleU8 : Scale UInt8 := ⟨fun x => x * 3⟩

instance instScaleU16 : Scale UInt16 := { scale := fun x => x * 5 }

instance : Scale UInt32 where
  scale := fun x => x * 7

def t8 (x : UInt8) : UInt8 := Scale.scale x
def t16 (x : UInt16) : UInt16 := Scale.scale x
def t32 (x : UInt32) : UInt32 := Scale.scale x
theorem t16_2 : t16 2 = 10 := rfl
theorem t32_2 : t32 2 = 14 := rfl
";

#[test]
fn ws6_10_review_all_three_instance_forms_commit_through_the_batch() {
    let source = format!("{THREE_FORMS}theorem t8_100 : t8 100 = 44 := rfl\n");
    let checked = batch(&source);
    assert!(
        checked.committed,
        "every instance form must commit through the header-first batch, got:\n{}",
        checked.rejections
    );
    for name in ["instScaleU8", "instScaleU16"] {
        assert_eq!(
            level_params(&checked.env, name),
            Vec::<String>::new(),
            "`{name}` is monomorphic and must register no level parameters"
        );
    }
    for name in ["t8_100", "t16_2", "t32_2"] {
        assert!(
            checked.env.get_const(&Name::from_string(name)).is_some(),
            "`{name}` must be registered"
        );
    }
}

/// Negative twin of the above: the SAME module with one false claim —
/// `t8 100 = 45`, where `100 * 3 = 300` wraps to 44 — is refused by the batch,
/// so closing the instance levels did not make a false theorem provable.
#[test]
fn ws6_10_review_three_forms_false_wrap_claim_is_refused() {
    let checked = batch(&format!(
        "{THREE_FORMS}theorem t8_100 : t8 100 = 45 := rfl\n"
    ));
    assert!(
        !checked.committed,
        "`t8 100 = 45` is false (300 wraps to 44) but the batch committed"
    );
    assert!(
        checked.rejections.contains("t8_100"),
        "the refusal must name the false theorem, got:\n{}",
        checked.rejections
    );
    assert!(checked
        .env
        .get_const(&Name::from_string("t8_100"))
        .is_none());
}

/// A GENUINELY universe-polymorphic instance (file-level `universe u`, an
/// instance-implicit binder, a structure over `Type u`) must stage and
/// register the SAME level list `[u]` through the batch — finalization keeps a
/// declared level that occurs, so the header-agreement check still passes —
/// and a downstream use through synthesis computes.
#[test]
fn ws6_10_review_polymorphic_instance_commits_through_the_batch() {
    let checked = batch(
        "\
universe u
structure Box (α : Type u) where
  val : α
instance instInhBox {α : Type u} [Inhabited α] : Inhabited (Box α) := ⟨⟨default⟩⟩
def b : Box Nat := default
theorem b_eq : b.val = 0 := rfl
",
    );
    assert!(
        checked.committed,
        "a universe-polymorphic instance must commit through the batch, got:\n{}",
        checked.rejections
    );
    assert_eq!(
        level_params(&checked.env, "instInhBox"),
        vec!["u".to_string()]
    );
    assert!(checked.env.get_const(&Name::from_string("b_eq")).is_some());
}
