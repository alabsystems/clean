// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! More adversarial shapes for the section-variable selection: the theorem
//! rule's instance and `include` clauses, instances and `abbrev`s with tactic
//! fields, `outParam` classes, dotted access — and the `ElabCtx`-level section
//! path, which the file-level driver never reaches. Ground truth as in
//! [`crate::tests_section_variable_inclusion_adv`] (pinned v4.30.0-rc2,
//! 2026-09-20; every fixture is accepted there).

use crate::tests_section_variable_inclusion::assert_all_accepted;
use crate::ElabResult;
use clean_kernel::{Environment, Expr, ExprKind};
use clean_parser::parse_file;

/// `withHeaderSecVars`' instance clause, with `by` proofs throughout. Lean:
/// `@t_alpha : ∀ {α : Type} [Inhabited α] (x : α), x = x` (not `[C2 α β]`: `β`
/// is not kept; not `[Inhabited γ]`), `@t_dflt : ∀ {α : Type} [inst :
/// Inhabited α], default = default`, `@t_conv : ∀ {α β : Type} [Inhabited α]
/// [inst : C2 α β] (x : α), …`.
#[test]
fn test_section_vars_theorem_instance_clause_keeps_instances_over_kept_variables_only() {
    let src = r"namespace B3
class C2 (α β : Type) where
  conv : α → β
section S
variable {α β γ : Type} [Inhabited α] [C2 α β] [Inhabited γ] (a : α) (g : γ) (hg : g = g)
theorem t_alpha (x : α) : x = x := by exact Eq.refl x
theorem t_dflt : (default : α) = default := by exact Eq.refl default
theorem t_conv (x : α) : (C2.conv x : β) = C2.conv x := by exact Eq.refl (C2.conv x)
end S
theorem u_alpha_at : (1 : Nat) = 1 := @t_alpha Nat _ 1
theorem u_dflt_at : (default : Nat) = default := @t_dflt Nat _
instance : C2 Nat Bool := ⟨fun n => n == 0⟩
theorem u_conv : (C2.conv (1 : Nat) : Bool) = C2.conv 1 := t_conv 1
theorem u_conv_at : (C2.conv (1 : Nat) : Bool) = C2.conv 1 := @t_conv Nat Bool _ _ 1
end B3
";
    assert_all_accepted(src, "the theorem rule's instance clause");
}

/// `include` reaches theorems — by identity, so a theorem binder of the same
/// name does not cancel it — and never definitions; `omit` cancels it. Lean:
/// `@t_inc : ∀ {α γ : Type} [Inhabited α] [Inhabited γ] (g : γ), g = g → ∀
/// (x : α), x = x`, `@t_inc_shadow : ∀ {γ : Type} [Inhabited γ] (g : γ), g = g
/// → ∀ (g : Nat), g = g`, `@d_inc : Nat → Nat`, `@tomit : True`.
#[test]
fn test_section_vars_include_reaches_theorems_by_identity_and_never_definitions() {
    let src = r"namespace B7
section S2
variable {α γ : Type} [Inhabited α] [Inhabited γ] (g : γ) (hg : g = g)
include hg
theorem t_inc (x : α) : x = x := by
  have _ := hg
  exact Eq.refl x
theorem t_inc_shadow (g : Nat) : g = g := by exact Eq.refl g
def d_inc (n : Nat) : Nat := by exact n
variable (z : Nat)
omit hg
theorem tomit : True := by exact True.intro
end S2
theorem u_inc_at : (1 : Nat) = 1 := @t_inc Nat Bool _ _ true rfl 1
theorem u_inc_shadow_at : (2 : Nat) = 2 := @t_inc_shadow Bool _ true rfl 2
def u_d_inc : Nat := @d_inc 3
theorem u_omit : True := tomit
end B7
";
    assert_all_accepted(src, "`include` / `omit` over `by` proofs");
}

/// Definitions, `abbrev`s and instances with a tactic field or body, in a
/// section whose variables include an instance: each keeps what its ELABORATED
/// value uses. `Pre.lift` is the `Function.Injective.preorder` shape (own
/// binders shadow the section's `f`; `ι π` and `[Tag β]` unused); `instTagProd`
/// reaches `[Tag β]` only through resolution inside `by`; `instTagOpt`'s own
/// `{β} [Tag β]` shadow the section's. Lean: `@Pre.lift : {α β : Type} → [Pre
/// β] → (α → β) → Pre α`, `@instPreNat : Pre Nat`, `@instTagProd : {β : Type}
/// → [Tag β] → Tag (β × Nat)`, `@instTagOpt : {β : Type} → [Tag β] → Tag
/// (Option β)`, `@tagOf : {β : Type} → [Tag β] → β → Nat`, `@idBy : {β : Type}
/// → β → β`.
#[test]
fn test_section_vars_instances_with_tactic_fields_keep_what_their_value_uses() {
    let src = r"namespace B2
class Pre (α : Type) where
  le : α → α → Prop
  le_refl : ∀ a, le a a
class Tag (α : Type) where
  tag : Nat
section S
variable {ι α β : Type} {π : ι → Type} [Tag β] (f : α → β)
abbrev Pre.lift [Pre β] (f : α → β) : Pre α where
  le a b := Pre.le (f a) (f b)
  le_refl a := by exact Pre.le_refl (f a)
instance instPreNat : Pre Nat where
  le a b := a = b
  le_refl _ := by rfl
instance instTagProd : Tag (β × Nat) where
  tag := by exact Tag.tag β + 1
instance instTagOpt {β : Type} [Tag β] : Tag (Option β) where
  tag := by exact Tag.tag β
instance instTagList : Tag (List β) := ⟨by exact Tag.tag β⟩
def tagOf (_x : β) : Nat := by exact Tag.tag β
def idBy (x : β) : β := by exact x
end S
instance : Tag Bool := ⟨1⟩
def u1 : Pre Bool := @Pre.lift Bool Nat instPreNat (fun b => if b then 1 else 0)
def u2 : Pre Nat := inferInstance
def u3 : Nat := Tag.tag (Bool × Nat)
def u3at : Tag (Bool × Nat) := @instTagProd Bool _
def u4at : Tag (Option Bool) := @instTagOpt Bool _
def u5 : Nat := Tag.tag (List Bool)
def u6at : Nat := @tagOf Bool _ true
def u7at : Nat := @idBy Nat 3
theorem u8 : @Pre.le Nat inferInstance 2 2 := Pre.le_refl 2
end B2
";
    assert_all_accepted(src, "instances and abbrevs with tactic fields");
}

/// An `outParam` class: the section instance `[Get F β]` reaches a definition
/// through resolution (`getIt`, `getBy`) or not at all (`idF`). Lean: `@getIt
/// : {F β : Type} → [Get F β] → F → β`, `@idF : {F : Type} → F → F`, `@getBy`
/// as `getIt`, `@get_congr : ∀ {F β : Type} [inst : Get F β] (f g : F), …`.
#[test]
fn test_section_vars_out_param_instance_reaches_a_definition_only_through_its_value() {
    let src = r"namespace A4
class Get (F : Type) (β : outParam Type) where
  get : F → β
section S
variable {F β γ : Type} [Get F β] (unused : γ)
def getIt (f : F) : β := Get.get f
def idF (f : F) : F := f
def getBy (f : F) : β := by exact Get.get f
theorem get_congr (f g : F) (h : f = g) : Get.get f = Get.get g := by rw [h]
end S
instance : Get Nat Bool := ⟨fun n => n == 0⟩
def v1at : Bool := @getIt Nat Bool _ 3
def v2at : Nat := @idF Nat 3
def v3at : Bool := @getBy Nat Bool _ 3
theorem v4at : Get.get (3 : Nat) = Get.get (3 : Nat) := @get_congr Nat Bool _ 3 3 rfl
end A4
";
    assert_all_accepted(src, "an outParam section instance over definitions");
}

/// A section variable reached only as a projection receiver, a structure
/// update source or a named argument is used; the unused `(unused : Bool)` is
/// not. Lean: `@len : {α : Type} → List α → Nat`, `@px : Pt → Nat`, `@px_eq :
/// ∀ (p : Pt), p.x = p.x`.
#[test]
fn test_section_vars_dotted_access_and_named_arguments_use_the_section_variable() {
    let src = r"namespace B9
structure Pt where
  x : Nat
  y : Nat
section S
variable {α : Type} (xs : List α) (p : Pt) (h : p.x = p.x) (unused : Bool)
def len : Nat := xs.length
def px : Nat := p.x + p.y
def upd : Pt := { p with x := 1 }
def mk : Pt := Pt.mk (y := p.y) (x := 0)
theorem px_eq : p.x = p.x := by rfl
end S
def u1at : Nat := @len Nat [1, 2]
def u2 : Nat := @px ⟨1, 2⟩
def u3 : Pt := @upd ⟨1, 2⟩
def u4 : Pt := @mk ⟨1, 2⟩
theorem u5at : (⟨1, 2⟩ : Pt).x = (⟨1, 2⟩ : Pt).x := @px_eq ⟨1, 2⟩
end B9
";
    assert_all_accepted(src, "dotted access and named arguments");
}

/// The number of leading `Π` binders of `ty`.
fn pi_arity(ty: &Expr) -> usize {
    let mut n = 0;
    let mut cur = ty;
    while let ExprKind::Pi(_, _, body) = cur.kind() {
        n += 1;
        cur = body;
    }
    n
}

/// The `ElabCtx`-level section path (`ElabCtx::elab_decl` on a `section`
/// block, `prepend_section_binders`) arms the same pruning the file-level
/// driver does. It registers nothing, so the pin reads the elaborated types:
/// Lean gives `@f : {α : Type} → α → α`, `@t : ∀ {α : Type} (x : α), x = x`
/// and `@g : {β : Type} → β → β` — two binders each, where the unpruned
/// telescopes had six.
#[test]
fn test_section_vars_elabctx_section_path_prunes_the_unused_variables() {
    let src = r"section S
variable {α : Type} {β : Type} (b : β) [Inhabited β]
def f (x : α) : α := by exact x
theorem t (x : α) : x = x := by exact Eq.refl x
def g : β := by exact b
end S
";
    let decls = parse_file(src).unwrap_or_else(|e| panic!("fixture must parse: {e:?}"));
    let [section] = decls.as_slice() else {
        panic!(
            "one `section` block expected, got {} declarations",
            decls.len()
        );
    };
    let env = Environment::with_prelude();
    let result = crate::elaborate_decl(&env, section)
        .unwrap_or_else(|e| panic!("the section must elaborate: {e:?}"));
    let mut leaves = Vec::new();
    result.leaf_decls(&mut leaves);
    let arities: Vec<(String, usize)> = leaves
        .iter()
        .filter_map(|leaf| match leaf {
            ElabResult::Definition { name, ty, .. } | ElabResult::Theorem { name, ty, .. } => {
                Some((name.to_string(), pi_arity(ty)))
            }
            _ => None,
        })
        .collect();
    assert_eq!(
        arities,
        [
            ("f".to_string(), 2),
            ("t".to_string(), 2),
            ("g".to_string(), 2)
        ],
        "each declaration keeps exactly the section variables Lean keeps"
    );
}
