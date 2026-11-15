// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Which section `variable`s a declaration receives, end to end — Lean's
//! `withHeaderSecVars` for theorems and `withUsed`/`removeUnusedVars` for the
//! rest (`Lean/Elab/MutualDef.lean:443-490, 593-609`).
//!
//! The class pinned here: whenever the surface use-scan met a construct it
//! does not model — a `by` block, a dependent `if h : …` — the declaration was
//! given EVERY section variable, unused and shadowed ones included, and every
//! later use of it carried implicit arguments nothing could solve (the
//! Mathlib rows `xor_comm`, `Decidable.forall_or_left`, `ite_eq_iff`,
//! `cast_bijective`, `Function.update`, `Function.invFun`,
//! `Function.Injective.preorder`). Each fixture was ground-truthed on the
//! pinned v4.30.0-rc2 `lean` binary (2026-09-12) and is accepted there; the
//! `@`-applications pin the telescope Lean prints with `#check @…`. Driven
//! through the same preprocess-then-elaborate loop `clean check` runs.

use crate::{
    elaborate_decl_and_register_with_context, preprocess_decl_with_context, ElabResult, FileContext,
};
use clean_kernel::Environment;
use clean_parser::parse_file;

/// `(name, Ok | Err(rendering))` per leaf declaration, in file order.
pub(crate) fn run(src: &str) -> Vec<(String, Result<(), String>)> {
    run_with_env(src).1
}

/// [`run`], also handing back the environment the declarations went into.
fn run_with_env(src: &str) -> (Environment, Vec<(String, Result<(), String>)>) {
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
                        ElabResult::Theorem { name, .. }
                        | ElabResult::Definition { name, .. }
                        | ElabResult::Instance { name, .. }
                        | ElabResult::Axiom { name, .. } => {
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
    (env, verdicts)
}

/// Every declaration of `src` elaborates and kernel-checks.
pub(crate) fn assert_all_accepted(src: &str, what: &str) {
    let verdicts = run(src);
    let failures: Vec<_> = verdicts.iter().filter(|(_, v)| v.is_err()).collect();
    assert!(
        failures.is_empty(),
        "{what} — Lean accepts every declaration; Clean refused: {failures:#?}"
    );
}

pub(crate) fn verdict_of<'a>(
    verdicts: &'a [(String, Result<(), String>)],
    name: &str,
) -> &'a Result<(), String> {
    &verdicts
        .iter()
        .find(|(n, _)| n == name)
        .unwrap_or_else(|| panic!("`{name}` must have a verdict; got {verdicts:#?}"))
        .1
}

/// RC1. A theorem proved `by` keeps only its HEADER's section variables, so a
/// use supplies exactly Lean's arguments. `kby` was `unsolved metavariables
/// ?[2, 3, 4]` (the phantom `β γ f`).
#[test]
fn test_section_vars_theorem_tactic_proof_takes_header_variables_only() {
    let src = "namespace T1\n\
               section Thm\n\
               variable {α β γ : Sort _} {f : α → β}\n\
               theorem tby (x : α) : x = x := by exact rfl\n\
               theorem tterm (x : α) : x = x := rfl\n\
               end Thm\n\
               theorem kby : (1 : Nat) = 1 := tby 1\n\
               theorem kterm : (1 : Nat) = 1 := tterm 1\n\
               theorem kby_arity : @tby Nat 1 = @tby Nat 1 := rfl\n\
               end T1\n";
    assert_all_accepted(src, "a `by`-proved theorem's use");
}

/// RC1. An unused EXPLICIT section variable used to become an explicit
/// argument of every `by`-proved theorem, so `thm_tac n` read `n` as that
/// argument (`Type mismatch … got (n : Nat) -> n = n`). Lean:
/// `@thm_tac : ∀ {α : Type} (x : α), x = x`.
#[test]
fn test_section_vars_theorem_tactic_proof_drops_unused_explicit_variable() {
    let src = "namespace T2\n\
               section S\n\
               variable {α : Type} {γ : Type} [Inhabited γ] (a : α)\n\
               theorem thm_tac (x : α) : x = x := by exact rfl\n\
               end S\n\
               theorem use_tac (n : Nat) : n = n := thm_tac n\n\
               end T2\n";
    assert_all_accepted(src, "an unused explicit section variable");
}

/// RC1. The theorem's own binders SHADOW the section variables of the same
/// name, and the shadowed ones are not bound: `xor_comm` (`(a b : Prop)` under
/// `variable {a b : Prop}`, proved `by`), `cast_injective` (`{α β}` under
/// `variable {α β}`, proved `by cases`) and `Decidable.forall_or_left` (its
/// own `{p}` under `variable {p}`, a dependent `if` in a term proof). Uses
/// were `?[1, 2]`, `?[9, 10]` and `?[4, 5]`.
#[test]
fn test_section_vars_theorem_shadowed_section_variables_are_not_bound() {
    let src = "namespace T3\n\
               def Xor2 (a b : Prop) : Prop := (a ∧ ¬b) ∨ (b ∧ ¬a)\n\
               axiom xc_ax (a b : Prop) : Xor2 a b = Xor2 b a\n\
               class Comm' {α : Sort _} (op : α → α → α) : Prop where\n\
               \x20 comm : ∀ a b, op a b = op b a\n\
               section Propositional\n\
               variable {a b : Prop}\n\
               theorem xor_comm2 (a b : Prop) : Xor2 a b = Xor2 b a := by\n\
               \x20 exact xc_ax a b\n\
               instance : Comm' Xor2 := ⟨xor_comm2⟩\n\
               end Propositional\n\
               end T3\n\
               namespace T4\n\
               section\n\
               variable {α β : Sort _}\n\
               theorem cast_injective' {α β : Sort _} (h : α = β) : ∀ x y : α, cast h x = cast h y → x = y := by\n\
               \x20 intro x y hxy\n\
               \x20 cases h\n\
               \x20 exact hxy\n\
               theorem cast_inj' {α β : Type u} (h : α = β) {x y : α} : cast h x = cast h y → x = y :=\n\
               \x20 cast_injective' h x y\n\
               end\n\
               end T4\n\
               namespace T5\n\
               theorem resolve_left' {a b : Prop} (h : a ∨ b) (na : ¬a) : b := Or.elim h (fun ha => absurd ha na) id\n\
               section Quantifiers\n\
               variable {α β : Sort _} {p : α → Prop}\n\
               protected theorem Decidable.forall_or_left' {q : Prop} {p : α → Prop} [Decidable q] :\n\
               \x20   (∀ x, q ∨ p x) ↔ q ∨ ∀ x, p x :=\n\
               \x20 ⟨fun h ↦ if hq : q then Or.inl hq else\n\
               \x20   Or.inr fun x ↦ resolve_left' (h x) hq, fun h x => Or.elim h Or.inl (fun h2 => Or.inr (h2 x))⟩\n\
               theorem forall_or_left'' {q} {p : α → Prop} [Decidable q] : (∀ x, q ∨ p x) ↔ q ∨ ∀ x, p x :=\n\
               \x20 Decidable.forall_or_left'\n\
               end Quantifiers\n\
               end T5\n";
    assert_all_accepted(src, "theorems whose own binders shadow section variables");
}

/// RC1, the instance rule: `[Inhabited Nat]` (no variable in its type) is
/// kept, `[C2 α β]` and `[Inhabited γ]` are not. Lean:
/// `@tonly : ∀ {α : Type} [Inhabited Nat] (a : α), a = a`, so `@tonly Nat
/// ⟨0⟩ 0` is the whole telescope.
#[test]
fn test_section_vars_theorem_instance_rule_matches_lean_arity() {
    let src = "namespace T6\n\
               class C2 (α β : Type) where\n\
               \x20 x : Nat\n\
               section B\n\
               variable {α β : Type} [C2 α β] [Inhabited Nat] {γ : Type} [Inhabited γ]\n\
               theorem tonly (a : α) : a = a := by exact rfl\n\
               end B\n\
               theorem tonly_arity : (0 : Nat) = 0 := @tonly Nat ⟨0⟩ 0\n\
               end T6\n";
    assert_all_accepted(src, "the instance-implicit rule of `withHeaderSecVars`");
}

/// RC1, the refusal half: a proof cannot reach a section variable its header
/// does not keep. Lean rejects `tuse` (`Unknown identifier 'hx'`); keeping
/// the header's variables must not quietly keep this one.
#[test]
fn test_section_vars_theorem_proof_cannot_use_a_variable_the_header_omits() {
    let src = "section\n\
               variable {α : Type} (hx : ∀ a : α, a = a)\n\
               theorem tuse (x : α) : x = x := by exact hx x\n\
               end\n";
    let verdicts = run(src);
    assert!(
        verdict_of(&verdicts, "tuse").is_err(),
        "Lean refuses a proof naming a section variable its header omits: {verdicts:#?}"
    );
}

/// RC2. A def whose body is a dependent `if h : c then … else …` keeps only
/// the section variables it uses (`Function.update`: Lean's
/// `@update : {α : Sort u_1} → {β : α → Sort u_2} → [DecidableEq α] → …`,
/// without the unused `α'` or the shadowed `f a b`), and so does a theorem
/// whose STATEMENT holds one (`dite_stmt`). The `@`-applications pin Lean's
/// arity: they were `Type mismatch: expected Sort ?u_4, got … Decidable (n =
/// n1)` — the `DecidableEq` argument landing in the phantom `α'` slot, the
/// Mathlib row `Function.surjective_eval` — and `update_self`/`update_of_ne`
/// were `unsolved metavariables ?[4, 6, 7, 8]` / `?[5, 7, 8, 9]`.
#[test]
fn test_section_vars_dependent_if_takes_only_used_variables() {
    let src = "universe u v w\n\
               axiom dif_pos' {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} :\n\
               \x20   (dite c t e) = t hc\n\
               axiom dif_neg' {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c → α} {e : ¬c → α} :\n\
               \x20   (dite c t e) = e hnc\n\
               section Update\n\
               variable {α : Sort u} {β : α → Sort v} {α' : Sort w} [DecidableEq α]\n\
               \x20 {f : (a : α) → β a} {a : α} {b : β a}\n\
               def update (f : ∀ a, β a) (a' : α) (v : β a') (a : α) : β a :=\n\
               \x20 if h : a = a' then Eq.ndrec v h.symm else f a\n\
               theorem update_self (a : α) (v : β a) (f : ∀ a, β a) : update f a v a = v :=\n\
               \x20 dif_pos' rfl\n\
               theorem update_of_ne {a a' : α} (h : a ≠ a') (v : β a') (f : ∀ a, β a) : update f a' v a = f a :=\n\
               \x20 dif_neg' h\n\
               theorem dite_stmt (a : α) : (if h : a = a then 1 else 0) = 1 := dif_pos' rfl\n\
               end Update\n\
               theorem update_arity (d : DecidableEq Nat) :\n\
               \x20   @update Nat (fun _ => Nat) d (fun x => x) 0 1 0 = @update Nat (fun _ => Nat) d (fun x => x) 0 1 0 := rfl\n\
               theorem dite_stmt_arity (d : DecidableEq Nat) : @dite_stmt Nat d 0 = @dite_stmt Nat d 0 := rfl\n";
    assert_all_accepted(src, "`Function.update` and a statement holding `if h :`");
}

/// RC2, `Function.invFun`'s shape: `fun y ↦ if h : (∃ x, f x = y) then …`.
/// `invFun2_neg` was `unsolved metavariables ?[4, 6, 7]`, and the ascribed
/// `@`-application pins Lean's `@invFun2 : {α : Sort u_1} → {β : Sort u_2} →
/// [Nonempty α] → (α → β) → β → α`.
#[test]
fn test_section_vars_dependent_if_over_exists_takes_only_used_variables() {
    let src = "universe u\n\
               axiom dif_neg' {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c → α} {e : ¬c → α} :\n\
               \x20   (dite c t e) = e hnc\n\
               axiom chooseX {α : Sort u} {p : α → Prop} (h : Exists p) : α\n\
               axiom arb (α : Sort u) [Nonempty α] : α\n\
               axiom propDec (p : Prop) : Decidable p\n\
               attribute [instance] propDec\n\
               section InvFun\n\
               variable {α β : Sort _} [Nonempty α] {f : α → β} {b : β}\n\
               noncomputable def invFun2 {α : Sort u} {β} [Nonempty α] (f : α → β) : β → α :=\n\
               \x20 fun y ↦ if h : (Exists fun x => f x = y) then chooseX h else arb α\n\
               theorem invFun2_neg (h : ¬Exists fun a => f a = b) : invFun2 f b = arb α :=\n\
               \x20 dif_neg' h\n\
               end InvFun\n\
               theorem invFun2_arity {α β : Type} (a : α) (f : α → β) (y : β) :\n\
               \x20   (@invFun2 α β ⟨a⟩ f y : α) = @invFun2 α β ⟨a⟩ f y := rfl\n";
    assert_all_accepted(src, "`Function.invFun`'s dependent `if` over an `∃`");
}

/// RC3, the `Function.Injective.preorder` shape: an `abbrev` whose structure
/// instance holds a `by` field. The scan cannot see into the tactic block, so
/// the declaration is elaborated with every section variable and the unused
/// `ι` and `π` are then dropped from the elaborated term (Lean's
/// `removeUnusedVars`). `Refl.twice` was `unsolved metavariables ?[0, 3]` —
/// the gate's `Function.Injective.partialOrder` `?[22, 25]` — and the
/// `@`-application pins Lean's `@Refl.pull : {α β : Type} → Refl β → (α → β)
/// → Refl α`.
#[test]
fn test_section_vars_def_with_tactic_field_drops_unused_variables() {
    let src = "namespace V1\n\
               structure Refl (α : Type) where\n\
               \x20 r : α → α → Prop\n\
               \x20 refl : ∀ a, r a a\n\
               section\n\
               variable {ι α β : Type} {π : ι → Type}\n\
               abbrev Refl.pull (s : Refl β) (f : α → β) : Refl α where\n\
               \x20 r a b := s.r (f a) (f b)\n\
               \x20 refl a := by exact s.refl (f a)\n\
               abbrev Refl.twice (s : Refl β) (f : α → β) : Refl α := Refl.pull s f\n\
               end\n\
               theorem pull_arity (s : Refl Nat) (f : Nat → Nat) : @Refl.pull Nat Nat s f = @Refl.pull Nat Nat s f := rfl\n\
               end V1\n";
    assert_all_accepted(src, "an `abbrev` with a `by` field");
}

/// RC3. A `def` proved `by` keeps what its elaborated value uses — `α` — and
/// NOT the unused instance `[Inhabited α]` or `β`: for a definition Lean has
/// no instance rule, only occurrence (`@dby : {α : Type} → α → α`). The
/// recorded parameter names follow the pruned telescope, so the named
/// argument `(x := …)` still lands on `x`.
#[test]
fn test_section_vars_def_tactic_body_keeps_only_what_its_value_uses() {
    let src = "section\n\
               variable {α : Type} [Inhabited α] {β : Type}\n\
               def dby (x : α) : α := by exact x\n\
               end\n\
               theorem dby_arity : @dby Nat 0 = 0 := rfl\n\
               theorem dby_named : dby (x := (0 : Nat)) = 0 := rfl\n";
    assert_all_accepted(src, "a `by`-bodied def's arity and named arguments");
}

/// RC3, the other direction: a tactic may use a section variable without
/// naming it (`assumption` picks up `h`), and the pruning keeps it because the
/// elaborated value mentions it. Lean: `usesH : 1 = 1 → 1 = 1`. `usesH_arity`
/// was `unsolved metavariables ?[4]` (the phantom `β`).
#[test]
fn test_section_vars_def_tactic_body_keeps_a_variable_used_without_its_name() {
    let src = "namespace V3\n\
               section\n\
               variable (h : 1 = 1) {β : Type}\n\
               def usesH : 1 = 1 := by assumption\n\
               end\n\
               theorem usesH_arity : 1 = 1 := usesH rfl\n\
               end V3\n";
    assert_all_accepted(src, "a section hypothesis a tactic uses unnamed");
}

/// RC3 for an `instance` with a `by` field: registered with the unused `β` and
/// `b` it could never be found (`failed to synthesize instance V4.HasTrue
/// Nat`); pruned, it is Lean's `HasTrue Nat`.
#[test]
fn test_section_vars_instance_with_tactic_field_drops_unused_variables() {
    let src = "namespace V4\n\
               class HasTrue (α : Type) : Prop where\n\
               \x20 t : True\n\
               section\n\
               variable {β : Type} (b : β)\n\
               instance : HasTrue Nat where\n\
               \x20 t := by exact True.intro\n\
               end\n\
               theorem useInst : HasTrue Nat := inferInstance\n\
               end V4\n";
    assert_all_accepted(src, "an instance with a `by` field");
}

/// RC3, the universe half: a section variable the pruning drops takes its
/// universe with it. `β : Sort v` is unused by both instances (each holds a
/// `by` field, so the scan cannot see them and every section variable is
/// prepended first); left in the registered level list, `v` would be a level
/// nothing constrains at every use of the instance (the pre-fix face:
/// `useInst` "failed to synthesize instance `V5.HasTrue Nat`", its only
/// candidate `(u : Sort v) -> u -> V5.HasTrue Nat`). Lean, with
/// `pp.universes`: `hasTrueNat : HasTrue Nat` and `boxNat : Inhabited.{1}
/// (Box Nat)` — no universe parameter on either. The assertion is on `v`
/// alone: the instance path registers the context's universe list
/// unfiltered, so `boxNat` also registers a minted `?u_0` where Lean
/// registers nothing — a separate defect this change neither adds nor
/// removes.
#[test]
fn test_section_vars_pruned_instance_drops_the_dropped_variables_universe() {
    let src = "namespace V5\n\
               universe v\n\
               class HasTrue (α : Type) : Prop where\n\
               \x20 t : True\n\
               structure Box (α : Type) where\n\
               \x20 val : α\n\
               \x20 ok : True\n\
               section\n\
               variable {β : Sort v} (b : β)\n\
               instance hasTrueNat : HasTrue Nat where\n\
               \x20 t := by exact True.intro\n\
               instance boxNat : Inhabited (Box Nat) where\n\
               \x20 default := { val := 0, ok := by exact True.intro }\n\
               end\n\
               theorem useInst : HasTrue Nat := inferInstance\n\
               theorem useBox : (default : Box Nat).val = 0 := rfl\n\
               end V5\n";
    let (env, verdicts) = run_with_env(src);
    let failures: Vec<_> = verdicts.iter().filter(|(_, v)| v.is_err()).collect();
    assert!(
        failures.is_empty(),
        "Lean accepts every declaration; Clean refused: {failures:#?}"
    );
    let v = clean_kernel::Name::from_string("v");
    for name in ["V5.hasTrueNat", "V5.boxNat"] {
        let info = env
            .get_const(&clean_kernel::Name::from_string(name))
            .unwrap_or_else(|| panic!("`{name}` must be registered; got {verdicts:#?}"));
        assert!(
            !info.level_params.contains(&v),
            "`{name}` must not register the dropped variable's universe `v` (Lean \
             registers no universe parameter); got {:?}",
            info.level_params
        );
    }
}
