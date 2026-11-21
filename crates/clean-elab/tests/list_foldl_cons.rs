// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Checked fold equations at distinct carrier types and universes.
use clean_elab::{
    elaborate_decl_and_register, prepare_session_environment, preprocess_decl_with_context,
    ElabResult, FileContext,
};
use clean_kernel::{reference::ReferenceKernel, Declaration, Environment, Expr, Level, Name};
use clean_parser::parse_file;

const POSITIVE: &str = r"
universe u v
theorem polymorphic_fold_cons {α : Type u} {β : Type v} (a : α) (l : List α) (f : β → α → β) (b : β) : List.foldl f b (a :: l) = List.foldl f (f b a) l := List.foldl_cons
theorem simplify_fold_cons {α : Type u} {β : Type v} (a : α) (l : List α) (f : β → α → β) (b : β) : List.foldl f b (a :: l) = List.foldl f (f b a) l := by simp only [List.foldl_cons]
theorem different_carriers (a : Nat) (l : List Nat) (b : Bool) : List.foldl (fun (acc : Bool) (_ : Nat) => Bool.not acc) b (a :: l) = List.foldl (fun (acc : Bool) (_ : Nat) => Bool.not acc) (Bool.not b) l := List.foldl_cons
theorem higher_universe_accumulator : List.foldl (fun (acc : Type) (_ : Nat) => acc) Nat [0] = List.foldl (fun (acc : Type) (_ : Nat) => acc) Nat [] := List.foldl_cons
theorem empty_tail_fold : List.foldl Nat.add 0 [1] = Nat.add 0 1 := List.foldl_cons
theorem retained_tail_fold : List.foldl Nat.add 0 (1 :: [2, 3]) = List.foldl Nat.add (Nat.add 0 1) [2, 3] := List.foldl_cons
";

fn failed(result: &ElabResult) -> bool {
    match result {
        ElabResult::Failed { .. } => true,
        ElabResult::Multiple(xs) => xs.iter().any(failed),
        _ => false,
    }
}
fn register(env: &mut Environment, source: &str) -> Result<(), String> {
    let mut context = FileContext::new();
    for declaration in parse_file(source).map_err(|error| format!("{error:?}"))? {
        let declaration = preprocess_decl_with_context(&declaration, &mut context);
        let result =
            elaborate_decl_and_register(env, &declaration).map_err(|error| error.to_string())?;
        if failed(&result) {
            return Err(format!("{result:?}"));
        }
    }
    Ok(())
}
fn environment() -> Environment {
    let mut env = Environment::with_prelude();
    prepare_session_environment(&mut env);
    env
}

#[test]
fn actual_polymorphic_fold_source_replays_without_axioms() {
    let mut env = environment();
    register(&mut env, POSITIVE).expect("actual fold source");
    let mut reference = ReferenceKernel::new(env).expect("source provenance");
    for name in [
        "polymorphic_fold_cons",
        "simplify_fold_cons",
        "different_carriers",
        "higher_universe_accumulator",
        "empty_tail_fold",
        "retained_tail_fold",
    ] {
        let original = Name::from_string(name);
        let info = reference
            .environment()
            .get_const(&original)
            .expect("actual source theorem");
        let type_ = info.type_.clone();
        let params = info.level_params.clone();
        let levels = params.iter().cloned().map(Level::param).collect::<Vec<_>>();
        let alias = Name::from_string(&format!("source_reference_{name}"));
        reference
            .add_checked(Declaration::Theorem {
                name: alias.clone(),
                level_params: params,
                type_,
                value: Expr::const_(original, levels),
            })
            .expect("replay actual source proof closure and its universes");
        assert!(reference
            .environment()
            .axiom_deps(&alias)
            .expect("closure")
            .is_empty());
    }
}
#[test]
fn source_refuses_original_fold_proof_without_accumulator_step() {
    let mut env = environment();
    let before = (env.num_constants(), env.num_instances());
    let source = "theorem bad_foldl (α β : Type) (a : α) (l : List α) (f : β → α → β) (b : β) : List.foldl f b (a :: l) = List.foldl f b l := List.foldl_cons";
    assert!(register(&mut env, source).is_err());
    assert!(env.get_const(&Name::from_string("bad_foldl")).is_none());
    assert_eq!((env.num_constants(), env.num_instances()), before);
}
#[test]
fn source_cannot_drop_tail_or_swap_element_and_accumulator_carriers() {
    for source in [
        "theorem bad_foldl : List.foldl Nat.add 0 (1 :: [2]) = List.foldl Nat.add (Nat.add 0 1) [] := List.foldl_cons",
        "theorem bad_foldl (l : List Nat) (b : Bool) : List.foldl Nat.add b (1 :: l) = List.foldl Nat.add b l := List.foldl_cons",
    ] {
        let mut env = environment();
        let before = (env.num_constants(), env.num_instances());
        assert!(
            register(&mut env, source).is_err(),
            "false source: {source}"
        );
        assert!(env.get_const(&Name::from_string("bad_foldl")).is_none());
        assert_eq!((env.num_constants(), env.num_instances()), before);
    }
}
