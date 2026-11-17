// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Class attributes validate the registered declaration, through both public
//! source entry points. The original baseline epochs are retained in Git and
//! reports; public duplicate refusal is aligned with the incoming Lean cohort.

use clean_elab::{
    elaborate_decl_and_register_with_context, preprocess_decl_with_context, ElabError, ElabResult,
    FileContext,
};
use clean_kernel::{Environment, Name};
use clean_parser::parse_file;

fn check(env: &mut Environment, context: &mut FileContext, source: &str) -> Result<(), ElabError> {
    fn inner_failure(result: &ElabResult) -> Option<ElabError> {
        match result {
            ElabResult::Failed { error, .. } => Some(error.as_ref().clone()),
            ElabResult::Multiple(results) => results.iter().find_map(inner_failure),
            _ => None,
        }
    }

    let decls =
        parse_file(source).unwrap_or_else(|e| panic!("fixture must parse: {e:?}\n{source}"));
    for decl in decls {
        let decl = preprocess_decl_with_context(&decl, context);
        let result = elaborate_decl_and_register_with_context(env, &decl, context)?;
        if let Some(error) = inner_failure(&result) {
            return Err(error);
        }
    }
    Ok(())
}

fn accept(env: &mut Environment, context: &mut FileContext, source: &str) {
    check(env, context, source).unwrap_or_else(|e| panic!("fixture must check: {e}\n{source}"));
}

fn name(value: &str) -> Name {
    Name::from_string(value)
}

fn refuse_target(env: &mut Environment, context: &mut FileContext, source: &str, target: &str) {
    let error = check(env, context, source).expect_err("a non-class target must be refused");
    assert_eq!(
        error.to_string(),
        format!(
            "invalid 'class', declaration '{target}' must be inductive datatype, structure, or constant"
        )
    );
    assert!(
        !env.is_class(&name(target)),
        "refusal must not register a class"
    );
}

#[test]
fn declaration_attribute_refuses_the_measured_definition() {
    let mut env = Environment::with_prelude();
    refuse_target(
        &mut env,
        &mut FileContext::new(),
        "@[class] def Foo (n : Nat) : Prop := n > 2\n",
        "Foo",
    );
}

#[test]
fn standalone_attribute_refuses_the_measured_definition() {
    let mut env = Environment::with_prelude();
    let mut context = FileContext::new();
    accept(
        &mut env,
        &mut context,
        "def Bla (n : Nat) : Prop := n > 2\n",
    );
    refuse_target(&mut env, &mut context, "attribute [class] Bla\n", "Bla");
}

#[test]
fn theorem_opaque_constructor_recursor_and_quotient_are_not_axiom_classes() {
    let mut env = Environment::with_prelude();
    let mut context = FileContext::new();
    accept(
        &mut env,
        &mut context,
        "theorem proof : True := True.intro\nopaque hidden : Nat := 7\n",
    );
    for target in ["proof", "hidden", "Nat.zero", "Nat.rec", "Quot"] {
        refuse_target(
            &mut env,
            &mut context,
            &format!("attribute [class] {target}\n"),
            target,
        );
    }
}

#[test]
fn declaration_and_standalone_axiom_classes_keep_their_telescope_metadata() {
    let mut env = Environment::with_prelude();
    let mut context = FileContext::new();
    accept(
        &mut env,
        &mut context,
        "@[class] axiom Inline (α : Type) (β : Type) (γ : Type) : Type\n\
         axiom Later (α : Type) (β : Type) (γ : Type) : Type\n\
         attribute [class] Later\n\
         def inlineClass [value : Inline Nat Nat Nat] : Inline Nat Nat Nat := value\n\
         def laterClass [value : Later Nat Nat Nat] : Later Nat Nat Nat := value\n",
    );
    for target in ["Inline", "Later"] {
        let info = env.get_class_info(&name(target)).expect("axiom is a class");
        assert_eq!(info.num_params, 3);
        assert!(info.out_params.is_empty());
        assert!(info.semi_out_params.is_empty());
    }
}

#[test]
fn standalone_inductive_class_is_usable_for_instance_synthesis() {
    let mut env = Environment::with_prelude();
    accept(
        &mut env,
        &mut FileContext::new(),
        "inductive Flag where\n  | mk : Flag\n\
         attribute [class] Flag\n\
         def flagInstance : Flag := Flag.mk\n\
         attribute [instance] flagInstance\n\
         def selectFlag [value : Flag] : Flag := value\n\
         def selected : Flag := selectFlag\n",
    );
    assert_eq!(
        env.get_class_info(&name("Flag"))
            .expect("Flag class")
            .num_params,
        0
    );
    assert!(env.is_instance(&name("flagInstance")));
    assert!(env
        .get_const(&name("selected"))
        .expect("checked value")
        .value
        .is_some());
    assert!(env
        .axiom_deps(&name("selected"))
        .expect("registered value")
        .is_empty());
}

#[test]
fn standalone_structure_class_preserves_parameters_and_checked_instance_use() {
    let mut env = Environment::with_prelude();
    accept(
        &mut env,
        &mut FileContext::new(),
        "structure Holder (α : Type) where\n  value : α\n\
         attribute [class] Holder\n\
         def holderInstance : Holder Nat := ⟨7⟩\n\
         attribute [instance] holderInstance\n\
         def readHolder {α : Type} [value : Holder α] : α := value.value\n\
         theorem selected_seven : (readHolder : Nat) = 7 := rfl\n",
    );
    assert_eq!(
        env.get_class_info(&name("Holder"))
            .expect("Holder class")
            .num_params,
        1
    );
    assert!(env.is_instance(&name("holderInstance")));
    assert!(env
        .axiom_deps(&name("selected_seven"))
        .expect("checked theorem")
        .is_empty());
}

#[test]
fn repeating_class_attribute_preserves_existing_output_metadata() {
    let mut env = Environment::with_prelude();
    let mut context = FileContext::new();
    accept(
        &mut env,
        &mut context,
        "class Route (α : Type) (β : outParam Type) (γ : semiOutParam Type) where\n  route : α → β → γ\n",
    );
    let before = env
        .get_class_info(&name("Route"))
        .expect("Route class")
        .clone();
    assert_eq!(before.num_params, 3);
    assert_eq!(before.out_params, [1]);
    assert_eq!(before.semi_out_params, [2]);
    for _ in 0..2 {
        let error = check(&mut env, &mut context, "attribute [class] Route\n")
            .expect_err("the public class attribute refuses duplicate registration");
        assert_eq!(error.to_string(), "class has already been declared 'Route'");
        assert_eq!(env.get_class_info(&name("Route")), Some(&before));
    }
}

#[test]
fn invalid_target_preflight_does_not_partially_apply_other_attributes_or_targets() {
    let mut env = Environment::with_prelude();
    let mut context = FileContext::new();
    accept(
        &mut env,
        &mut context,
        "structure Candidate where\n  value : Nat\n\
         def invalid : Nat := 7\n\
         theorem proof : True := True.intro\n",
    );
    refuse_target(
        &mut env,
        &mut context,
        "attribute [class] Candidate invalid\n",
        "invalid",
    );
    assert!(
        !env.is_class(&name("Candidate")),
        "all class targets are preflighted"
    );
    refuse_target(
        &mut env,
        &mut context,
        "attribute [simp, class] proof\n",
        "proof",
    );
    assert!(
        !env.is_simp_lemma(&name("proof")),
        "invalid class does not apply simp first"
    );
    accept(&mut env, &mut context, "attribute [class] Candidate\n");
    assert!(
        env.is_class(&name("Candidate")),
        "refusal does not poison a later valid command"
    );
}

#[test]
fn local_and_scoped_class_wrappers_are_refused_without_registration() {
    for scope in ["local", "scoped"] {
        let mut env = Environment::with_prelude();
        let mut context = FileContext::new();
        accept(
            &mut env,
            &mut context,
            "structure Candidate where\n  value : Nat\n",
        );
        let error = check(
            &mut env,
            &mut context,
            &format!("attribute [{scope} class] Candidate\n"),
        )
        .expect_err("class attributes must be global");
        assert!(error.to_string().contains("class"), "{error}");
        assert!(error.to_string().contains("global"), "{error}");
        assert!(!env.is_class(&name("Candidate")));
    }
}

#[test]
fn namespace_resolution_validates_the_resolved_target_not_a_root_namesake() {
    let mut env = Environment::with_prelude();
    let mut context = FileContext::new();
    accept(
        &mut env,
        &mut context,
        "structure Candidate where\n  value : Nat\n",
    );
    refuse_target(
        &mut env,
        &mut context,
        "namespace Inner\ndef Candidate : Nat := 7\nattribute [class] Candidate\nend Inner\n",
        "Inner.Candidate",
    );
    assert!(!env.is_class(&name("Candidate")));
}

#[test]
fn unknown_attribute_still_refuses_before_class_registration() {
    let mut env = Environment::with_prelude();
    let mut context = FileContext::new();
    accept(
        &mut env,
        &mut context,
        "structure Candidate where\n  value : Nat\n",
    );
    let error = check(
        &mut env,
        &mut context,
        "attribute [class, noSuchClassAttribute] Candidate\n",
    )
    .expect_err("unknown attributes remain errors");
    assert_eq!(
        error.to_string(),
        "Unknown attribute `[noSuchClassAttribute]`"
    );
    assert!(!env.is_class(&name("Candidate")));
}

#[test]
fn header_first_batch_refuses_invalid_class_attribute_without_publishing() {
    use clean_elab::module_batch::{elaborate_module, BatchOptions, SourceUnit, UnitId};

    let mut env = Environment::with_prelude();
    let decls = parse_file("@[class] def invalid : Nat := 7\n").expect("fixture must parse");
    let units = [SourceUnit {
        id: UnitId(0),
        decls: &decls,
    }];
    let outcome = elaborate_module(
        &mut env,
        &mut FileContext::new(),
        &units,
        BatchOptions::islands(),
    );
    assert!(
        !outcome.committed,
        "invalid attribute must refuse batch publication"
    );
    assert!(outcome.render_rejections().contains("invalid 'class'"));
    assert!(!env.is_class(&name("invalid")));
    assert!(
        env.get_const(&name("invalid")).is_none(),
        "all-or-nothing batch rolls back"
    );
}

#[test]
fn axiom_marker_telescope_survives_both_class_attribute_forms() {
    let mut env = Environment::with_prelude();
    let mut context = FileContext::new();
    accept(
        &mut env,
        &mut context,
        "@[class] axiom InlineMarked (α : Type) (β : outParam Type) (γ : semiOutParam Type) : Type\n\
         axiom LaterMarked (α : Type) (β : outParam Type) (γ : semiOutParam Type) : Type\n\
         attribute [class] LaterMarked\n",
    );
    for target in ["InlineMarked", "LaterMarked"] {
        let info = env.get_class_info(&name(target)).expect("axiom class");
        assert_eq!(info.num_params, 3);
        assert_eq!(info.out_params, [1]);
        assert_eq!(info.semi_out_params, [2]);
    }
}

#[test]
fn duplicate_targets_in_one_packet_do_not_register_a_partial_class() {
    let mut env = Environment::with_prelude();
    let mut context = FileContext::new();
    accept(
        &mut env,
        &mut context,
        "structure Candidate where\n  val : Nat\n",
    );
    let error = check(
        &mut env,
        &mut context,
        "attribute [class] Candidate Candidate\n",
    )
    .expect_err("a duplicate packet is refused before attribute effects");
    assert_eq!(
        error.to_string(),
        "class has already been declared 'Candidate'"
    );
    assert!(!env.is_class(&name("Candidate")));
}
