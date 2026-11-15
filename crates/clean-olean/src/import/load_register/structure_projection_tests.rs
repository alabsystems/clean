// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::{structure_table_contradiction, TableFault};
use clean_kernel::{Environment, Name};

struct DeclarationBudget;
impl Drop for DeclarationBudget {
    fn drop(&mut self) {
        clean_kernel::tc::clear_declaration_budget();
    }
}

#[test]
fn cic_l_projection_tables_fit_original_budget_and_refuse_tampering() {
    let lib = crate::require_pinned_lean_lib_path().expect("pinned Lean is required");
    let compiled = crate::test_support::compiled_fixture_dir("cic_l_level");
    let paths = [compiled, lib];
    let module = Name::from_string("CICL.CoreTyping");
    let structure = Name::from_string("CICL.ConstantDecl");
    {
        let mut env = Environment::try_with_prelude_for_import().expect("import prelude");
        clean_kernel::tc::set_declaration_budget(1);
        let _budget = DeclarationBudget;
        let result = crate::load_typed_module_with_deps_bounded_shared(
            &mut env,
            &module,
            &paths,
            1000,
            &mut hashbrown::HashSet::new(),
        );
        assert!(clean_kernel::tc::declaration_budget_exhausted());
        let error = result.expect_err("the bounded import cannot finish");
        assert!(
            matches!(error, crate::ImportError::ResourceLimit { .. }),
            "{error}"
        );
        assert!(error.is_resource_refusal());
        assert!(!error.is_inconsistent_artifact());
        assert!(env.get_structure_field_names(&structure).is_none());
    }

    // The unchanged original source-import budget now authenticates the real
    // artifact after the theory stopped importing unrelated Nat/List lemmas.
    let mut env = Environment::try_with_prelude_for_import().expect("import prelude");
    clean_kernel::tc::set_declaration_budget(2_000_000);
    let _budget = DeclarationBudget;
    crate::load_typed_module_with_deps_bounded_shared(
        &mut env,
        &module,
        &paths,
        1000,
        &mut hashbrown::HashSet::new(),
    )
    .expect("the real structure imports within the original budget");
    assert!(!clean_kernel::tc::declaration_budget_exhausted());
    eprintln!(
        "CIC_L structure import used {} of 2000000 operations",
        clean_kernel::tc::declaration_budget_used()
    );
    // `CICL.ConstantDecl` carries one `payload` in place of the independent
    // `value`/`transparent` pair since cd59bbabd (docs/DECISIONS.md,
    // "Retain declaration origins before inductive admission").
    let fields: Vec<Name> = ["parameters", "type", "payload"]
        .into_iter()
        .map(Name::from_string)
        .collect();
    assert_eq!(
        env.get_structure_field_names(&structure),
        Some(fields.as_slice())
    );
    assert_eq!(
        structure_table_contradiction(&env, &structure, &fields, &[], false),
        None
    );

    let mut reversed = fields.clone();
    reversed.swap(0, 1);
    assert!(matches!(
        structure_table_contradiction(&env, &structure, &reversed, &[], false),
        Some(TableFault::Computes(_))
    ));
    assert!(env.forget_decl(&Name::from_string("CICL.ConstantDecl.parameters")));
    assert!(matches!(
        structure_table_contradiction(&env, &structure, &fields, &[], false),
        Some(TableFault::Absent(_))
    ));
}
