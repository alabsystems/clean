// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
//! Real nested/overlapping source through the maintained compiler pipeline.

use super::super::e2e_support::{compile_root, elaborated_env_with, o0};
use super::super::RcRepairMode;
use crate::pass_manager::{PassManager, PipelineConfig};
use crate::to_lcnf::constant_to_decl;
use clean_kernel::Name;

const SOURCE: &str = include_str!(
    "../../../tests/fixtures/advice_replay_checker/programs/c03_nested_overlapping_patterns.lean"
);

#[test]
fn nested_unary_pattern_c03_must_compile_without_rc_leak() {
    for nested in ["lit", "var", "lam", "succ"] {
        let source = SOURCE.replace(".succ (.lit _)", &format!(".succ (.{nested} _)"));
        let env = elaborated_env_with(&source);
        for pipeline in [PipelineConfig::default(), o0()] {
            let compiled = compile_root(&env, "Tm.isNormal", &pipeline, RcRepairMode::Enabled);
            if compiled.is_err() {
                // Diagnostic only: the assertion below uses the real, unchanged
                // pipeline and verifier, never this unverified intermediate output.
                let info = env
                    .get_const(&Name::from_string("Tm.isNormal"))
                    .expect("root");
                let decl = constant_to_decl(&env, info)
                    .expect("LCNF lowering")
                    .expect("computable");
                let manager =
                    PassManager::default_pipeline_with_config(&pipeline.opt, &pipeline.rc);
                let rc = manager.run_batch(&[decl], &env).expect("LCNF passes");
                for declaration in &rc {
                    eprintln!("NESTED_PATTERN_LCNF\n{declaration}");
                }
                let ir = crate::to_ir::to_ir_with_env(&rc, &env).expect("IR lowering");
                let boxed = crate::boxing::explicit_boxing_with_kernel_env(
                    &ir.decls,
                    &env,
                    &pipeline.boxing,
                );
                let repaired = super::super::rc_repair_boxed(&ir.decls, boxed, &ir.rc_unmanaged);
                eprintln!("NESTED_PATTERN_FINAL_IR\n{repaired:#?}");
            }
            compiled
                .expect("nested unary first-match patterns must compile with linear references");
        }
    }
}

#[test]
fn nested_unary_pattern_c03_executes_both_first_match_branches() {
    let source = format!(
        "{SOURCE}\n\
         def nestedCase1 : Bool := Tm.isNormal (.app (.var 0) (.lit 1))\n\
         def nestedCase2 : Bool := Tm.isNormal (.app (.lam (.var 0)) (.lit 1))\n\
         def nestedCase3 : Bool := Tm.isNormal (.lam (.succ (.lit 1)))\n\
         def nestedCase4 : Bool := Tm.isNormal (.lam (.succ (.var 1)))\n"
    );
    let env = elaborated_env_with(&source);
    let driver = r#"
int main(void) {
  printf("%u\n", (unsigned)l_nestedCase1());
  printf("%u\n", (unsigned)l_nestedCase2());
  printf("%u\n", (unsigned)l_nestedCase3());
  printf("%u\n", (unsigned)l_nestedCase4());
  return 0;
}
"#;
    for pipeline in [PipelineConfig::default(), o0()] {
        let (lines, asan) = super::end_to_end::run_emitted_c_of(
            &env,
            &["nestedCase1", "nestedCase2", "nestedCase3", "nestedCase4"],
            driver,
            &pipeline,
        );
        assert_eq!(lines, ["1", "0", "0", "1"], "wrong first-match values");
        if cfg!(target_os = "macos") {
            assert!(asan, "macOS supports the runtime's AddressSanitizer check");
        }
    }
}
