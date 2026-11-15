// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Actual emitted U32 wrapper choreography, checked without granting a license.

use clean_kernel::{Declaration, Environment, Name};
use trust_ir::Module;

use crate::emit_trust_ir::{names::wire_name, TrustIrError};
use crate::ir::{IRDecl, IRType};
use crate::mangle::{mangle_boxed_name, mangle_name};

fn check_conditional_lemma(env: &Environment, theorem: &Declaration) -> Result<(), TrustIrError> {
    let Declaration::Theorem { type_, value, .. } = theorem else {
        return Err(TrustIrError::Unsupported(
            "boxed-entry composition requires a theorem judgment".to_string(),
        ));
    };
    // Check the actual judgment, including strict dependency provenance. An
    // import mode can accept add_decl while parking its proof as an axiom;
    // neither that success nor a name-based axiom scan checks this term.
    let audit = env.audit_certification(type_, value);
    if !audit.is_certified() {
        return Err(TrustIrError::Unsupported(format!(
            "boxed-entry conditional theorem: {:?}",
            audit.issues,
        )));
    }
    Ok(())
}

/// Called on the actual canonical pipeline output, before its TV mint. This
/// component detects incorrect wrapper lowering while the runtime, target ABI
/// and independent pointer-fragment evidence are still missing. It never
/// changes the denominator, obligations, certificates or codegen gates.
pub(crate) fn check_generated_uint32_entries(
    module: &Module,
    originals: &[IRDecl],
) -> Result<(), TrustIrError> {
    let mut theorem_env = None;
    for decl in originals {
        if decl.params.is_empty()
            || decl.params.len() > clean_reflect::boxed_entry::MAX_UINT32_BOXED_ENTRY_ARGS
            || decl.return_type != IRType::UInt32
            || decl.params.iter().any(|(_, ty)| *ty != IRType::UInt32)
        {
            continue;
        }
        let scalar_name = wire_name(&decl.name);
        let boxed_name = wire_name(&Name::from_string(&mangle_boxed_name(&mangle_name(
            &decl.name,
        ))));
        // A native primitive or imported declaration may have no local body.
        // A pipeline with wrapper generation off has no such helper. None is
        // invented here, nor is a missing/bodyless function licensed.
        let Some(callee) = module
            .functions
            .iter()
            .find(|f| f.name == scalar_name && !f.is_declaration())
        else {
            continue;
        };
        let Some(wrapper) = module
            .functions
            .iter()
            .find(|f| f.name == boxed_name && !f.is_declaration())
        else {
            continue;
        };
        let shape =
            clean_reflect::boxed_entry::check_uint32_boxed_entry(module, wrapper.id, callee.id)
                .map_err(|e| TrustIrError::Unsupported(e.to_string()))?;
        // Check the conditional COMPOSITION lemma, not the runtime premise.
        // The scalar function and both box carriers are universally quantified;
        // decode(encode y)=y remains an explicit hypothesis. This theorem is
        // deliberately absent from the module's certificate/license surface.
        if theorem_env.is_none() {
            theorem_env = Some(Environment::try_with_prelude().map_err(|e| {
                TrustIrError::Unsupported(format!("boxed-entry theorem environment: {e:?}"))
            })?);
        }
        let env = theorem_env.as_ref().ok_or_else(|| {
            TrustIrError::Unsupported("missing boxed-entry theorem environment".to_string())
        })?;
        let theorem =
            Name::from_string("CleanBoxedEntry.composition").num(wrapper.id.index() as u64);
        check_conditional_lemma(env, &shape.conditional_composition_theorem(theorem))?;
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::emit_trust_ir::{emit_trust_ir_with_config, RuntimeLowering, TrustIrConfig};
    use crate::ir::{IRArg, IRBody, VarId};
    use trust_ir::inst::Inst;

    #[test]
    fn boxed_entry_conditional_check_never_treats_axiom_only_admission_as_proof() {
        use clean_kernel::{set_mm_axiom_only, Expr, Level, MmAxiomOnlyGuard};
        let env = Environment::with_prelude();
        let level = vec![Level::succ(Level::zero())];
        let bad = Declaration::Theorem {
            name: Name::from_string("BoxedEntry.badConditional"),
            level_params: vec![],
            type_: Expr::apps(
                Expr::const_(Name::from_string("Eq"), level.clone()),
                [
                    Expr::const_str("Nat"),
                    Expr::nat_lit(0u64),
                    Expr::nat_lit(1u64),
                ],
            ),
            value: Expr::apps(
                Expr::const_(Name::from_string("Eq.refl"), level),
                [Expr::const_str("Nat"), Expr::nat_lit(0u64)],
            ),
        };
        for axiom_only in [false, true] {
            let _guard = MmAxiomOnlyGuard::enter();
            set_mm_axiom_only(axiom_only);
            let error = check_conditional_lemma(&env, &bad).expect_err(
                "the production checker must reject the actual false judgment in either mode",
            );
            assert!(error.to_string().contains("TypeMismatch"), "{error:?}");
        }
    }

    fn emitted() -> (IRDecl, Module) {
        let scalar = IRDecl {
            name: Name::from_string("entrySubject"),
            params: vec![(VarId(0), IRType::UInt32), (VarId(1), IRType::UInt32)],
            return_type: IRType::UInt32,
            body: IRBody::Ret(IRArg::Var(VarId(0))),
        };
        let boxed = super::super::mk_boxed_version(&scalar);
        let module = emit_trust_ir_with_config(
            &[scalar.clone(), boxed],
            &TrustIrConfig {
                runtime_lowering: RuntimeLowering::ExternCalls,
                ..Default::default()
            },
        )
        .expect("the actual wrapper generator and actual backend");
        (scalar, module)
    }

    #[test]
    fn boxed_entry_pipeline_check_reads_actual_emission_without_minting_authority() {
        let (scalar, module) = emitted();
        let before = module.clone();
        check_generated_uint32_entries(&module, &[scalar]).expect("actual U32 wrapper");
        assert_eq!(
            module, before,
            "the checker cannot mint a wrapper license or certificate"
        );
    }

    #[test]
    fn boxed_entry_pipeline_check_refuses_wrong_lowered_ownership_and_argument_order() {
        for mutation in 0..2 {
            let (scalar, mut module) = emitted();
            let function = module
                .functions
                .iter_mut()
                .find(|f| f.name == "l_entrySubject___boxed")
                .expect("actual generated wrapper");
            let body = &mut function.blocks[0].body;
            if mutation == 0 {
                let release = body
                    .iter()
                    .position(|n| matches!(n.inst, Inst::Release { .. }))
                    .expect("the generated wrapper consumes its input");
                body.remove(release);
            } else {
                let call = &mut body[4];
                let Inst::Call { args, .. } = &mut call.inst else {
                    panic!("actual scalar call")
                };
                args.swap(0, 1);
            }
            check_generated_uint32_entries(&module, &[scalar])
                .expect_err("the production checker refuses an incorrect emitted wrapper");
        }
    }
}
