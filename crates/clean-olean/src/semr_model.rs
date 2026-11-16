// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
//! Shared completed SemR context and exact original-model comparison.
use crate::{reference_base_closed, ClosedRecheckOptions, ReferenceBase};
use clean_kernel::{Environment, Expr, Level, Name, ReferenceKernel};
use std::collections::BTreeSet;
use std::sync::OnceLock;

#[derive(Debug, thiserror::Error)]
pub enum SemrModelRefusal {
    #[error("model context lacks a genuinely completed reference replay")]
    IncompleteContext,
    #[error("model context lacks required declaration {0}")]
    MissingDeclaration(String),
    #[error("original source/model closure differs at {0}")]
    ModelSourceMismatch(String),
    #[error("cannot compare the complete original model closure: {0}")]
    ModelSourceClosure(String),
}

pub(crate) struct SemrModelContext {
    kernel: ReferenceKernel,
    roots: &'static [&'static str],
    source_reference: OnceLock<CheckedSourceReference>,
}

// Digests cache an actual completed full replay and exact comparison, never
// authenticate source or substitute for a mathematical admission.
struct CheckedSourceReference {
    input: Vec<[u8; 32]>,
    _kernel: ReferenceKernel,
}

impl SemrModelContext {
    pub(crate) fn from_reference_base(
        base: ReferenceBase,
        roots: &'static [&'static str],
        helpers: &[&str],
    ) -> Result<Self, SemrModelRefusal> {
        let kernel = base
            .into_kernel()
            .map_err(|_| SemrModelRefusal::IncompleteContext)?;
        for root in roots.iter().copied().chain(helpers.iter().copied()) {
            kernel
                .environment()
                .dependency_closure(&Name::from_string(root))
                .map_err(|_| SemrModelRefusal::MissingDeclaration(root.into()))?;
        }
        Ok(Self {
            kernel,
            roots,
            source_reference: OnceLock::new(),
        })
    }

    pub(crate) fn kernel(&self) -> &ReferenceKernel {
        &self.kernel
    }

    fn source_input(&self, original: &Environment) -> Result<Vec<[u8; 32]>, SemrModelRefusal> {
        self.roots
            .iter()
            .map(|root| {
                original
                    .closure_digest(&Name::from_string(root))
                    .map_err(|e| SemrModelRefusal::ModelSourceClosure(e.to_string()))
            })
            .collect()
    }

    pub(crate) fn check_model_source(
        &self,
        original: &Environment,
    ) -> Result<(), SemrModelRefusal> {
        let input = self.source_input(original)?;
        if let Some(cached) = self.source_reference.get() {
            return if cached.input == input {
                Ok(())
            } else {
                Err(SemrModelRefusal::ModelSourceMismatch(
                    "fixed source batch changed".into(),
                ))
            };
        }
        let roots: BTreeSet<Name> = self
            .roots
            .iter()
            .map(|root| Name::from_string(root))
            .collect();
        let base = reference_base_closed(original, &roots, &ClosedRecheckOptions::default())
            .map_err(|e| SemrModelRefusal::ModelSourceClosure(e.to_string()))?;
        let source_kernel = base
            .into_kernel()
            .map_err(|report| SemrModelRefusal::ModelSourceClosure(report.verdict_sentence()))?;
        let checked = self.kernel.environment();
        let source = source_kernel.environment();
        for root in self.roots {
            let name = Name::from_string(root);
            let left = checked
                .dependency_closure(&name)
                .map_err(|e| SemrModelRefusal::ModelSourceClosure(e.to_string()))?;
            let right = source
                .dependency_closure(&name)
                .map_err(|e| SemrModelRefusal::ModelSourceClosure(e.to_string()))?;
            if left != right {
                return Err(SemrModelRefusal::ModelSourceMismatch((*root).into()));
            }
            for member in left {
                if checked.get_const(&member) != source.get_const(&member)
                    || checked.get_inductive(&member) != source.get_inductive(&member)
                    || checked.get_constructor(&member) != source.get_constructor(&member)
                    || checked.get_recursor(&member) != source.get_recursor(&member)
                    || checked.get_quot(&member) != source.get_quot(&member)
                {
                    return Err(SemrModelRefusal::ModelSourceMismatch(member.to_string()));
                }
            }
        }
        if self.source_input(original)? != input {
            return Err(SemrModelRefusal::ModelSourceMismatch(
                "source changed during replay".into(),
            ));
        }
        let binding = CheckedSourceReference {
            input,
            _kernel: source_kernel,
        };
        match self.source_reference.set(binding) {
            Ok(()) => Ok(()),
            Err(binding)
                if self
                    .source_reference
                    .get()
                    .is_some_and(|source| source.input == binding.input) =>
            {
                Ok(())
            }
            Err(_) => Err(SemrModelRefusal::ModelSourceMismatch(
                "fixed source batch changed".into(),
            )),
        }
    }
}

pub(crate) fn c(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}
pub(crate) fn list(ty: Expr, values: Vec<Expr>) -> Expr {
    values.into_iter().rev().fold(
        Expr::app(
            Expr::const_(Name::from_string("List.nil"), vec![Level::zero()]),
            ty.clone(),
        ),
        |tail, value| {
            Expr::apps(
                Expr::const_(Name::from_string("List.cons"), vec![Level::zero()]),
                [ty.clone(), value, tail],
            )
        },
    )
}
pub(crate) fn bytes(values: &[u8]) -> Expr {
    list(
        c("Nat"),
        values
            .iter()
            .map(|value| Expr::nat_lit(u64::from(*value)))
            .collect(),
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::env::Declaration;

    fn original_source(level: Level) -> Environment {
        let mut kernel = ReferenceKernel::new(Environment::for_lean_replay()).unwrap();
        kernel
            .add_checked(Declaration::Definition {
                name: Name::from_string("ModelSourceProbe"),
                level_params: vec![],
                type_: Expr::sort(Level::succ(level.clone())),
                value: Expr::sort(level),
                is_reducible: true,
            })
            .unwrap();
        kernel.environment().clone()
    }

    #[test]
    fn exact_source_comparison_reuses_completion_and_refuses_changed_source() {
        const ROOTS: &[&str] = &["ModelSourceProbe"];
        let original = original_source(Level::zero());
        let roots = BTreeSet::from([Name::from_string(ROOTS[0])]);
        let base =
            reference_base_closed(&original, &roots, &ClosedRecheckOptions::default()).unwrap();
        let context = SemrModelContext::from_reference_base(base, ROOTS, &[]).unwrap();
        context.check_model_source(&original).unwrap();
        context.check_model_source(&original).unwrap();
        let changed = original_source(Level::succ(Level::zero()));
        assert!(matches!(
            context.check_model_source(&changed),
            Err(SemrModelRefusal::ModelSourceMismatch(_))
        ));
        context.check_model_source(&original).unwrap();
        let changed_base =
            reference_base_closed(&changed, &roots, &ClosedRecheckOptions::default()).unwrap();
        let changed_context =
            SemrModelContext::from_reference_base(changed_base, ROOTS, &[]).unwrap();
        assert!(matches!(
            changed_context.check_model_source(&original),
            Err(SemrModelRefusal::ModelSourceMismatch(_))
        ));
    }
}
