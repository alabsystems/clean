// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Select Lean 4.36's state-token constructor from its imported binding.

use clean_kernel::env::{CompilerExternArity, CompilerExternEntry, CompilerExternMetadata};
use clean_kernel::{BinderInfo, ConstantInfo, ConstantKind, Environment, Expr, LeanWorld, Name};

/// The native selection walk reached the measured stable SDK operation.
pub(crate) struct VoidMk(());

impl VoidMk {
    pub(crate) fn definition(self) -> &'static str {
        include_str!("void_mk.c")
    }

    pub(crate) fn select(env: &Environment, info: &ConstantInfo) -> anyhow::Result<Option<Self>> {
        let name = &info.name;
        if name != &Name::from_string("Void.mk")
            || clean_olean::environment_world(env) != Some(LeanWorld::Lean436.tag())
        {
            return Ok(None);
        }
        let expected = Expr::pi(
            BinderInfo::Implicit,
            Expr::type_(),
            Expr::pi(
                BinderInfo::Default,
                Expr::bvar(0),
                Expr::app(Expr::const_str("Void"), Expr::bvar(1)),
            ),
        );
        anyhow::ensure!(
            clean_olean::import::lean_declaration_artifact(env, name).as_deref()
                == Some("Init.System.ST")
                && clean_olean::import::lean_declaration_artifact(env, &Name::from_string("Void"))
                    .as_deref()
                    == Some("Init.System.ST")
                // Stable's public .olean exports this opaque as an axiom. The
                // implementation part restores its opaque declaration.
                && (info.kind == ConstantKind::Opaque
                    || (info.kind == ConstantKind::Axiom && info.value.is_none()))
                && info.level_params.is_empty()
                && info.type_ == expected
                && !env.is_unsafe(name)
                && !env.is_partial(name)
                && !env.is_noncomputable(name)
                && env.get_implemented_by(name).is_none(),
            "stable Void.mk requires the Init.System.ST opaque and its owned parameter"
        );
        let Some(CompilerExternMetadata::Complete(binding)) = env.extern_metadata(name)? else {
            anyhow::bail!("stable Void.mk requires its SDK extern metadata");
        };
        anyhow::ensure!(
            binding.arity == CompilerExternArity::Unspecified
                && matches!(binding.entries.as_slice(), [CompilerExternEntry::Standard { backend, symbol }]
                    if backend == &Name::from_string("all") && symbol == "lean_void_mk"),
            "stable Void.mk requires precisely the all-backend lean_void_mk binding"
        );
        Ok(Some(Self(())))
    }
}
