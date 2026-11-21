// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Adapt the borrowed Nat comparison used by the 4.36 Unicode scalar decision.
use super::stable_bitvec::{from_prelude, scalar_family};
use clean_kernel::env::{CompilerExternArity, CompilerExternEntry, CompilerExternMetadata};
use clean_kernel::{
    BinderInfo, ConstantInfo, ConstantKind, Environment, Expr, LeanWorld, Level, MDataValue, Name,
};

fn decidable_layout(env: &Environment) -> bool {
    let proposition = Expr::prop();
    let reflect = Expr::apps(
        Expr::const_str("Bool.Reflects"),
        [Expr::bvar(0), Expr::bvar(1)],
    );
    let constructor_ty = Expr::pi(
        BinderInfo::Implicit,
        proposition,
        Expr::arrow(
            Expr::const_str("Bool"),
            Expr::arrow(
                reflect,
                Expr::app(Expr::const_str("Decidable"), Expr::bvar(2)),
            ),
        ),
    );
    [
        "Decidable",
        "Decidable.intro",
        "Decidable.decide",
        "Bool.Reflects",
    ]
    .iter()
    .all(|name| from_prelude(env, &Name::from_string(name)))
        && env
            .get_constructor(&Name::from_string("Decidable.intro"))
            .is_some_and(|ctor| {
                ctor.inductive_name == Name::from_string("Decidable")
                    && ctor.constructor_idx == 0
                    && ctor.num_params == 1
                    && ctor.num_fields == 2
                    && ctor.type_ == constructor_ty
            })
        && clean_compiler::to_lcnf::decidable_projects_bool(env)
}

pub(super) fn select(env: &Environment, info: &ConstantInfo) -> anyhow::Result<bool> {
    let name = &info.name;
    if *name != Name::interned("Nat.decLt")
        || clean_olean::environment_world(env) != Some(LeanWorld::Lean436.tag())
    {
        return Ok(false);
    }
    let nat = Expr::const_str("Nat");
    let boolean = Expr::const_str("Bool");
    let borrowed = Expr::mdata(
        vec![(Name::interned("borrowed"), MDataValue::Bool(true))],
        nat.clone(),
    );
    let less = Expr::apps(
        Expr::const_(Name::interned("LT.lt"), vec![Level::zero()]),
        [
            borrowed.clone(),
            Expr::const_str("instLTNat"),
            Expr::bvar(1),
            Expr::bvar(0),
        ],
    );
    let result = Expr::app(Expr::const_str("Decidable"), less);
    anyhow::ensure!(
        from_prelude(env, name)
            && decidable_layout(env)
            && scalar_family(
                env,
                "Nat",
                true,
                [
                    ("zero", 0, nat.clone()),
                    ("succ", 1, Expr::arrow(nat.clone(), nat))
                ]
            )
            && scalar_family(
                env,
                "Bool",
                false,
                [("false", 0, boolean.clone()), ("true", 0, boolean)]
            )
            && info.kind == ConstantKind::Definition
            && info.level_params.is_empty()
            && info.type_ == Expr::arrow(borrowed.clone(), Expr::arrow(borrowed, result))
            && !env.is_unsafe(name)
            && !env.is_partial(name)
            && !env.is_noncomputable(name)
            && env.get_implemented_by(name).is_none(),
        "stable {name} requires its SDK borrowed telescope and Bool-backed decision"
    );
    let Some(CompilerExternMetadata::Complete(descriptor)) = env.extern_metadata(name)? else {
        anyhow::bail!("stable {name} requires complete compiler extern metadata");
    };
    anyhow::ensure!(
        descriptor.arity == CompilerExternArity::Unspecified
            && matches!(descriptor.entries.as_slice(), [CompilerExternEntry::Standard { backend, symbol }]
            if *backend == Name::interned("all") && symbol == "lean_nat_dec_lt"),
        "stable {name} requires the original lean_nat_dec_lt binding"
    );
    Ok(true)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::PathBuf;

    #[test]
    #[ignore = "requires the official 4.36.0 SDK in CLEAN_LEAN436_LIB"]
    fn require_the_original_borrowed_nat_decision() {
        let lib = PathBuf::from(std::env::var_os("CLEAN_LEAN436_LIB").unwrap());
        let mut env = Environment::for_lean_replay();
        clean_olean::declare_environment_world(&mut env, LeanWorld::Lean436.tag()).unwrap();
        clean_olean::load_module_with_deps(&mut env, "Init.Prelude", &[lib]).unwrap();
        let name = Name::interned("Nat.decLt");
        let info = env.get_const(&name).unwrap().clone();
        assert!(select(&env, &info).unwrap());

        let mut incorrect_telescope = info.clone();
        incorrect_telescope.type_ = Expr::arrow(Expr::const_str("Nat"), Expr::const_str("Bool"));
        assert!(select(&env, &incorrect_telescope).is_err());

        env.register_extern(name, "lean_nat_dec_le".into());
        assert!(select(&env, &info).is_err());
    }
}
