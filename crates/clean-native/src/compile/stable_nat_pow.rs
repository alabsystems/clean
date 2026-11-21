// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::stable_bitvec::{from_prelude, scalar_family};
use clean_kernel::env::{CompilerExternArity, CompilerExternEntry, CompilerExternMetadata};
use clean_kernel::{ConstantInfo, ConstantKind, Environment, Expr, LeanWorld, MDataValue, Name};

/// Admit the selected stable SDK binding before adapting its two borrowed
/// inputs to the Clean compiler's owned call convention.
pub(super) fn select(env: &Environment, info: &ConstantInfo) -> anyhow::Result<bool> {
    let name = &info.name;
    if *name != Name::interned("Nat.pow")
        || clean_olean::environment_world(env) != Some(LeanWorld::Lean436.tag())
    {
        return Ok(false);
    }
    let nat = Expr::const_str("Nat");
    let borrowed = Expr::mdata(
        vec![(Name::interned("borrowed"), MDataValue::Bool(true))],
        nat.clone(),
    );
    anyhow::ensure!(
        from_prelude(env, name)
            && scalar_family(
                env,
                "Nat",
                true,
                [
                    ("zero", 0, nat.clone()),
                    ("succ", 1, Expr::arrow(nat.clone(), nat.clone())),
                ]
            )
            && info.kind == ConstantKind::Definition
            && info.level_params.is_empty()
            && info.type_ == Expr::arrow(borrowed.clone(), Expr::arrow(borrowed, nat))
            && !env.is_unsafe(name)
            && !env.is_partial(name)
            && !env.is_noncomputable(name)
            && env.get_implemented_by(name).is_none(),
        "stable Nat.pow requires its SDK borrowed Nat telescope"
    );
    let Some(CompilerExternMetadata::Complete(binding)) = env.extern_metadata(name)? else {
        anyhow::bail!("stable Nat.pow requires complete compiler extern metadata");
    };
    anyhow::ensure!(
        binding.arity == CompilerExternArity::Unspecified
            && matches!(binding.entries.as_slice(), [CompilerExternEntry::Standard { backend, symbol }]
                if *backend == Name::interned("all") && symbol == "lean_nat_pow"),
        "stable Nat.pow requires the original lean_nat_pow extern"
    );
    Ok(true)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::PathBuf;

    #[test]
    #[ignore = "requires the official 4.36.0 SDK in CLEAN_LEAN436_LIB"]
    fn admit_the_original_borrowed_nat_power() {
        let lib = PathBuf::from(std::env::var_os("CLEAN_LEAN436_LIB").unwrap());
        let mut env = Environment::for_lean_replay();
        clean_olean::declare_environment_world(&mut env, LeanWorld::Lean436.tag()).unwrap();
        clean_olean::load_module_with_deps(&mut env, "Init.Prelude", &[lib]).unwrap();
        let name = Name::interned("Nat.pow");
        let info = env.get_const(&name).unwrap().clone();
        assert!(select(&env, &info).unwrap());

        let mut unborrowed = info.clone();
        let nat = Expr::const_str("Nat");
        unborrowed.type_ = Expr::arrow(nat.clone(), Expr::arrow(nat.clone(), nat));
        assert!(select(&env, &unborrowed).is_err());

        env.register_extern(name, "lean_nat_mul".to_owned());
        assert!(select(&env, &info).is_err());
    }
}
