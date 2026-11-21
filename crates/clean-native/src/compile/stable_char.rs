// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The original stable SDK conversion whose second source parameter proves scalar validity.

use crate::native_ffi_audit::checked_char_carrier;
use clean_kernel::env::{CompilerExternArity, CompilerExternEntry, CompilerExternMetadata};
use clean_kernel::{ConstantInfo, ConstantKind, Environment, Expr, LeanWorld, MDataValue, Name};

pub(crate) struct CharFromValidNat(());

impl CharFromValidNat {
    pub(crate) fn definition(self) -> &'static str {
        concat!(
            "#include \"clean_runtime.h\"\n",
            "clean_obj* l_Char_ofNatAux(clean_obj* n, clean_obj* proof) {\n",
            "    return clean_char_from_valid_nat_owned(n, proof);\n",
            "}\n",
        )
    }

    pub(crate) fn select(env: &Environment, info: &ConstantInfo) -> anyhow::Result<Option<Self>> {
        let name = &info.name;
        if name != &Name::from_string("Char.ofNatAux")
            || clean_olean::environment_world(env) != Some(LeanWorld::Lean436.tag())
        {
            return Ok(None);
        }
        let predicate = Name::from_string("Nat.isValidChar");
        let nat = Expr::const_str("Nat");
        let sdk = |n: &Name| {
            clean_olean::import::lean_declaration_artifact(env, n).as_deref()
                == Some("Init.Prelude")
        };
        anyhow::ensure!(
            sdk(name)
                && sdk(&predicate)
                && sdk(&Name::from_string("Nat"))
                && env
                    .get_const(&predicate)
                    .is_some_and(|p| p.kind == ConstantKind::Definition
                        && p.level_params.is_empty()
                        && p.type_ == Expr::arrow(nat.clone(), Expr::prop())),
            "stable Char.ofNatAux requires its original Nat.isValidChar source predicate"
        );
        let borrowed = Expr::mdata(
            vec![(Name::from_string("borrowed"), MDataValue::Bool(true))],
            nat,
        );
        let scalar = checked_char_carrier(env, name)?;
        let expected = Expr::arrow(
            borrowed,
            Expr::arrow(
                Expr::app(Expr::const_(predicate, vec![]), Expr::bvar(0)),
                scalar,
            ),
        );
        anyhow::ensure!(
            info.kind == ConstantKind::Definition
                && info.level_params.is_empty()
                && info.type_ == expected
                && !env.is_unsafe(name)
                && !env.is_partial(name)
                && !env.is_noncomputable(name)
                && env.get_implemented_by(name).is_none(),
            "stable Char.ofNatAux requires its borrowed Nat, erased validity proof and Char result"
        );
        let Some(CompilerExternMetadata::Complete(binding)) = env.extern_metadata(name)? else {
            anyhow::bail!("stable Char.ofNatAux requires complete compiler extern metadata");
        };
        anyhow::ensure!(
            binding.arity == CompilerExternArity::Unspecified
                && matches!(binding.entries.as_slice(), [CompilerExternEntry::Standard {backend,symbol}]
                    if backend == &Name::from_string("all") && symbol == "lean_uint32_of_nat"),
            "stable Char.ofNatAux requires the original lean_uint32_of_nat binding"
        );
        Ok(Some(Self(())))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    #[ignore = "requires the original Lean 4.36 SDK in CLEAN_LEAN436_LIB"]
    fn original_char_extern_preserves_the_predicate_and_borrowed_nat() {
        let lib = std::path::PathBuf::from(std::env::var_os("CLEAN_LEAN436_LIB").unwrap());
        let mut env = Environment::new();
        clean_olean::declare_environment_world(&mut env, LeanWorld::Lean436.tag()).unwrap();
        clean_olean::load_module_with_deps(&mut env, "Init.Prelude", &[lib]).unwrap();
        let name = Name::from_string("Char.ofNatAux");
        let info = env.get_const(&name).unwrap();
        assert!(CharFromValidNat::select(&env, info).unwrap().is_some());
        let mut wrong = info.clone();
        wrong.type_ = Expr::arrow(
            Expr::const_str("Nat"),
            Expr::arrow(
                Expr::app(Expr::const_str("Nat.isValidChar"), Expr::bvar(0)),
                Expr::const_str("Char"),
            ),
        );
        assert!(CharFromValidNat::select(&env, &wrong).is_err());
        for owner in ["Nat.isValidChar", "Char.mk", "UInt32.isValidChar"] {
            let mut foreign = env.clone();
            assert!(foreign.set_constant_origin(
                Name::from_string(owner),
                clean_kernel::env::ConstantOrigin::olean_import(Some("Foreign".into())),
            ));
            assert!(CharFromValidNat::select(&foreign, info).is_err());
        }
        let mut changed = env.clone();
        changed
            .register_extern_metadata(
                name,
                env.extern_metadata(&Name::from_string("UInt32.toNat"))
                    .unwrap()
                    .unwrap(),
            )
            .unwrap();
        assert!(CharFromValidNat::select(&changed, info).is_err());
    }

    #[test]
    fn untyped_c_calls_cannot_select_char_of_nat_aux() {
        let call =
            "clean_obj* l_convert(clean_obj* x) {\n return l_Char_ofNatAux(x, clean_box(0));\n}";
        let refusal = crate::native_build::select_shims_for_c_text(call).unwrap_err();
        assert!(refusal.to_string().contains("l_Char_ofNatAux"));
    }
}
