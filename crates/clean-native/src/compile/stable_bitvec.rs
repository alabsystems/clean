// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Lean 4.36's owned, proof-erased BitVec 32 constructor input.

use clean_kernel::env::{CompilerExternArity, CompilerExternEntry, CompilerExternMetadata};
use clean_kernel::{
    BinderInfo, ConstantInfo, ConstantKind, Environment, Expr, LeanWorld, Level, Name,
};

pub(crate) struct BitVec32(());

impl BitVec32 {
    pub(crate) fn definition(self) -> &'static str {
        include_str!("uint32_of_bitvec.c")
    }

    pub(crate) fn select(env: &Environment, info: &ConstantInfo) -> anyhow::Result<Option<Self>> {
        let name = &info.name;
        if name != &Name::from_string("UInt32.ofBitVec")
            || clean_olean::environment_world(env) != Some(LeanWorld::Lean436.tag())
        {
            return Ok(None);
        }
        let nat = Expr::const_str("Nat");
        anyhow::ensure!(
            scalar_family(
                env,
                "Nat",
                true,
                [
                    ("zero", 0, nat.clone()),
                    ("succ", 1, Expr::arrow(nat.clone(), nat))
                ]
            ) && info.kind == ConstantKind::Definition
                && info.value.is_none()
                && info.level_params.is_empty()
                && info.type_ == uint32_bitvec_type(env)?
                && !env.is_unsafe(name)
                && !env.is_partial(name)
                && !env.is_noncomputable(name)
                && env.get_implemented_by(name).is_none(),
            "stable UInt32.ofBitVec requires its SDK constructor and owned BitVec 32 carrier"
        );
        let Some(CompilerExternMetadata::Complete(binding)) = env.extern_metadata(name)? else {
            anyhow::bail!("stable UInt32.ofBitVec requires complete compiler extern metadata");
        };
        anyhow::ensure!(
            binding.arity == CompilerExternArity::Unspecified
                && matches!(binding.entries.as_slice(), [CompilerExternEntry::Standard { backend, symbol }]
                    if backend == &Name::from_string("all") && symbol == "lean_uint32_of_nat_mk"),
            "stable UInt32.ofBitVec requires precisely the all-backend lean_uint32_of_nat_mk binding"
        );
        Ok(Some(Self(())))
    }
}

pub(super) fn from_prelude(env: &Environment, name: &Name) -> bool {
    clean_olean::import::lean_declaration_artifact(env, name).as_deref() == Some("Init.Prelude")
}

pub(super) fn scalar_family<const N: usize>(
    env: &Environment,
    name: &str,
    recursive: bool,
    roles: [(&str, u32, Expr); N],
) -> bool {
    let name = Name::from_string(name);
    let constructors = roles.each_ref().map(|(ctor, _, _)| name.clone().str(*ctor));
    from_prelude(env, &name)
        && env.get_inductive(&name).is_some_and(|family| {
            family.is_recursive == recursive
                && family.level_params.is_empty()
                && family.num_params == 0
                && family.num_indices == 0
                && family.type_ == Expr::type_()
                && family.constructor_names.as_slice() == constructors
        })
        && roles
            .into_iter()
            .enumerate()
            .all(|(index, (_, fields, ty))| {
                let ctor = &constructors[index];
                from_prelude(env, ctor)
                    && env.get_constructor(ctor).is_some_and(|c| {
                        c.name == *ctor
                            && c.inductive_name == name
                            && c.level_params.is_empty()
                            && c.constructor_idx as usize == index
                            && c.num_params == 0
                            && c.num_fields == fields
                            && c.type_ == ty
                    })
            })
}

fn sdk_nat_literal(value: u64) -> Expr {
    let n = Expr::nat_lit(value);
    Expr::apps(
        Expr::const_(Name::from_string("OfNat.ofNat"), vec![Level::zero()]),
        [
            Expr::const_str("Nat"),
            n.clone(),
            Expr::app(Expr::const_str("instOfNatNat"), n),
        ],
    )
}

fn sdk_power_of_two(exponent: Expr) -> Expr {
    let nat = Expr::const_str("Nat");
    let zero = Level::zero();
    let pow = Expr::apps(
        Expr::const_(Name::from_string("instPowNat"), vec![zero.clone()]),
        [nat.clone(), Expr::const_str("instNatPowNat")],
    );
    let hpow = Expr::apps(
        Expr::const_(Name::from_string("instHPow"), vec![zero.clone(); 2]),
        [nat.clone(), nat.clone(), pow],
    );
    Expr::apps(
        Expr::const_(Name::from_string("HPow.hPow"), vec![zero; 3]),
        [
            nat.clone(),
            nat.clone(),
            nat,
            hpow,
            sdk_nat_literal(2),
            exponent,
        ],
    )
}

fn uint32_bitvec_type(env: &Environment) -> anyhow::Result<Expr> {
    let nat = Expr::const_str("Nat");
    let family_at = |family, index| Expr::app(Expr::const_str(family), Expr::bvar(index));
    let fin_bound = Expr::apps(
        Expr::const_(Name::from_string("LT.lt"), vec![Level::zero()]),
        [
            nat.clone(),
            Expr::const_str("instLTNat"),
            Expr::bvar(0),
            Expr::bvar(1),
        ],
    );
    let fin_fields = Expr::arrow(nat.clone(), Expr::arrow(fin_bound, family_at("Fin", 2)));
    let bv_field = Expr::app(Expr::const_str("Fin"), sdk_power_of_two(Expr::bvar(0)));
    let bv_fields = Expr::arrow(bv_field, family_at("BitVec", 1));

    // The boxed adapter receives the unsigned value itself only if the compiler
    // represents both the indexed Fin and the enclosing BitVec by their first field.
    for (family, constructor, fields, telescope) in [
        ("Fin", "Fin.mk", 2, fin_fields),
        ("BitVec", "BitVec.ofFin", 1, bv_fields),
    ] {
        let family = Name::from_string(family);
        let ctor = Name::from_string(constructor);
        let ctor_type = Expr::pi(BinderInfo::Implicit, nat.clone(), telescope);
        anyhow::ensure!(
            from_prelude(env, &family)
                && from_prelude(env, &ctor)
                && env.get_inductive(&family).is_some_and(|f| !f.is_recursive
                    && f.level_params.is_empty()
                    && f.num_params == 1
                    && f.num_indices == 0
                    && f.type_ == Expr::arrow(nat.clone(), Expr::type_())
                    && f.constructor_names.as_slice() == [ctor.clone()])
                && env
                    .get_constructor(&ctor)
                    .is_some_and(|c| c.inductive_name == family
                        && c.level_params.is_empty()
                        && c.constructor_idx == 0
                        && c.num_params == 1
                        && c.num_fields == fields
                        && c.type_ == ctor_type)
                && clean_compiler::to_mono::has_trivial_structure(&family, env).is_some_and(|r| r
                    .ctor_name
                    == ctor
                    && r.num_params == 1
                    && r.field_idx == 0),
            "stable UInt32.ofBitVec requires the SDK {family} bound and erased carrier"
        );
    }
    let ty = Expr::arrow(
        Expr::app(Expr::const_str("BitVec"), sdk_nat_literal(32)),
        Expr::const_str("UInt32"),
    );
    anyhow::ensure!(
        scalar_family(env, "UInt32", false, [("ofBitVec", 1, ty.clone())]),
        "stable UInt32.ofBitVec requires the SDK 32-bit constructor"
    );
    Ok(ty)
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_compiler::emit_c::CEmitConfig;
    use clean_compiler::pass_manager::{compile_lcnf_decls_in_runtime_closure, PipelineConfig};
    use clean_kernel::env::ConstantOrigin;
    use std::path::PathBuf;

    #[test]
    #[ignore = "requires the official Lean 4.36.0 SDK through CLEAN_LEAN436_LIB"]
    fn bitvec_conversion_checks_the_width_proof_and_executable_constructor() {
        let lib = PathBuf::from(std::env::var_os("CLEAN_LEAN436_LIB").expect("official SDK"));
        let mut env = Environment::new();
        clean_olean::declare_environment_world(&mut env, LeanWorld::Lean436.tag()).unwrap();
        clean_olean::load_module_with_deps(&mut env, "Init.Prelude", &[lib]).unwrap();
        let name = Name::from_string("UInt32.ofBitVec");
        let info = env.get_const(&name).unwrap();
        assert!(BitVec32::select(&env, info).unwrap().is_some());
        let mut wrong = info.clone();
        wrong.type_ = Expr::arrow(
            Expr::app(Expr::const_str("BitVec"), sdk_nat_literal(64)),
            Expr::const_str("UInt32"),
        );
        assert!(BitVec32::select(&env, &wrong).is_err());
        for role in ["Fin.mk", "BitVec.ofFin", "UInt32"] {
            let mut foreign = env.clone();
            assert!(foreign.set_constant_origin(
                Name::from_string(role),
                ConstantOrigin::olean_import(Some("Foreign".into()))
            ));
            assert!(BitVec32::select(&foreign, info).is_err());
        }
        let mut swapped = env.clone();
        swapped
            .register_extern_metadata(
                name,
                env.extern_metadata(&Name::from_string("UInt32.toNat"))
                    .unwrap()
                    .unwrap(),
            )
            .unwrap();
        assert!(BitVec32::select(&swapped, info).is_err());

        let root = Name::from_string("convertStableBits");
        let bits = Expr::app(Expr::const_str("BitVec"), sdk_nat_literal(32));
        env.add_decl(clean_kernel::Declaration::Definition {
            name: root.clone(),
            level_params: vec![],
            type_: Expr::arrow(bits.clone(), Expr::const_str("UInt32")),
            value: Expr::lam(
                BinderInfo::Default,
                bits,
                Expr::app(Expr::const_str("UInt32.ofBitVec"), Expr::bvar(0)),
            ),
            is_reducible: false,
        })
        .unwrap();
        let closure = clean_compiler::RuntimeBindingClosure::check_executable(
            &env,
            std::slice::from_ref(&root),
        )
        .unwrap();
        let declaration = clean_compiler::constant_to_decl_in_runtime_closure(
            &env,
            env.get_const(&root).unwrap(),
            &closure,
        )
        .unwrap()
        .unwrap();
        let generated = compile_lcnf_decls_in_runtime_closure(
            &[declaration],
            &env,
            &PipelineConfig::default(),
            &closure,
        )
        .unwrap()
        .emit_c(CEmitConfig {
            check_ir: true,
            ..Default::default()
        })
        .unwrap();
        assert!(generated.contains(" = l_UInt32_ofBitVec("), "{generated}");
        assert!(generated.contains(" = clean_unbox_uint32("), "{generated}");
    }

    #[test]
    fn untyped_c_text_does_not_select_the_stable_constructor() {
        let code = "clean_obj* l_UInt32_ofBitVec(clean_obj* bits);\nclean_obj* l_convert(clean_obj* n) {\n return l_UInt32_ofBitVec(n);\n}";
        let err = crate::native_build::select_shims_for_c_text(code).unwrap_err();
        assert!(err.to_string().contains("l_UInt32_ofBitVec"), "{err}");
    }
}
