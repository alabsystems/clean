// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Read-only declaration validation for the check RPC.

use super::helpers::format_expr;
use clean_elab::{DerivedInstance, ElabResult};
use clean_kernel::env::TrustedEnvExt;
use clean_kernel::{
    Constructor, Declaration, Environment, InductiveDecl, InductiveType, TypeChecker,
};
use std::collections::HashSet;

/// Classes whose *derived* instances are best-effort: a kernel-check failure on
/// the auto-generated instance is downgraded to a skip rather than failing the
/// parent type declaration during read-only validation.
///
/// `Repr` / `Hashable` / `ToString` are pretty-printing / hashing conveniences
/// that are never consumed in proofs at this milestone. Their derive handlers
/// can emit terms referencing not-yet-bootstrapped constants (`Std.Format`) or
/// mis-leveled recursors; before these classes were bootstrapped into the
/// prelude (Task NN) the derives were silently skipped, so a rejected derived
/// instance must keep the parent type alive — exactly the prior behaviour.
///
/// This does NOT weaken the kernel check: the rejected instance is still fully
/// type-checked here (`add_decl` runs the kernel) and is simply not registered
/// into the overlay on failure. We only decline to propagate that failure.
fn is_best_effort_derived_class(class_name: &clean_kernel::Name) -> bool {
    matches!(
        class_name.to_string().as_str(),
        "Repr" | "Hashable" | "ToString"
    )
}

pub fn validate_decl_read_only(
    env: &Environment,
    tc: &TypeChecker<'_>,
    decl: &ElabResult,
) -> Result<Option<String>, String> {
    let inferred_type = decl.declaration_type().map(format_expr);

    match decl {
        ElabResult::Definition { ty, val, .. } | ElabResult::Instance { ty, val, .. } => {
            let _ = tc
                .infer_sort(ty)
                .map_err(|e| format!("Type check error: {e}"))?;
            tc.check_type(val, ty)
                .map_err(|e| format!("Type check error: {e}"))?;
        }
        // An `example` is an anonymous, discarded definition (B02; lean4
        // `src/Lean/Elab/Declaration.lean`, `elabExample`): re-check its value
        // against its type exactly like a `Definition`. The type may live in
        // any sort (`example : Nat := 3` is legal), so no Prop restriction.
        ElabResult::Example { ty, val } => {
            let _ = tc
                .infer_sort(ty)
                .map_err(|e| format!("Type check error: {e}"))?;
            tc.check_type(val, ty)
                .map_err(|e| format!("Type check error: {e}"))?;
        }
        ElabResult::Theorem { ty, proof, .. } => {
            let sort = tc
                .infer_sort(ty)
                .map_err(|e| format!("Type check error: {e}"))?;
            if !sort.is_zero() {
                let theorem_name = decl
                    .declaration_name()
                    .map(|name| name.to_string())
                    .unwrap_or_else(|| "<anonymous>".to_string());
                return Err(format!(
                    "Type check error: Theorem {theorem_name}: type must be a Prop, but inferred sort is {sort:?}"
                ));
            }
            tc.check_type(proof, ty)
                .map_err(|e| format!("Type check error: {e}"))?;
        }
        ElabResult::Axiom { ty, .. } | ElabResult::Opaque { ty, val: None, .. } => {
            let _ = tc
                .infer_sort(ty)
                .map_err(|e| format!("Type check error: {e}"))?;
        }
        ElabResult::Opaque {
            ty, val: Some(val), ..
        } => {
            let _ = tc
                .infer_sort(ty)
                .map_err(|e| format!("Type check error: {e}"))?;
            tc.check_type(val, ty)
                .map_err(|e| format!("Type check error: {e}"))?;
        }
        ElabResult::Inductive {
            name,
            universe_params,
            num_params,
            ty,
            constructors,
            derived_instances,
            ..
        } => validate_inductive_read_only(
            env,
            name,
            universe_params,
            *num_params,
            ty,
            constructors,
            derived_instances,
        )?,
        ElabResult::MutualInductive {
            decl,
            derived_instances,
            ..
        } => validate_mutual_inductive_read_only(env, decl, derived_instances)?,
        ElabResult::Structure {
            name,
            universe_params,
            num_params,
            ty,
            ctor_name,
            ctor_ty,
            field_names,
            projections,
            derived_instances,
            ..
        } => validate_structure_read_only(
            env,
            name,
            universe_params,
            *num_params,
            ty,
            ctor_name,
            ctor_ty,
            field_names,
            projections,
            derived_instances,
        )?,
        ElabResult::Multiple(results) => {
            for inner in results {
                validate_decl_read_only(env, tc, inner)?;
            }
            return Ok(inferred_type);
        }
        ElabResult::Command(_) | ElabResult::Skipped => {
            return Err(
                "Type check error: unsupported declaration kind cannot be checked read-only"
                    .to_string(),
            );
        }
        // A `Failed` leaf is an inner decl that already failed; surface its
        // recorded error rather than attempting a (meaningless) read-only check.
        ElabResult::Failed { name, error, .. } => {
            return Err(format!("Type check error in declaration {name}: {error}"));
        }
    }

    Ok(inferred_type)
}

fn validate_inductive_read_only(
    env: &Environment,
    name: &clean_kernel::Name,
    universe_params: &[clean_kernel::Name],
    num_params: u32,
    ty: &clean_kernel::Expr,
    constructors: &[(clean_kernel::Name, clean_kernel::Expr)],
    derived_instances: &[DerivedInstance],
) -> Result<(), String> {
    let mut shadowed_names = HashSet::from([name.clone()]);
    insert_generated_inductive_names(&mut shadowed_names, name);
    // Shadow artifacts from a prior nested-inductive registration (#3392).
    // The current restore pass erases its temporary `_nested.*` mirrors and
    // retains container-major companions as `<type>.rec_N`; both current and
    // legacy spellings must be pruned from the read-only replay overlay.
    insert_nested_auxiliary_names(&mut shadowed_names, env, name);
    for (ctor_name, _) in constructors {
        shadowed_names.insert(ctor_name.clone());
    }
    for inst in derived_instances {
        shadowed_names.insert(inst.name.clone());
    }

    let mut overlay = shadowing_overlay_env(env, &shadowed_names);
    overlay
        .add_inductive(InductiveDecl {
            level_params: universe_params.to_vec(),
            num_params,
            types: vec![InductiveType {
                name: name.clone(),
                type_: ty.clone(),
                constructors: constructors
                    .iter()
                    .map(|(ctor_name, ctor_ty)| Constructor {
                        name: ctor_name.clone(),
                        type_: ctor_ty.clone(),
                    })
                    .collect(),
            }],
        })
        .map_err(|e| format!("Type check error: {e}"))?;

    for inst in derived_instances {
        if overlay.get_const(&inst.name).is_none() {
            if let Err(e) = overlay.add_decl(Declaration::Definition {
                name: inst.name.clone(),
                level_params: universe_params.to_vec(),
                type_: inst.ty.clone(),
                value: inst.val.clone(),
                is_reducible: true,
            }) {
                // Best-effort derived instances (Repr/Hashable/ToString) keep
                // the parent declaration alive on kernel rejection — the bad
                // term is fully checked and simply not registered.
                if is_best_effort_derived_class(&inst.class_name) {
                    continue;
                }
                return Err(format!("Type check error: {e}"));
            }
        }
    }

    Ok(())
}

/// Read-only validation of a mutual inductive family: replay the whole
/// [`InductiveDecl`] into a shadowing overlay so the kernel re-checks positivity
/// and every constructor type without mutating the real environment.
fn validate_mutual_inductive_read_only(
    env: &Environment,
    decl: &InductiveDecl,
    derived_instances: &[DerivedInstance],
) -> Result<(), String> {
    let mut shadowed_names = HashSet::new();
    for ind_ty in &decl.types {
        shadowed_names.insert(ind_ty.name.clone());
        insert_generated_inductive_names(&mut shadowed_names, &ind_ty.name);
        insert_nested_auxiliary_names(&mut shadowed_names, env, &ind_ty.name);
        for ctor in &ind_ty.constructors {
            shadowed_names.insert(ctor.name.clone());
        }
    }
    for inst in derived_instances {
        shadowed_names.insert(inst.name.clone());
    }

    let mut overlay = shadowing_overlay_env(env, &shadowed_names);
    overlay
        .add_inductive(decl.clone())
        .map_err(|e| format!("Type check error: {e}"))?;

    for inst in derived_instances {
        if overlay.get_const(&inst.name).is_none() {
            if let Err(e) = overlay.add_decl(Declaration::Definition {
                name: inst.name.clone(),
                level_params: decl.level_params.clone(),
                type_: inst.ty.clone(),
                value: inst.val.clone(),
                is_reducible: true,
            }) {
                if is_best_effort_derived_class(&inst.class_name) {
                    continue;
                }
                return Err(format!("Type check error: {e}"));
            }
        }
    }

    Ok(())
}

fn validate_structure_read_only(
    env: &Environment,
    name: &clean_kernel::Name,
    universe_params: &[clean_kernel::Name],
    num_params: u32,
    ty: &clean_kernel::Expr,
    ctor_name: &clean_kernel::Name,
    ctor_ty: &clean_kernel::Expr,
    field_names: &[clean_kernel::Name],
    projections: &[(clean_kernel::Name, clean_kernel::Expr, clean_kernel::Expr)],
    derived_instances: &[DerivedInstance],
) -> Result<(), String> {
    let mut shadowed_names = HashSet::from([name.clone(), ctor_name.clone()]);
    insert_generated_inductive_names(&mut shadowed_names, name);
    for (proj_name, _, _) in projections {
        shadowed_names.insert(proj_name.clone());
    }
    for inst in derived_instances {
        shadowed_names.insert(inst.name.clone());
    }

    let mut overlay = shadowing_overlay_env(env, &shadowed_names);
    overlay
        .add_inductive(InductiveDecl {
            level_params: universe_params.to_vec(),
            num_params,
            types: vec![InductiveType {
                name: name.clone(),
                type_: ty.clone(),
                constructors: vec![Constructor {
                    name: ctor_name.clone(),
                    type_: ctor_ty.clone(),
                }],
            }],
        })
        .map_err(|e| format!("Type check error: {e}"))?;
    overlay
        .register_structure_fields(name.clone(), field_names.to_vec())
        .map_err(|e| format!("Type check error: {e}"))?;

    for (proj_name, proj_ty, proj_val) in projections {
        overlay
            .add_decl(Declaration::Definition {
                name: proj_name.clone(),
                level_params: universe_params.to_vec(),
                type_: proj_ty.clone(),
                value: proj_val.clone(),
                is_reducible: true,
            })
            .map_err(|e| format!("Type check error: {e}"))?;
    }
    for inst in derived_instances {
        if overlay.get_const(&inst.name).is_none() {
            if let Err(e) = overlay.add_decl(Declaration::Definition {
                name: inst.name.clone(),
                level_params: universe_params.to_vec(),
                type_: inst.ty.clone(),
                value: inst.val.clone(),
                is_reducible: true,
            }) {
                // Best-effort derived instances (Repr/Hashable/ToString) keep
                // the parent declaration alive on kernel rejection.
                if is_best_effort_derived_class(&inst.class_name) {
                    continue;
                }
                return Err(format!("Type check error: {e}"));
            }
        }
    }

    Ok(())
}

fn shadowing_overlay_env(
    env: &Environment,
    shadowed_names: &HashSet<clean_kernel::Name>,
) -> Environment {
    env.clone_pruned_shadowing_overlay(shadowed_names)
}

fn insert_generated_inductive_names(
    shadowed_names: &mut HashSet<clean_kernel::Name>,
    type_name: &clean_kernel::Name,
) {
    let type_name_str = type_name.to_string();
    for suffix in ["rec", "casesOn", "recOn", "noConfusionType", "noConfusion"] {
        shadowed_names.insert(clean_kernel::Name::from_string(&format!(
            "{type_name_str}.{suffix}"
        )));
    }
}

/// Insert names for artifacts generated by nested-inductive elimination (#3392).
///
/// When an inductive type uses a container applied to itself (e.g.,
/// `aggregate : List Value -> Value`), the kernel temporarily creates auxiliary
/// types and then restores their eliminators as `Value.rec_1`, `Value.rec_2`,
/// etc. If the declaration is replayed read-only after ordinary elaboration has
/// already registered it, those companions must be shadowed along with the
/// original family. Otherwise restore rejects the replay as a duplicate even
/// though the overlay is specifically intended to replace that family.
fn insert_nested_auxiliary_names(
    shadowed_names: &mut HashSet<clean_kernel::Name>,
    env: &Environment,
    type_name: &clean_kernel::Name,
) {
    let prefix = format!("{}._", type_name);
    let companion_prefix = format!("{type_name}.rec_");

    // Current post-restore spelling. Restrict the match to registered recursor
    // packets owned by this family so an unrelated user definition such as
    // `Value.rec_helper` (or even a non-recursor `Value.rec_1`) is never pruned.
    for rec_val in env.recursors() {
        let name_str = rec_val.name.to_string();
        if rec_val.inductive_name == *type_name && name_str.starts_with(&companion_prefix) {
            shadowed_names.insert(rec_val.name.clone());
        }
    }

    // Legacy/pre-restore spelling retained for environments imported from an
    // older producer: `TypeName._Container...` plus its generated artifacts.
    for info in env.constants() {
        let name_str = info.name.to_string();
        if name_str.starts_with(&prefix) {
            shadowed_names.insert(info.name.clone());
        }
    }
    for ind_val in env.inductives() {
        let name_str = ind_val.name.to_string();
        if name_str.starts_with(&prefix) {
            shadowed_names.insert(ind_val.name.clone());
            // Also shadow generated recursors/casesOn/recOn for the auxiliary type
            for suffix in ["rec", "casesOn", "recOn", "noConfusionType", "noConfusion"] {
                shadowed_names.insert(clean_kernel::Name::from_string(&format!(
                    "{name_str}.{suffix}"
                )));
            }
        }
    }
    for ctor_val in env.constructors() {
        let name_str = ctor_val.name.to_string();
        if name_str.starts_with(&prefix) {
            shadowed_names.insert(ctor_val.name.clone());
        }
    }
    for rec_val in env.recursors() {
        let name_str = rec_val.name.to_string();
        if name_str.starts_with(&prefix) {
            shadowed_names.insert(rec_val.name.clone());
        }
    }
}

#[cfg(test)]
mod tests {
    use super::validate_decl_read_only;
    use clean_elab::ElabResult;
    use clean_kernel::{BinderInfo, Environment, Expr, Level, Name, TypeChecker};

    fn prelude_env() -> Environment {
        Environment::try_with_prelude().expect("try_with_prelude should succeed")
    }

    #[test]
    fn test_validate_decl_read_only_rejects_skipped_declarations() {
        let env = prelude_env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        let err = validate_decl_read_only(&env, &tc, &ElabResult::Skipped)
            .expect_err("skipped declarations should be rejected");
        assert!(
            err.contains("unsupported declaration kind"),
            "expected unsupported declaration error, got: {err}"
        );
    }

    #[test]
    fn test_validate_decl_read_only_rejects_invalid_inductive_constructor() {
        let env = prelude_env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        let decl = ElabResult::Inductive {
            name: Name::from_string("Bad"),
            universe_params: vec![],
            num_params: 0,
            ty: Expr::sort(Level::succ(Level::zero())),
            constructors: vec![(
                Name::from_string("Bad.mk"),
                Expr::const_(Name::from_string("Nat"), vec![]),
            )],
            derived_instances: vec![],
            modifiers: clean_parser::DeclModifiers::default(),
        };

        let err = validate_decl_read_only(&env, &tc, &decl)
            .expect_err("constructor not returning the inductive should be rejected");
        assert!(
            err.contains("does not return the inductive type"),
            "expected constructor return type error, got: {err}"
        );
    }

    // #2552: opaque with well-typed body accepted
    #[test]
    fn test_validate_decl_read_only_accepts_opaque_with_valid_body() {
        let env = prelude_env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let nat_zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
        let decl = ElabResult::Opaque {
            name: Name::from_string("ok_opaque"),
            universe_params: vec![],
            ty: nat,
            val: Some(nat_zero),
            modifiers: clean_parser::DeclModifiers::default(),
        };
        validate_decl_read_only(&env, &tc, &decl)
            .expect("well-typed opaque body should be accepted");
    }

    // #2552: opaque with ill-typed body rejected
    #[test]
    fn test_validate_decl_read_only_rejects_opaque_with_invalid_body() {
        let env = prelude_env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        // opaque bad : Prop := Type  — Type is not a proof of Prop
        let decl = ElabResult::Opaque {
            name: Name::from_string("bad_opaque"),
            universe_params: vec![],
            ty: Expr::prop(),
            val: Some(Expr::type_()),
            modifiers: clean_parser::DeclModifiers::default(),
        };
        let err = validate_decl_read_only(&env, &tc, &decl)
            .expect_err("ill-typed opaque body should be rejected");
        assert!(
            err.contains("Type check error"),
            "expected type check error, got: {err}"
        );
    }

    // #2552: body-less opaque accepted on sort-only lane
    #[test]
    fn test_validate_decl_read_only_accepts_opaque_without_body() {
        let env = prelude_env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let decl = ElabResult::Opaque {
            name: Name::from_string("declared_opaque"),
            universe_params: vec![],
            ty: nat,
            val: None,
            modifiers: clean_parser::DeclModifiers::default(),
        };
        validate_decl_read_only(&env, &tc, &decl)
            .expect("body-less opaque on sort-only lane should be accepted");
    }

    #[test]
    fn test_validate_decl_read_only_rejects_invalid_structure_projection() {
        let env = prelude_env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        let struct_name = Name::from_string("BrokenStruct");
        let struct_const = Expr::const_(struct_name.clone(), vec![]);
        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let decl = ElabResult::Structure {
            name: struct_name.clone(),
            universe_params: vec![],
            num_params: 0,
            ty: Expr::sort(Level::succ(Level::zero())),
            ctor_name: Name::from_string("BrokenStruct.mk"),
            ctor_ty: Expr::pi(BinderInfo::Default, nat.clone(), struct_const.clone()),
            field_names: vec![Name::from_string("value")],
            field_defaults: vec![],
            projections: vec![(
                Name::from_string("BrokenStruct.value"),
                Expr::pi(BinderInfo::Default, struct_const.clone(), nat),
                Expr::lam(BinderInfo::Default, struct_const, Expr::bvar(0)),
            )],
            projection_param_infos: vec![],
            parents: vec![],
            derived_instances: vec![],
            class_info: None,
            modifiers: clean_parser::DeclModifiers::default(),
        };

        let err = validate_decl_read_only(&env, &tc, &decl)
            .expect_err("projection value/type mismatch should be rejected");
        assert!(
            err.contains("Type mismatch"),
            "expected projection type mismatch, got: {err}"
        );
    }

    /// #3392: Re-validating an inductive with a nested List parameter must
    /// shadow the restored `Value.rec_1` companion from the prior registration.
    #[test]
    fn test_validate_nested_inductive_re_check_3392() {
        use clean_kernel::{Constructor, InductiveDecl, InductiveType};

        // Start with a prelude env that has List, Nat, Bool
        let mut env = prelude_env();

        let value = Name::from_string("Value");
        let value_ref = Expr::const_(value.clone(), vec![]);
        let nat_ref = Expr::const_(Name::from_string("Nat"), vec![]);
        let bool_ref = Expr::const_(Name::from_string("Bool"), vec![]);
        // List.{0} Value : Type 0 = Sort 1 — matches Value's result sort.
        // Using Level::zero() because Value : Type (= Sort 1) lives at universe 0,
        // so List.{0} : Type 0 -> Type 0 is the correct instantiation.
        let list_value = Expr::app(
            Expr::const_(Name::from_string("List"), vec![Level::zero()]),
            value_ref.clone(),
        );

        // Register Value with List Value first (simulating prior declaration)
        let int_type = Expr::pi(
            BinderInfo::Default,
            nat_ref.clone(),
            Expr::pi(BinderInfo::Default, nat_ref.clone(), value_ref.clone()),
        );
        let float_type = Expr::pi(BinderInfo::Default, nat_ref.clone(), value_ref.clone());
        let bool_type = Expr::pi(BinderInfo::Default, bool_ref, value_ref.clone());
        let aggregate_type = Expr::pi(BinderInfo::Default, list_value.clone(), value_ref.clone());

        let value_decl = InductiveDecl {
            level_params: vec![],
            num_params: 0,
            types: vec![InductiveType {
                name: value.clone(),
                type_: Expr::type_(),
                constructors: vec![
                    Constructor {
                        name: Name::from_string("Value.int"),
                        type_: int_type.clone(),
                    },
                    Constructor {
                        name: Name::from_string("Value.float"),
                        type_: float_type.clone(),
                    },
                    Constructor {
                        name: Name::from_string("Value.bool"),
                        type_: bool_type.clone(),
                    },
                    Constructor {
                        name: Name::from_string("Value.aggregate"),
                        type_: aggregate_type.clone(),
                    },
                ],
            }],
        };

        // First registration should succeed
        env.add_inductive(value_decl)
            .expect("first Value registration should succeed");

        // The temporary mirror is erased and its container-major eliminator is
        // retained under Lean's restored companion spelling.
        assert!(
            env.get_inductive(&Name::from_string("Value._List"))
                .is_none(),
            "temporary nested mirror must be erased after restoration"
        );
        assert!(
            env.get_recursor(&Name::from_string("Value.rec_1"))
                .is_some(),
            "Value.rec_1 should retain the restored List companion"
        );

        // Now re-validate via the read-only validation path (simulating the
        // server re-checking an existing declaration). This previously failed
        // with "Duplicate declaration: Value.rec_1" after the restore naming
        // migration (the original #3392 failure used `Value._List`).
        let tc = TypeChecker::with_mode(&env, env.mode());
        let elab_result = ElabResult::Inductive {
            name: value.clone(),
            universe_params: vec![],
            num_params: 0,
            ty: Expr::type_(),
            constructors: vec![
                (Name::from_string("Value.int"), int_type),
                (Name::from_string("Value.float"), float_type),
                (Name::from_string("Value.bool"), bool_type),
                (Name::from_string("Value.aggregate"), aggregate_type),
            ],
            derived_instances: vec![],
            modifiers: clean_parser::DeclModifiers::default(),
        };

        let result = validate_decl_read_only(&env, &tc, &elab_result);
        assert!(
            result.is_ok(),
            "re-validating Value with nested List should succeed (#3392), got: {:?}",
            result.err()
        );
    }
}
