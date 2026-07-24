// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Common test utilities for integration tests.
//!
//! Provides helpers for parsing, elaborating, and type-checking Lean code.

use clean_elab::{elaborate, elaborate_decl, ElabResult};
use clean_kernel::{
    BinderInfo, Declaration, Environment, Expr, KernelClassInfo, KernelInstanceInfo, Name,
    TypeChecker,
};
use clean_parser::{parse_decl, parse_expr};

/// Parse, elaborate, and type-check an expression
pub fn check_expr(env: &Environment, input: &str) -> Result<Expr, String> {
    let surface = parse_expr(input).map_err(|e| format!("Parse error: {e}"))?;
    let kernel_expr = elaborate(env, &surface).map_err(|e| format!("Elab error: {e}"))?;
    let tc = TypeChecker::new(env);
    let ty = tc
        .infer_type(&kernel_expr)
        .map_err(|e| format!("Type error: {e}"))?;
    Ok(ty)
}

/// Register an opaque declaration: body-bearing → `Declaration::Opaque`,
/// body-less → `Declaration::Axiom`. Extracted from `check_and_add_decl` (#2552).
fn register_opaque_decl(
    env: &mut Environment,
    name: Name,
    universe_params: Vec<Name>,
    ty: Expr,
    val: Option<Expr>,
) -> Result<(), String> {
    {
        let tc = TypeChecker::new(env);
        ensure_type_infers(&tc, &ty, "Type check ty")?;
        if let Some(ref value) = val {
            tc.check_type(value, &ty)
                .map_err(|e| format!("Type check val: {e}"))?;
        }
    }
    match val {
        Some(value) => env
            .add_decl(Declaration::Opaque {
                name,
                level_params: universe_params,
                type_: ty,
                value,
            })
            .map_err(|e| format!("Add decl: {e}")),
        None => env
            .add_decl(Declaration::Axiom {
                name,
                level_params: universe_params,
                type_: ty,
            })
            .map_err(|e| format!("Add decl: {e}")),
    }
}

fn ensure_type_infers(tc: &TypeChecker, expr: &Expr, context: &str) -> Result<(), String> {
    let _ = tc.infer_type(expr).map_err(|e| format!("{context}: {e}"))?;
    Ok(())
}

/// Parse, elaborate, type-check and add a declaration to environment
pub fn check_and_add_decl(env: &mut Environment, input: &str) -> Result<(), String> {
    let surface = parse_decl(input).map_err(|e| format!("Parse error: {e}"))?;
    let elab_result = elaborate_decl(env, &surface).map_err(|e| format!("Elab error: {e}"))?;

    match elab_result {
        ElabResult::Definition {
            name,
            universe_params,
            ty,
            val,
            modifiers: _,
        } => {
            {
                // Scope tc to release immutable borrow before add_decl
                let tc = TypeChecker::new(env);
                ensure_type_infers(&tc, &ty, "Type check ty")?;
                tc.check_type(&val, &ty)
                    .map_err(|e| format!("Type check val: {e}"))?;
            }
            env.add_decl(Declaration::Definition {
                name,
                level_params: universe_params,
                type_: ty,
                value: val,
                is_reducible: true,
            })
            .map_err(|e| format!("Add decl: {e}"))?;
        }
        ElabResult::Theorem {
            name,
            universe_params,
            ty,
            proof,
            modifiers: _,
        } => {
            {
                // Scope tc to release immutable borrow before add_decl
                let tc = TypeChecker::new(env);
                ensure_type_infers(&tc, &ty, "Type check ty")?;
                tc.check_type(&proof, &ty)
                    .map_err(|e| format!("Type check proof: {e}"))?;
            }
            env.add_decl(Declaration::Theorem {
                name,
                level_params: universe_params,
                type_: ty,
                value: proof,
            })
            .map_err(|e| format!("Add decl: {e}"))?;
        }
        ElabResult::Axiom {
            name,
            universe_params,
            ty,
            modifiers: _,
        } => register_opaque_decl(env, name, universe_params, ty, None)?,
        ElabResult::Opaque {
            name,
            universe_params,
            ty,
            val,
            modifiers: _,
        } => register_opaque_decl(env, name, universe_params, ty, val)?,
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
            class_info,
            ..
        } => {
            use clean_kernel::{Constructor, InductiveDecl, InductiveType};
            {
                // Type check struct type (not ctor type — kernel validates that)
                let tc = TypeChecker::new(env);
                ensure_type_infers(&tc, &ty, "Type check struct type")?;
            }
            env.add_inductive(InductiveDecl {
                level_params: universe_params.clone(),
                num_params,
                types: vec![InductiveType {
                    name: name.clone(),
                    type_: ty,
                    constructors: vec![Constructor {
                        name: ctor_name,
                        type_: ctor_ty,
                    }],
                }],
            })
            .map_err(|e| format!("Add inductive: {e}"))?;

            env.register_structure_fields(name.clone(), field_names)
                .map_err(|e| format!("Register fields: {e}"))?;

            for (proj_name, proj_ty, proj_val) in projections {
                {
                    let tc = TypeChecker::new(env);
                    ensure_type_infers(
                        &tc,
                        &proj_ty,
                        &format!("Type check projection type for {proj_name}"),
                    )?;
                }
                env.add_decl(Declaration::Definition {
                    name: proj_name.clone(),
                    level_params: universe_params.clone(),
                    type_: proj_ty,
                    value: proj_val,
                    is_reducible: true,
                })
                .map_err(|e| format!("Add projection {proj_name}: {e}"))?;
            }

            if let Some(info) = class_info {
                env.register_class(KernelClassInfo {
                    name: name.clone(),
                    num_params: info.num_params,
                    out_params: info.out_params,
                    semi_out_params: info.semi_out_params,
                });
            }

            // Register derived instances (#439, #443)
            for inst in derived_instances {
                // Skip already-existing toParent projections
                if env.get_const(&inst.name).is_none() {
                    {
                        let tc = TypeChecker::new(env);
                        ensure_type_infers(
                            &tc,
                            &inst.ty,
                            &format!("Type check derived instance type '{}'", inst.name),
                        )?;
                        tc.check_type(&inst.val, &inst.ty).map_err(|e| {
                            format!("Type check derived instance val '{}': {e}", inst.name)
                        })?;
                    }
                    // Use the instance's own level_params, NOT the struct's universe_params.
                    // Derive handlers generate fresh universe params (e.g., u_0) for
                    // universe-polymorphic constants they reference.  Fixes #3393.
                    env.add_decl(Declaration::Definition {
                        name: inst.name.clone(),
                        level_params: inst.level_params.clone(),
                        type_: inst.ty.clone(),
                        value: inst.val.clone(),
                        is_reducible: true,
                    })
                    .map_err(|e| format!("Add derived instance '{}': {e}", inst.name))?;
                }

                // Register instance metadata with correct binder info (#443)
                env.register_instance(KernelInstanceInfo {
                    name: inst.name.clone(),
                    class_name: inst.class_name.clone(),
                    priority: inst.priority,
                    type_: Some(inst.ty),
                    value: Some(inst.val),
                });
            }
        }
        ElabResult::Inductive {
            name,
            universe_params,
            num_params,
            ty,
            constructors,
            derived_instances,
            ..
        } => {
            use clean_kernel::{Constructor, InductiveDecl, InductiveType};
            {
                let tc = TypeChecker::new(env);
                ensure_type_infers(&tc, &ty, "Type check inductive type")?;
            }
            let ctors: Vec<Constructor> = constructors
                .into_iter()
                .map(|(ctor_name, ctor_ty)| Constructor {
                    name: ctor_name,
                    type_: ctor_ty,
                })
                .collect();
            env.add_inductive(InductiveDecl {
                level_params: universe_params,
                num_params,
                types: vec![InductiveType {
                    name,
                    type_: ty,
                    constructors: ctors,
                }],
            })
            .map_err(|e| format!("Add inductive: {e}"))?;
            let _ = derived_instances;
        }
        ElabResult::Instance {
            name,
            universe_params,
            ty,
            val,
            ..
        } => {
            {
                let tc = TypeChecker::new(env);
                ensure_type_infers(&tc, &ty, "Type check instance type")?;
                tc.check_type(&val, &ty)
                    .map_err(|e| format!("Type check instance val: {e}"))?;
            }
            env.add_decl(Declaration::Definition {
                name,
                level_params: universe_params,
                type_: ty,
                value: val,
                is_reducible: true,
            })
            .map_err(|e| format!("Add instance: {e}"))?;
        }
        ElabResult::MutualInductive { decl, .. } => {
            {
                let tc = TypeChecker::new(env);
                for it in &decl.types {
                    ensure_type_infers(&tc, &it.type_, "Type check mutual inductive type")?;
                }
            }
            // The kernel re-checks positivity and every constructor for the
            // whole family in one call.
            env.add_inductive(decl)
                .map_err(|e| format!("Add mutual inductive: {e}"))?;
        }
        ElabResult::Skipped | ElabResult::Command(_) => {} // import, #check, etc.
        // An `example` is already fully kernel-checked during elaboration and
        // is checked-then-DISCARDED (B02): nothing to add to the environment.
        ElabResult::Example { .. } => {}
        ElabResult::Multiple(results) => {
            for r in results {
                // Recursively register each sub-result (not ideal, but handles the case)
                let _ = r;
            }
        }
        // A failing inner decl surfaces its recorded error rather than being added.
        ElabResult::Failed { name, error, .. } => {
            return Err(format!("{name}: {error}"));
        }
    }

    Ok(())
}

// =============================================================================
// Arithmetic Environment Setup (used by tactics and regression tests)
// =============================================================================

/// Helper to set up an environment with arithmetic axioms for tactic tests.
///
/// Initializes: Nat, Int, Even, Odd, Dvd, LE, LT, and key lemmas.
pub fn setup_arith_env() -> Environment {
    let mut env = Environment::new();

    // Initialize core types
    env.init_nat().expect("init_nat failed");
    env.init_and().expect("init_and failed");
    env.init_true_false().expect("init_true_false failed");
    env.init_classical().expect("init_classical failed");
    env.init_eq().expect("init_eq failed"); // Required for Eq.symm, Eq.trans in proof reconstruction

    // Add Int type (simplified - just the type, not the full implementation)
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Int"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .expect("add Int axiom");

    // Add Even predicate: Even : Nat -> Prop
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Even"),
        level_params: vec![],
        type_: Expr::arrow(Expr::const_(Name::from_string("Nat"), vec![]), Expr::prop()),
    })
    .expect("add Even axiom");

    // Add Odd predicate: Odd : Nat -> Prop
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Odd"),
        level_params: vec![],
        type_: Expr::arrow(Expr::const_(Name::from_string("Nat"), vec![]), Expr::prop()),
    })
    .expect("add Odd axiom");

    // Add Dvd relation: Dvd : Nat -> Nat -> Prop
    // In Mathlib: Dvd.dvd m n means m divides n
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Dvd.dvd"),
        level_params: vec![],
        type_: Expr::arrow(
            Expr::const_(Name::from_string("Nat"), vec![]),
            Expr::arrow(Expr::const_(Name::from_string("Nat"), vec![]), Expr::prop()),
        ),
    })
    .expect("add Dvd.dvd axiom");

    // Add LE relation: LE.le : Nat -> Nat -> Prop
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("LE.le"),
        level_params: vec![],
        type_: Expr::arrow(
            Expr::const_(Name::from_string("Nat"), vec![]),
            Expr::arrow(Expr::const_(Name::from_string("Nat"), vec![]), Expr::prop()),
        ),
    })
    .expect("add LE.le axiom");

    // Add LT relation: LT.lt : Nat -> Nat -> Prop
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("LT.lt"),
        level_params: vec![],
        type_: Expr::arrow(
            Expr::const_(Name::from_string("Nat"), vec![]),
            Expr::arrow(Expr::const_(Name::from_string("Nat"), vec![]), Expr::prop()),
        ),
    })
    .expect("add LT.lt axiom");

    // Note: absurd is already provided by init_true_false() above.
    // A previous version silently swallowed a DuplicateName error via .ok() here.

    // Add Nat.even_and_odd_elim : forall n, Even n -> Odd n -> False
    // This is the key lemma for parity contradiction proofs.
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let false_ty = Expr::const_(Name::from_string("False"), vec![]);
    let even_n = Expr::app(
        Expr::const_(Name::from_string("Even"), vec![]),
        Expr::bvar(0),
    );
    let odd_n = Expr::app(
        Expr::const_(Name::from_string("Odd"), vec![]),
        Expr::bvar(1),
    );
    let parity_elim_ty = Expr::pi(
        BinderInfo::Default,
        nat.clone(),
        Expr::pi(
            BinderInfo::Default,
            even_n,
            Expr::pi(BinderInfo::Default, odd_n, false_ty),
        ),
    );
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Nat.even_and_odd_elim"),
        level_params: vec![],
        type_: parity_elim_ty,
    })
    .expect("add Nat.even_and_odd_elim axiom");

    // Add le_trans as an axiom (simplified type for testing)
    // le_trans : (a <= b) -> (b <= c) -> (a <= c)
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("le_trans"),
        level_params: vec![],
        type_: Expr::arrow(
            Expr::prop(), // a <= b (simplified)
            Expr::arrow(
                Expr::prop(), // b <= c
                Expr::prop(), // a <= c
            ),
        ),
    })
    .expect("add le_trans axiom");

    env
}
