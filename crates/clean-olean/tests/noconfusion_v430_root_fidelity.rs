// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! 33-root noConfusion twin-type fidelity gate vs the GENUINE Lean v4.30
//! olean types (designs/2026-07-03-noconfusion-ctoridx-convention.md §6/A5).
//!
//! For every prelude-seeded inductive root that produced `existing checked
//! inductive-family constant … has different type` rows in the Init.Prelude /
//! Init.Core stamps (31 Init.Prelude roots + Sigma + Sum), Clean's
//! kernel-synthesized `T.noConfusionType` / `T.noConfusion` TYPE must match
//! the genuine olean type under the shard-acceptance predicate: identical
//! level-param arity, positional level renaming, and the kernel's
//! `is_def_eq` (mirroring
//! `clean-mathverse/src/verify/incremental/mod.rs:863-907`).
//!
//! Requires the pinned v4.30.0-rc2 toolchain; skips gracefully when absent
//! (same convention as `import_mathlib_tests.rs`).

use std::collections::{HashMap, HashSet};
use std::path::PathBuf;

use clean_kernel::env::Environment;
use clean_kernel::expr::{BinderInfo, Expr, ExprKind};
use clean_kernel::level::Level;
use clean_kernel::name::Name;
use clean_kernel::tc::TypeChecker;
use clean_olean::{convert_parsed_constant_to_const_info, parse_module_file};

/// The 31 Init.Prelude dedup-conflict roots (design §2.5).
const ROOTS_PRELUDE: &[&str] = &[
    "Add",
    "Array",
    "BEq",
    "Decidable",
    "Fin",
    "HAdd",
    "HAnd",
    "HAppend",
    "HDiv",
    "HMod",
    "HMul",
    "HOr",
    "HPow",
    "HShiftLeft",
    "HShiftRight",
    "HSub",
    "HXor",
    "Inhabited",
    "LE",
    "List",
    "LT",
    "Membership",
    "Mul",
    "Neg",
    "OfNat",
    "One",
    "Option",
    "Prod",
    "Sub",
    "Subtype",
    "Zero",
];
/// The 2 Init.Core roots (Sigma/Sum twins are realized lazily there —
/// design §1.6/§2.5).
const ROOTS_CORE: &[&str] = &["Sigma", "Sum"];

fn toolchain_lib() -> Option<PathBuf> {
    if let Ok(p) = std::env::var("CLEAN_V430_LEAN_LIB") {
        let p = PathBuf::from(p);
        if p.exists() {
            return Some(p);
        }
    }
    let home = std::env::var("HOME").ok()?;
    let p = PathBuf::from(home).join(".elan/toolchains/leanprover--lean4---v4.30.0-rc2/lib/lean");
    p.exists().then_some(p)
}

/// Register the `outParam` / `semiOutParam` identity gadgets so `is_def_eq`
/// can unfold them: the GENUINE H-class / Membership twin types spell their
/// out-params as `outParam (Type w)`, while Clean's seeded types use the
/// plain sort — the two are definitionally equal exactly like they are in a
/// real import environment (where the olean provides these definitions).
fn register_out_param_gadgets(env: &mut Environment) {
    for name in ["outParam", "semiOutParam"] {
        let u = Name::from_string("u");
        let sort_u = Expr::from_kind(ExprKind::Sort(Level::param(u.clone())));
        // outParam.{u} : Sort u → Sort u := fun α => α
        let ty = Expr::pi(BinderInfo::Default, sort_u.clone(), sort_u.clone());
        let val = Expr::lam(BinderInfo::Default, sort_u, Expr::bvar(0));
        env.add_decl(clean_kernel::env::Declaration::Definition {
            name: Name::from_string(name),
            level_params: vec![u],
            type_: ty,
            value: val,
            is_reducible: true,
        })
        .expect("outParam gadget should register");
    }
}

#[test]
fn test_v430_33_root_twin_types_match_genuine_olean() {
    let Some(lib) = toolchain_lib() else {
        eprintln!(
            "SKIP: leanprover--lean4---v4.30.0-rc2 toolchain not found \
             (set CLEAN_V430_LEAN_LIB to override)"
        );
        return;
    };

    // Collect the genuine twin types from the raw olean constant streams.
    let mut genuine: HashMap<String, (Vec<Name>, Expr)> = HashMap::new();
    for (file, roots) in [
        ("Init/Prelude.olean", ROOTS_PRELUDE),
        ("Init/Core.olean", ROOTS_CORE),
    ] {
        let wanted: HashSet<String> = roots
            .iter()
            .flat_map(|r| [format!("{r}.noConfusionType"), format!("{r}.noConfusion")])
            .collect();
        let module =
            parse_module_file(lib.join(file)).unwrap_or_else(|e| panic!("parse {file}: {e:?}"));
        for pc in &module.constants {
            if !wanted.contains(&pc.name) {
                continue;
            }
            let ci = convert_parsed_constant_to_const_info(pc)
                .unwrap_or_else(|e| panic!("convert {}: {e:?}", pc.name))
                .unwrap_or_else(|| panic!("{} should be a value-bearing decl", pc.name));
            genuine.insert(pc.name.clone(), (ci.level_params, ci.type_));
        }
    }

    // Clean's seeded twins (synthesized by the kernel generator at prelude
    // init — the same twins name-dedup keeps on import, design §2.3/M1).
    let mut env = Environment::with_prelude();
    register_out_param_gadgets(&mut env);
    let tc = TypeChecker::new(&env);

    let mut missing_genuine: Vec<String> = Vec::new();
    let mut missing_seeded: Vec<String> = Vec::new();
    let mut mismatched: Vec<String> = Vec::new();
    for root in ROOTS_PRELUDE.iter().chain(ROOTS_CORE) {
        for suffix in ["noConfusionType", "noConfusion"] {
            let name = format!("{root}.{suffix}");
            let Some((g_levels, g_type)) = genuine.get(&name) else {
                missing_genuine.push(name);
                continue;
            };
            let Some(seeded) = env.get_const(&Name::from_string(&name)) else {
                missing_seeded.push(name);
                continue;
            };
            // The acceptance predicate (verify/incremental/mod.rs:863-907):
            // identical level arity, positional rename, then def-eq.
            if seeded.level_params.len() != g_levels.len() {
                mismatched.push(format!(
                    "{name}: level arity {} (seeded) vs {} (genuine)",
                    seeded.level_params.len(),
                    g_levels.len()
                ));
                continue;
            }
            let renaming: Vec<Level> = seeded
                .level_params
                .iter()
                .map(|n| Level::param(n.clone()))
                .collect();
            let g_renamed = g_type.instantiate_level_params_direct(g_levels, &renaming);
            if !tc.is_def_eq(&seeded.type_, &g_renamed) {
                mismatched.push(format!(
                    "{name}:\n  seeded:  {:?}\n  genuine: {g_renamed:?}",
                    seeded.type_
                ));
            }
        }
    }

    assert!(
        missing_genuine.is_empty(),
        "genuine twins not found in the oleans (root list stale?): {missing_genuine:?}"
    );
    assert!(
        missing_seeded.is_empty(),
        "seeded twins missing from with_prelude (seeding regressed?): {missing_seeded:?}"
    );
    assert!(
        mismatched.is_empty(),
        "{} of 66 twin TYPES diverge from the genuine v4.30 olean types \
         (design §6/A5):\n{}",
        mismatched.len(),
        mismatched.join("\n")
    );
}
