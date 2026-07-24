// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use crate::ElabError;
use clean_kernel::{
    BinderInfo, Declaration, Environment, Expr, KernelClassInfo, KernelInstanceInfo, Level, Name,
    DEFAULT_INSTANCE_PRIORITY,
};

pub trait PreludeProvider {
    fn provides(&self) -> &'static [&'static str];
    fn init(&self, env: &mut Environment) -> Result<(), ElabError>;
}

struct Provider {
    modules: &'static [&'static str],
    init: fn(&mut Environment) -> Result<(), ElabError>,
}

impl PreludeProvider for Provider {
    fn provides(&self) -> &'static [&'static str] {
        self.modules
    }

    fn init(&self, env: &mut Environment) -> Result<(), ElabError> {
        (self.init)(env)
    }
}

fn map_init_error<E: std::fmt::Display>(init: &str, err: E) -> ElabError {
    ElabError::NotImplemented(format!("{init}: {err}"))
}

fn init_euclidean_geometry(env: &mut Environment) -> Result<(), ElabError> {
    env.init_euclidean_geometry()
        .map_err(|e| map_init_error("init_euclidean_geometry", e))?;
    env.init_euclidean_angle()
        .map_err(|e| map_init_error("init_euclidean_angle", e))?;
    Ok(())
}

fn init_inner_product_space(env: &mut Environment) -> Result<(), ElabError> {
    env.init_euclidean_geometry()
        .map_err(|e| map_init_error("init_euclidean_geometry", e))?;
    Ok(())
}

fn init_real_numbers(env: &mut Environment) -> Result<(), ElabError> {
    env.init_hadd()
        .map_err(|e| map_init_error("init_hadd", e))?;
    env.init_hsub()
        .map_err(|e| map_init_error("init_hsub", e))?;
    env.init_hmul()
        .map_err(|e| map_init_error("init_hmul", e))?;
    env.init_hdiv()
        .map_err(|e| map_init_error("init_hdiv", e))?;
    env.init_hpow()
        .map_err(|e| map_init_error("init_hpow", e))?;
    env.init_real_complex_analysis()
        .map_err(|e| map_init_error("init_real_complex_analysis", e))?;
    env.init_real_linear_order()
        .map_err(|e| map_init_error("init_real_linear_order", e))?;
    env.init_real_hadd_inst()
        .map_err(|e| map_init_error("init_real_hadd_inst", e))?;
    env.init_real_hpow_nat_inst()
        .map_err(|e| map_init_error("init_real_hpow_nat_inst", e))?;
    env.init_ofnat_nat()
        .map_err(|e| map_init_error("init_ofnat_nat", e))?;
    env.init_ofnat_real()
        .map_err(|e| map_init_error("init_ofnat_real", e))?;
    Ok(())
}

fn init_set_theory(env: &mut Environment) -> Result<(), ElabError> {
    env.init_set_theory()
        .map_err(|e| map_init_error("init_set_theory", e))?;
    Ok(())
}

fn init_topology(env: &mut Environment) -> Result<(), ElabError> {
    env.init_topological_space()
        .map_err(|e| map_init_error("init_topological_space", e))?;
    Ok(())
}

fn init_metric_space(env: &mut Environment) -> Result<(), ElabError> {
    env.init_metric_space()
        .map_err(|e| map_init_error("init_metric_space", e))?;
    Ok(())
}

fn init_number_theory(env: &mut Environment) -> Result<(), ElabError> {
    env.init_number_theory()
        .map_err(|e| map_init_error("init_number_theory", e))?;
    Ok(())
}

fn init_ring(env: &mut Environment) -> Result<(), ElabError> {
    env.init_ring()
        .map_err(|e| map_init_error("init_ring", e))?;
    Ok(())
}

fn init_rat_field(env: &mut Environment) -> Result<(), ElabError> {
    env.init_rat_field_inst()
        .map_err(|e| map_init_error("init_rat_field_inst", e))?;
    Ok(())
}

fn init_linear_algebra(env: &mut Environment) -> Result<(), ElabError> {
    env.init_algebra_linear()
        .map_err(|e| map_init_error("init_algebra_linear", e))?;
    Ok(())
}

fn init_module_submodule(env: &mut Environment) -> Result<(), ElabError> {
    env.init_add_comm_group()
        .map_err(|e| map_init_error("init_add_comm_group", e))?;
    env.init_module()
        .map_err(|e| map_init_error("init_module", e))?;
    env.init_submodule()
        .map_err(|e| map_init_error("init_submodule", e))?;
    Ok(())
}

fn init_algebra(env: &mut Environment) -> Result<(), ElabError> {
    env.init_algebra()
        .map_err(|e| map_init_error("init_algebra", e))?;
    Ok(())
}

fn init_ideal(env: &mut Environment) -> Result<(), ElabError> {
    env.init_ideal()
        .map_err(|e| map_init_error("init_ideal", e))?;
    Ok(())
}

fn ensure_semiring_class(env: &mut Environment) -> Result<(), ElabError> {
    let semiring = Name::from_string("Semiring");
    if env.get_const(&semiring).is_none() {
        env.init_ring()
            .map_err(|e| map_init_error("init_ring", e))?;
    }
    if !env.is_class(&semiring) {
        env.register_class(KernelClassInfo {
            name: semiring,
            num_params: 1,
            out_params: vec![],
            semi_out_params: vec![],
        });
    }
    Ok(())
}

fn semiring_app(level: Level, ty: Expr) -> Expr {
    Expr::app(Expr::const_(Name::from_string("Semiring"), vec![level]), ty)
}

fn zmod_app(n: Expr) -> Expr {
    Expr::app(Expr::const_(Name::from_string("ZMod"), vec![]), n)
}

fn mvpolynomial_app(u: Level, v: Level, sigma: Expr, r: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("MvPolynomial"), vec![u, v]),
        [sigma, r],
    )
}

fn register_semiring_zmod_instance(env: &mut Environment) -> Result<(), ElabError> {
    if env.get_const(&Name::from_string("ZMod")).is_none() {
        return Ok(());
    }

    ensure_semiring_class(env)?;

    let inst_name = Name::from_string("instSemiringZMod");
    if env.get_const(&inst_name).is_none() {
        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let body = semiring_app(Level::zero(), zmod_app(Expr::bvar(0)));
        let inst_ty = Expr::pi(BinderInfo::Implicit, nat, body);
        env.add_decl_if_absent(Declaration::Axiom {
            name: inst_name.clone(),
            level_params: vec![],
            type_: inst_ty,
        })
        .map_err(|e| map_init_error("init_zmod_basic instSemiringZMod", e))?;
    }

    if !env.is_instance(&inst_name) {
        env.register_instance(KernelInstanceInfo {
            name: inst_name,
            class_name: Name::from_string("Semiring"),
            priority: DEFAULT_INSTANCE_PRIORITY,
            type_: None,
            value: None,
        });
    }

    Ok(())
}

fn register_semiring_mvpolynomial_instance(env: &mut Environment) -> Result<(), ElabError> {
    let mvpolynomial = Name::from_string("MvPolynomial");
    if env.get_const(&mvpolynomial).is_none() {
        return Ok(());
    }

    ensure_semiring_class(env)?;

    let inst_name = Name::from_string("instSemiringMvPolynomial");
    if env.get_const(&inst_name).is_none() {
        let u = Name::from_string("u");
        let v = Name::from_string("v");
        let u_level = Level::param(u.clone());
        let v_level = Level::param(v.clone());
        let type_u = Expr::sort(Level::succ(u_level.clone()));
        let type_v = Expr::sort(Level::succ(v_level.clone()));
        let semiring_r = semiring_app(v_level.clone(), Expr::bvar(0));
        let mvpoly_ty = mvpolynomial_app(
            u_level.clone(),
            v_level.clone(),
            Expr::bvar(2),
            Expr::bvar(1),
        );
        let result = semiring_app(Level::max(u_level.clone(), v_level.clone()), mvpoly_ty);
        let inst_ty = Expr::pi(
            BinderInfo::Implicit,
            type_u,
            Expr::pi(
                BinderInfo::Implicit,
                type_v,
                Expr::pi(BinderInfo::InstImplicit, semiring_r, result),
            ),
        );
        env.add_decl_if_absent(Declaration::Axiom {
            name: inst_name.clone(),
            level_params: vec![u, v],
            type_: inst_ty,
        })
        .map_err(|e| map_init_error("init_mvpolynomial_basic instSemiringMvPolynomial", e))?;
    }

    if !env.is_instance(&inst_name) {
        env.register_instance(KernelInstanceInfo {
            name: inst_name,
            class_name: Name::from_string("Semiring"),
            priority: DEFAULT_INSTANCE_PRIORITY,
            type_: None,
            value: None,
        });
    }

    Ok(())
}

/// Swallow "Duplicate declaration" errors — these happen when the prelude
/// already registered a name that an init_* function tries to re-add.
/// This is harmless and expected when loading Mathlib stubs on top of
/// `Environment::with_prelude()`.
fn ignore_dup<E: std::fmt::Display>(result: Result<(), E>) {
    if let Err(e) = result {
        let msg = e.to_string();
        if !msg.contains("Duplicate declaration") && !msg.contains("duplicate declaration") {
            tracing::warn!("init stub error (non-duplicate): {msg}");
        }
    }
}

fn init_full_mathlib(env: &mut Environment) -> Result<(), ElabError> {
    ignore_dup(env.init_list());
    ignore_dup(env.init_set());
    ignore_dup(env.init_ge());
    ignore_dup(env.init_nontrivial());
    ignore_dup(env.init_and());
    ignore_dup(env.init_ring());
    ignore_dup(env.init_comm_ring());
    ignore_dup(env.init_field());
    ignore_dup(env.init_integral_domain());
    ignore_dup(env.init_group());
    ignore_dup(env.init_add_comm_group());
    ignore_dup(env.init_module_algebra_all());
    ignore_dup(env.init_algebra_linear());
    ignore_dup(env.init_fin());
    ignore_dup(env.init_polynomial());
    ignore_dup(env.init_is_principal_ideal_ring());
    ignore_dup(env.init_prime());
    ignore_dup(env.init_ufm());
    ignore_dup(env.init_set_theory());
    ignore_dup(env.init_category_theory());
    ignore_dup(env.init_real_complex_analysis());
    ignore_dup(env.init_subgroup());
    ignore_dup(env.init_subring());
    ignore_dup(env.init_subfield());
    ignore_dup(env.init_submonoid());
    ignore_dup(env.init_fact());
    ignore_dup(env.init_odd());
    ignore_dup(env.init_nat_card());
    ignore_dup(env.init_ring_hom());
    ignore_dup(env.init_is_empty());
    ignore_dup(env.init_finite());
    ignore_dup(env.init_domain_types());
    ignore_dup(env.init_fate_x_order_stubs());
    ignore_dup(env.init_io());
    ignore_dup(env.init_state_t());
    ignore_dup(env.init_state_m());
    register_semiring_zmod_instance(env)?;
    register_semiring_mvpolynomial_instance(env)?;
    Ok(())
}

fn init_measure_theory(env: &mut Environment) -> Result<(), ElabError> {
    env.init_measure_theory()
        .map_err(|e| map_init_error("init_measure_theory", e))?;
    Ok(())
}

fn init_combinatorics(env: &mut Environment) -> Result<(), ElabError> {
    env.init_combinatorics()
        .map_err(|e| map_init_error("init_combinatorics", e))?;
    Ok(())
}

fn init_graph_theory(env: &mut Environment) -> Result<(), ElabError> {
    env.init_graph_theory()
        .map_err(|e| map_init_error("init_graph_theory", e))?;
    Ok(())
}

fn init_zmod_basic(env: &mut Environment) -> Result<(), ElabError> {
    env.init_nat().map_err(|e| map_init_error("init_nat", e))?;

    let zmod_name = Name::from_string("ZMod");
    if env.get_const(&zmod_name).is_none() {
        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let type0 = Expr::sort(Level::succ(Level::zero()));
        let zmod_type = Expr::pi(BinderInfo::Default, nat, type0);
        env.add_decl_if_absent(Declaration::Axiom {
            name: zmod_name,
            level_params: vec![],
            type_: zmod_type,
        })
        .map_err(|e| map_init_error("init_zmod_basic", e))?;
    }

    register_semiring_zmod_instance(env)?;
    Ok(())
}

/// Register a single opaque constant (`name : type_`) as a `Declaration::Axiom`,
/// idempotently. Axioms are explicit trust assumptions checked for type
/// well-formedness by the kernel — they are NOT proofs and do NOT touch the
/// `add_decl_unchecked`/`add_decl_structural` ratchet.
fn register_opaque_axiom(env: &mut Environment, name: &str, type_: Expr) -> Result<(), ElabError> {
    env.add_decl_if_absent(Declaration::Axiom {
        name: Name::from_string(name),
        level_params: vec![],
        type_,
    })
    .map_err(|e| map_init_error("init_lean_meta_prelude", e))
}

/// Clean-native metaprogramming shim (plan decision 1).
///
/// Stands in for `import Lean.Elab` / `import Lean.Meta` and the
/// `Lean.Syntax` / `Lean.Expr` surface they pull in, so that meta-*referencing*
/// Lean files **elaborate** under Clean-native semantics WITHOUT depending on
/// real Lean `.olean` metaprogramming artifacts. This is the Tier-1 ("merely
/// elaborates") layer from `reports/phase0-meta-shim-surface-2026-06-23.md`: the
/// foundational types are registered as opaque axioms (labeled trust
/// assumptions) so their names resolve; executable Clean-native macro/elaborator
/// behavior (Tier 2) and the long tail (Tier 3) build on top in later work.
fn init_lean_meta_prelude(env: &mut Environment) -> Result<(), ElabError> {
    // `Type` (`Sort 1`).
    let type0 = Expr::sort(Level::succ(Level::zero()));
    // `Type → Type`, the kind of the metaprogramming monads.
    let type_to_type = Expr::pi(BinderInfo::Default, type0.clone(), type0.clone());

    // Foundational opaque `Type`-valued meta types (Init/Prelude + Lean/Expr).
    for name in [
        "Lean.Name",
        "Lean.Syntax",
        "Lean.SourceInfo",
        "Lean.Level",
        "Lean.Expr",
        "Lean.Macro",
    ] {
        register_opaque_axiom(env, name, type0.clone())?;
    }

    // Metaprogramming monads, as opaque `Type → Type` constructors.
    for name in [
        "Lean.MacroM",
        "Lean.MetaM",
        "Lean.CoreM",
        "Lean.Elab.TermElabM",
        "Lean.Elab.Tactic.TacticM",
        "Lean.Elab.Command.CommandElabM",
    ] {
        register_opaque_axiom(env, name, type_to_type.clone())?;
    }

    Ok(())
}

static PRELUDE_PROVIDERS: &[Provider] = &[
    Provider {
        modules: &[
            "Mathlib.Geometry.Euclidean.Basic",
            "Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic",
            "Mathlib.Geometry.Euclidean.Angle.Unoriented.Affine",
            "Mathlib.Geometry.Euclidean.Angle.Oriented.Basic",
        ],
        init: init_euclidean_geometry,
    },
    Provider {
        modules: &[
            "Mathlib.Analysis.InnerProductSpace.Basic",
            "Mathlib.Analysis.InnerProductSpace.PiL2",
        ],
        init: init_inner_product_space,
    },
    Provider {
        modules: &["Mathlib.Data.Real.Basic", "Mathlib.Data.Real.Sqrt"],
        init: init_real_numbers,
    },
    Provider {
        modules: &["Mathlib.Data.Set.Basic", "Mathlib.Data.Set.Function"],
        init: init_set_theory,
    },
    Provider {
        modules: &["Mathlib.Topology.Basic", "Mathlib.Topology.Constructions"],
        init: init_topology,
    },
    Provider {
        modules: &["Mathlib.Topology.MetricSpace.Basic"],
        init: init_metric_space,
    },
    Provider {
        modules: &["Mathlib.NumberTheory.Basic"],
        init: init_number_theory,
    },
    Provider {
        modules: &["Mathlib.Algebra.Ring.Basic"],
        init: init_ring,
    },
    Provider {
        modules: &["Mathlib.Algebra.Field.Basic"],
        init: init_rat_field,
    },
    Provider {
        modules: &["Mathlib.LinearAlgebra.Basic"],
        init: init_linear_algebra,
    },
    Provider {
        modules: &[
            "Mathlib.Algebra.Module.Basic",
            "Mathlib.Algebra.Module.Submodule.Basic",
        ],
        init: init_module_submodule,
    },
    Provider {
        modules: &[
            "Mathlib.Algebra.Algebra.Basic",
            "Mathlib.RingTheory.Adjoin.Basic",
        ],
        init: init_algebra,
    },
    Provider {
        modules: &[
            "Mathlib.RingTheory.Ideal.Basic",
            "Mathlib.RingTheory.Ideal.Quotient",
        ],
        init: init_ideal,
    },
    Provider {
        modules: &["Mathlib"],
        init: init_full_mathlib,
    },
    Provider {
        modules: &["Mathlib.MeasureTheory.Measure.MeasureSpace"],
        init: init_measure_theory,
    },
    Provider {
        modules: &["Mathlib.Combinatorics.Basic"],
        init: init_combinatorics,
    },
    Provider {
        modules: &["Mathlib.Combinatorics.SimpleGraph.Basic"],
        init: init_graph_theory,
    },
    Provider {
        modules: &["Mathlib.Data.ZMod.Basic"],
        init: init_zmod_basic,
    },
];

/// Track whether full Mathlib stubs have been initialized to avoid
/// duplicate declaration errors from multiple `import Mathlib.*` lines.
static MATHLIB_INIT: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);

pub fn init_prelude_for_module(env: &mut Environment, module: &str) -> Result<bool, ElabError> {
    // Try exact match first
    for provider in PRELUDE_PROVIDERS {
        if provider.provides().contains(&module) {
            // Skip duplicate-prone exact providers after full Mathlib init.
            // Narrow surface providers that are not part of the broad stub set
            // remain idempotent and must still run.
            if module == "Mathlib.Data.ZMod.Basic"
                || !MATHLIB_INIT.load(std::sync::atomic::Ordering::Relaxed)
            {
                provider.init(env)?;
            }
            return Ok(true);
        }
    }

    // Prefix fallback: any Mathlib.* import gets the full Mathlib stub set.
    // This is critical for arXiv formalization where LLMs import specific
    // Mathlib modules (e.g., Mathlib.AlgebraicGeometry.Scheme) that we don't
    // have individual providers for.
    if module.starts_with("Mathlib.") {
        if !MATHLIB_INIT.swap(true, std::sync::atomic::Ordering::Relaxed) {
            init_full_mathlib(env)?;
        }
        return Ok(true);
    }

    // Clean-native metaprogramming shim (plan decision 1): any `import Lean` /
    // `Lean.*` that was not resolved from real `.olean` artifacts gets the
    // opaque meta-type stand-ins so meta-referencing files elaborate. Idempotent
    // (`add_decl_if_absent`), so repeated `import Lean.*` lines are safe.
    if module == "Lean" || module.starts_with("Lean.") {
        init_lean_meta_prelude(env)?;
        return Ok(true);
    }

    Ok(false)
}

pub fn init_surface_prelude_after_olean(
    env: &mut Environment,
    module: &str,
) -> Result<bool, ElabError> {
    match module {
        "Mathlib.Algebra.MvPolynomial.Basic" => {
            register_semiring_mvpolynomial_instance(env)?;
            Ok(true)
        }
        "Mathlib.Data.ZMod.Basic" => {
            init_zmod_basic(env)?;
            Ok(true)
        }
        _ => Ok(false),
    }
}

/// Reset Mathlib init tracking (for tests).
#[cfg(test)]
pub fn reset_mathlib_init() {
    MATHLIB_INIT.store(false, std::sync::atomic::Ordering::Relaxed);
}
