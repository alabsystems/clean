// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! B101: elaborator-session homogeneous→heterogeneous bridge instances.
//!
//! Lean core ships `instHAdd [Add α] : HAdd α α α` (and `instHMul`,
//! `instHSub`, …), which is what makes a USER `instance : Add X` reachable
//! through `+` — the operator desugars to `HAdd.hAdd`, whose `[HAdd α α α]`
//! goal the bridge discharges by recursing into `[Add α]`. Clean's kernel
//! prelude ships only the directly-registered monomorphic instances
//! (`instHAddNat`, `instHAddInt`, …), so a user `Add X` instance never
//! reached its operator: `(v1 + v2)` failed with
//! `FailedToSynthesizeInstance { goal: "HAdd X X X" }` (r92
//! `ev_defs_add_instance_operator`).
//!
//! This seed registers the missing bridges into the SESSION environment as
//! real, kernel-checked definitions (`Environment::add_decl` — the checked
//! path — typechecks the value against the type; nothing is trusted):
//!
//! ```text
//! instHAdd.{u} : {α : Type u} → [inst : Add α] → HAdd α α α :=
//!   fun {α} [inst] => HAdd.mk α α α (Add.add α inst)
//! ```
//!
//! Engagement gates:
//! - The bridges register at priority [`BRIDGE_INSTANCE_PRIORITY`] (50),
//!   strictly below `DEFAULT_INSTANCE_PRIORITY` (100): priority dominates
//!   `candidate_order`, so every directly-registered monomorphic instance
//!   (`instHAddNat`, …) is tried first and builtin arithmetic elaborates
//!   byte-identically.
//! - Each bridge seeds only when its instance constant is ABSENT and every
//!   ingredient constant is PRESENT: a genuine imported `instHAdd` (olean
//!   lane) or a user redefinition is never clobbered, and import-suppressed
//!   preludes (no `Add.add`) are left untouched.
//!
//! Sibling coverage (B101): `Add`/`Mul`/`Sub` land. `Div`/`Mod` are NOT
//! seeded as instances: since 2026-09-30 the default kernel prelude has the
//! `Div` / `Mod` classes and Lean's `instHDiv` / `instHMod` constants
//! (`clean-kernel` `env/lean_arith_bridges.rs`, where Lean's floor lemmas are
//! stated through them), but registering the division bridge with the
//! resolver is a separate change to what `/` elaborates to, and this seed does
//! not make it. `x / y` over a user carrier stays the loud
//! `FailedToSynthesizeInstance { goal: "HDiv …" }`. `Neg` needs no bridge:
//! unary `-` elaborates through `Neg.neg` directly and the kernel prelude
//! already registers `Neg` as a class.
//!
//! Where the kernel prelude already DEFINES a bridge constant (it defines all
//! five since 2026-09-30), this seed only REGISTERS it, at the same priority.

use clean_kernel::{BinderInfo, Declaration, Environment, Expr, KernelInstanceInfo, Level, Name};

/// Is this `add_decl` rejection a RESOURCE limit rather than a statement about
/// the declaration?
///
/// `HeartbeatExceeded` (this type checker ran out of its own fuel) and
/// `DeclarationBudgetExhausted` (the caller's ambient per-declaration budget
/// ran out — `clean check --decl-budget`) both mean "the check did not
/// finish". Neither means the bridge is ill-typed, so neither may trip the
/// shape assertion below.
fn is_resource_limit(err: &clean_kernel::EnvError) -> bool {
    matches!(
        err,
        clean_kernel::EnvError::TypeCheckFailed {
            source: clean_kernel::KernelTypeError::HeartbeatExceeded { .. }
                | clean_kernel::KernelTypeError::DeclarationBudgetExhausted { .. },
            ..
        }
    )
}

/// Priority for the seeded bridge instances: strictly below
/// `clean_kernel::DEFAULT_INSTANCE_PRIORITY` (100), so the prelude's
/// directly-registered monomorphic instances always win their carriers.
const BRIDGE_INSTANCE_PRIORITY: u32 = 50;

/// One homogeneous→heterogeneous bridge (Lean core's `instH*` shape).
struct BridgeSpec {
    /// Bridge instance constant, e.g. `instHAdd`.
    inst_name: &'static str,
    /// Heterogeneous class, e.g. `HAdd` (3 params, levels `{u, v, w}`).
    hetero_class: &'static str,
    /// Heterogeneous class constructor, e.g. `HAdd.mk`.
    hetero_ctor: &'static str,
    /// Homogeneous class, e.g. `Add` (1 param, level `{u}`).
    homog_class: &'static str,
    /// Homogeneous method projection, e.g. `Add.add`.
    homog_method: &'static str,
}

/// The bridges the kernel prelude supports today (see module docs for the
/// `Div`/`Neg` descope rationale).
const BRIDGES: &[BridgeSpec] = &[
    BridgeSpec {
        inst_name: "instHAdd",
        hetero_class: "HAdd",
        hetero_ctor: "HAdd.mk",
        homog_class: "Add",
        homog_method: "Add.add",
    },
    BridgeSpec {
        inst_name: "instHMul",
        hetero_class: "HMul",
        hetero_ctor: "HMul.mk",
        homog_class: "Mul",
        homog_method: "Mul.mul",
    },
    BridgeSpec {
        inst_name: "instHSub",
        hetero_class: "HSub",
        hetero_ctor: "HSub.mk",
        homog_class: "Sub",
        homog_method: "Sub.sub",
    },
];

/// Seed every supported bridge into `env`. Idempotent and cheap after the
/// first call (one constant lookup per bridge).
pub(crate) fn seed_hetero_bridges(env: &mut Environment) {
    for spec in BRIDGES {
        seed_bridge(env, spec);
    }
}

/// Seed one bridge. Skips (leaving today's loud synthesis failure intact)
/// when the bridge constant already exists or an ingredient is missing.
fn seed_bridge(env: &mut Environment, spec: &BridgeSpec) {
    let inst_name = Name::from_string(spec.inst_name);
    if let Some(existing) = env.get_const(&inst_name) {
        // Since 2026-09-30 the DEFAULT kernel prelude defines Lean's bridge
        // constants itself (`clean-kernel` `env/lean_arith_bridges.rs`: Lean's
        // floor lemmas are stated through them) but does not register them
        // as instances. Register exactly that constant, at exactly the
        // priority this seed always used, so user `Add`/`Mul`/`Sub` instances
        // keep reaching their operators. Anything else of that name — an
        // imported bridge already registered, or a user declaration of a
        // different shape — is left alone, as before.
        let registered = env.is_instance(&inst_name);
        let kernel_bridge = existing.type_ == bridge_type(spec);
        if !registered && kernel_bridge {
            env.register_instance(KernelInstanceInfo {
                name: inst_name,
                class_name: Name::from_string(spec.hetero_class),
                priority: BRIDGE_INSTANCE_PRIORITY,
                type_: None,
                value: None,
            });
        }
        return;
    }
    let ingredients = [
        spec.hetero_class,
        spec.hetero_ctor,
        spec.homog_class,
        spec.homog_method,
    ];
    if ingredients
        .iter()
        .any(|c| env.get_const(&Name::from_string(c)).is_none())
    {
        return;
    }

    let u = Level::param(Name::from_string("u"));
    let type_u = Expr::sort(Level::succ(u.clone()));
    // `Homog α` with `α` at de Bruijn depth `alpha_idx`.
    let homog_alpha = |alpha_idx: u32| {
        Expr::app(
            Expr::const_(Name::from_string(spec.homog_class), vec![u.clone()]),
            Expr::bvar(alpha_idx),
        )
    };
    // `Hetero.{u,u,u} α α α` / `Hetero.mk.{u,u,u} α α α` heads.
    let hetero_levels = vec![u.clone(), u.clone(), u.clone()];
    let hetero_alpha3 = |head: &str| {
        Expr::apps(
            Expr::const_(Name::from_string(head), hetero_levels.clone()),
            [Expr::bvar(1), Expr::bvar(1), Expr::bvar(1)],
        )
    };

    let type_ = bridge_type(spec);
    // fun {α} [inst] => Hetero.mk α α α (Homog.method α inst)
    let method_call = Expr::apps(
        Expr::const_(Name::from_string(spec.homog_method), vec![u.clone()]),
        [Expr::bvar(1), Expr::bvar(0)],
    );
    let value = Expr::lam(
        BinderInfo::Implicit,
        type_u,
        Expr::lam(
            BinderInfo::InstImplicit,
            homog_alpha(0),
            Expr::app(hetero_alpha3(spec.hetero_ctor), method_call),
        ),
    );

    // KERNEL-CHECKED registration: `add_decl` typechecks the bridge value
    // against its type. A rejection means a co-tenant reshaped the prelude
    // classes; the bridge is then NOT registered and operator synthesis
    // keeps failing with today's loud `FailedToSynthesizeInstance`.
    let added = env.add_decl(Declaration::Definition {
        name: inst_name.clone(),
        level_params: vec![Name::from_string("u")],
        type_,
        value,
        is_reducible: true,
    });
    // …but a RESOURCE-LIMIT rejection is not that. The assertion's subject is
    // the SHAPE of the prelude classes; a spent heartbeat or a spent ambient
    // per-declaration budget says nothing about shape, and firing on one turns
    // a legitimate `clean check --decl-budget <small>` into a debug-build
    // panic. The production path below is already correct for both cases: the
    // bridge is skipped, and the seed is idempotent and retries on the next
    // declaration.
    debug_assert!(
        added.is_ok() || added.as_ref().err().is_some_and(is_resource_limit),
        "B101 hetero bridge {} failed kernel check: {:?}",
        spec.inst_name,
        added.err()
    );
    if added.is_err() {
        return;
    }

    env.register_instance(KernelInstanceInfo {
        name: inst_name,
        class_name: Name::from_string(spec.hetero_class),
        priority: BRIDGE_INSTANCE_PRIORITY,
        type_: None,
        value: None,
    });
}

/// `{α : Type u} → [inst : Homog α] → Hetero α α α` — Lean's bridge type.
fn bridge_type(spec: &BridgeSpec) -> Expr {
    let u = Level::param(Name::from_string("u"));
    let type_u = Expr::sort(Level::succ(u.clone()));
    let homog = Expr::app(
        Expr::const_(Name::from_string(spec.homog_class), vec![u.clone()]),
        Expr::bvar(0),
    );
    let hetero = Expr::apps(
        Expr::const_(
            Name::from_string(spec.hetero_class),
            vec![u.clone(), u.clone(), u],
        ),
        [Expr::bvar(1), Expr::bvar(1), Expr::bvar(1)],
    );
    Expr::pi(
        BinderInfo::Implicit,
        type_u,
        Expr::pi(BinderInfo::InstImplicit, homog, hetero),
    )
}
