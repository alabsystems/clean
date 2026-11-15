// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Authority for the cubical and directed layers' RESERVED heads
//! (`docs/issues/2026-09-26-kernel-native-fold-by-name.md`).
//!
//! The Kan, Glue, Σ, interval-connection and directed rules
//! (`tc/reduction/kan.rs`, `tc/reduction/directed.rs`, and the hcomp-system
//! rebuild in `tc/reduction/mod.rs`) recognise constants by NAME: `Sigma.elim`
//! over `Sigma.mk`, `Equiv.fwd` over `Equiv.mk`, `Cofib.and`, `System.cons`,
//! `I.min`, `Dir.homApp`, … Each rule is justified by the kernel's own axiom
//! for that name — the declarations its registrars install
//! (`register_kan_system_axioms`, `register_glue_axioms`,
//! `register_sigma_axioms`, `register_directed_axioms`) — and by nothing else.
//! A user `Sigma.elim := λ … => a0` over a user `Sigma.mk` got the Σ-iota
//! beside its own δ, identifying two opaque points.
//!
//! The rule for admitting the layer: every reserved name the environment
//! declares must be declared EXACTLY as the kernel's registrar declares it
//! (kind, universe parameters, type, value), and none may be an inductive, a
//! constructor or a recursor. A reserved name the environment does not declare
//! cannot occur in a term that type-checks, so it needs no check. An
//! environment that declares one differently gets no name-keyed cubical
//! computation at all: every gated rule stays stuck, and an hcomp system is
//! unparseable (which hcomp validation already treats as "no reduction will
//! consume it"). Soundness-monotone: it can only reject.

use std::cell::Cell;
use std::collections::HashMap;
use std::sync::{LazyLock, OnceLock};

use crate::env::{ConstantInfo, Environment};
use crate::mode::CleanMode;
use crate::name::Name;
use crate::tc::reduction::directed::{dir_names, register_directed_axioms};
use crate::tc::reduction::kan::{
    conn_names, glue_names, kan_names, register_glue_axioms, register_kan_system_axioms,
    register_sigma_axioms, sigma_names,
};

/// `Dir.degen2` (its `dir_names` static is test-only; the registrar installs
/// it in every build).
static DIR_DEGEN2: LazyLock<Name> = LazyLock::new(|| Name::from_string("Dir.degen2"));

/// Every name a cubical or directed rule recognises.
pub(crate) fn reserved_names() -> [&'static Name; 35] {
    [
        &kan_names::COFIB_TOP,
        &kan_names::COFIB_BOT,
        &kan_names::COFIB_EQ0,
        &kan_names::COFIB_EQ1,
        &kan_names::COFIB_AND,
        &kan_names::COFIB_OR,
        &kan_names::SYSTEM_CONS,
        &kan_names::SYSTEM_NIL,
        &glue_names::EQUIV,
        &glue_names::EQUIV_ID,
        &glue_names::EQUIV_FWD,
        &glue_names::EQUIV_BWD,
        &glue_names::EQUIV_MK,
        &glue_names::EQUIV_TO_IS_EQUIV,
        &glue_names::GLUE_SYS,
        &glue_names::GLUE_SYS_CONS,
        &glue_names::GLUE_SYS_NIL,
        &glue_names::GLUE,
        &glue_names::GLUE_INTRO,
        &glue_names::UNGLUE,
        &conn_names::I_MIN,
        &conn_names::I_MAX,
        &conn_names::I_NEG,
        &sigma_names::SIGMA,
        &sigma_names::SIGMA_MK,
        &sigma_names::SIGMA_ELIM,
        &dir_names::DIR_INTERVAL,
        &dir_names::DIR_I0,
        &dir_names::DIR_I1,
        &dir_names::DIR_LE,
        &dir_names::DIR_HOM,
        &dir_names::DIR_HOM_LAM,
        &dir_names::DIR_HOM_APP,
        &dir_names::DIR_HOM2,
        &DIR_DEGEN2,
    ]
}

/// The kernel registrars' declarations of the reserved names, built once per
/// process in a scratch Directed-mode environment (the mode that carries both
/// layers). `None` if a registrar fails, which admits nothing.
static CANONICAL: OnceLock<Option<HashMap<Name, ConstantInfo>>> = OnceLock::new();

thread_local! {
    /// Set while THIS thread builds [`CANONICAL`]. The registrars type-check
    /// their own declarations, which can reach a gated rule and so ask for the
    /// table being built; the environment asking is then the registrars'
    /// scratch environment (nothing else runs on this thread meanwhile), which
    /// holds exactly the kernel's declarations. Not a `LazyLock`: its
    /// initializer would re-enter its own cell and deadlock.
    static BUILDING: Cell<bool> = const { Cell::new(false) };
}

/// Holds [`BUILDING`] for one build and restores it on every exit, unwinding
/// included: a flag left set would admit every environment on this thread.
struct Building(bool);

impl Building {
    fn start() -> Self {
        Building(BUILDING.with(|b| b.replace(true)))
    }
}

impl Drop for Building {
    fn drop(&mut self) {
        BUILDING.with(|b| b.set(self.0));
    }
}

/// The canonical table, building it on first use.
fn canonical() -> Option<&'static HashMap<Name, ConstantInfo>> {
    if let Some(done) = CANONICAL.get() {
        return done.as_ref();
    }
    let built = {
        let _building = Building::start();
        // Built once per process and kept: a deadline the caller installed must
        // not cut the build short and leave `None` (which admits nothing) for
        // every later caller. The build is the kernel's own registrars, bounded
        // by construction.
        crate::tc::with_deadline_suspended(canonical_declarations)
    };
    // A racing thread may have stored an identical table first; keep either.
    CANONICAL.get_or_init(|| built).as_ref()
}

pub(crate) fn canonical_declarations() -> Option<HashMap<Name, ConstantInfo>> {
    let mut env = Environment::with_mode(CleanMode::Directed);
    register_kan_system_axioms(&mut env).ok()?;
    register_glue_axioms(&mut env).ok()?;
    register_sigma_axioms(&mut env).ok()?;
    register_directed_axioms(&mut env).ok()?;
    Some(
        reserved_names()
            .into_iter()
            .filter_map(|name| env.get_const(name).map(|c| (name.clone(), c.clone())))
            .collect(),
    )
}

/// Whether every reserved name `env` declares is the kernel's own declaration.
pub(crate) fn cubical_primitives_canonical(env: &Environment) -> bool {
    if BUILDING.with(Cell::get) {
        return true;
    }
    let Some(canonical) = canonical() else {
        return false;
    };
    reserved_names().into_iter().all(|name| {
        if env.get_inductive(name).is_some()
            || env.get_constructor(name).is_some()
            || env.get_recursor(name).is_some()
        {
            return false;
        }
        match env.get_const(name) {
            None => true,
            Some(entry) => canonical
                .get(name)
                .is_some_and(|canon| same_declaration(entry, canon)),
        }
    })
}

fn same_declaration(a: &ConstantInfo, b: &ConstantInfo) -> bool {
    a.kind == b.kind && a.level_params == b.level_params && a.type_ == b.type_ && a.value == b.value
}

#[cfg(test)]
#[path = "cubical_authority_tests.rs"]
mod tests;
