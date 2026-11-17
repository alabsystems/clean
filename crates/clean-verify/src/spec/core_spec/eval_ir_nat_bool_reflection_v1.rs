// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0

//! A fixed production-Prelude package, independent of historical Crystal stages.
//! The original owners retain every statement and term. Production spells their
//! foundation-only Eq.cong through the existing identical EvalIR congruence bridge.

use crate::spec::{SpecError, Specification};
use clean_kernel::{ConstantKind, Declaration, Expr, Name};

#[cfg(test)]
#[path = "eval_ir_nat_bool_reflection_v1_tests.rs"]
mod tests;

const ROOTS: [&str; 5] = [
    "ir_bool_false_ne_true",
    "ir_nat_eqb_refl",
    "ir_nat_eqb_sound",
    "ir_bm_and_fst",
    "ir_bm_and_snd",
];

fn sources() -> impl Iterator<Item = (&'static str, &'static str)> + Clone {
    std::iter::once((
        "ir_bool_false_ne_true",
        super::eval_ir_lzd_fresh::bool_false_ne_true_source(),
    ))
    .chain(super::eval_ir_slot_lemmas::nat_eqb_reflexivity_sources())
    .chain(super::eval_ir_lzd_fresh::nat_eqb_soundness_sources())
    .chain(super::eval_ir_bmem_core::bool_and_elimination_sources())
}

fn check_stored(spec: &Specification, root: &str) -> Result<(), SpecError> {
    let name = Name::from_string(root);
    let definition = spec
        .get_definition(root)
        .ok_or_else(|| SpecError::UnknownDefinition(root.into()))?;
    let info = spec
        .env()
        .get_const(&name)
        .ok_or_else(|| SpecError::UnknownDefinition(root.into()))?;
    let value = info
        .value
        .as_ref()
        .ok_or_else(|| SpecError::MissingElaboration(root.into()))?;
    if info.kind != ConstantKind::Definition
        || !info.level_params.is_empty()
        || definition.is_axiom
        || definition.name != root
        || definition.elaborated_type.as_ref() != Some(&info.type_)
        || definition.elaborated_value.as_ref() != Some(value)
        || info.type_.has_fvar_quick()
        || value.has_fvar_quick()
    {
        return Err(SpecError::TypeError(format!(
            "Nat/Bool reflection root {root} has inconsistent or open stored endpoints"
        )));
    }
    spec.verify_definition(root)?;
    spec.env()
        .check_decl_readonly_strict(&Declaration::Definition {
            name: name.clone(),
            level_params: vec![],
            type_: info.type_.clone(),
            value: value.clone(),
            is_reducible: info.is_reducible,
        })
        .map_err(|error| SpecError::TypeError(format!("{root}: {error}")))?;
    for (kind, closure) in [
        ("axioms", spec.env().axiom_deps(&name)),
        (
            "foundational axioms",
            spec.env().foundational_axiom_deps(&name),
        ),
        ("trust markers", spec.env().trust_marker_deps(&name)),
    ] {
        let closure = closure.ok_or_else(|| SpecError::UnknownDefinition(root.into()))?;
        if !closure.is_empty() {
            return Err(SpecError::TypeError(format!(
                "Nat/Bool reflection root {root} depends on {kind}: {closure:?}"
            )));
        }
    }
    Ok(())
}

impl Specification {
    pub(crate) fn into_nat_bool_reflection_prelude_v1(mut self) -> Result<Self, SpecError> {
        // Only the fixed public factory calls this with its owned production Prelude.
        // Preflight before adding anything; failure never publishes a partial owner.
        for (name, _) in sources() {
            if self.get_definition(name).is_some()
                || self.env().get_const(&Name::from_string(name)).is_some()
            {
                return Err(SpecError::EnvError(format!(
                    "Nat/Bool reflection package name collision: {name}"
                )));
            }
        }
        // Normal kernel defaults, made explicit for the separately named profile.
        // No unlimited budget or inherited caller override is an admission path.
        self.env_mut().set_option(
            "maxHeartbeats".into(),
            Some(clean_kernel::tc::DEFAULT_HEARTBEAT_LIMIT.to_string()),
        );
        self.env_mut()
            .set_option("tcMaxCacheEntries".into(), Some("100000".into()));
        for (name, source) in sources() {
            self.add_recursive_def(
                &source.replace("Eq.cong", "ir_eq_cong"),
                &format!(
                    "{name}: {} (authoritative shared Nat/Bool source)",
                    crate::eval_ir::NAT_BOOL_REFLECTION_PRELUDE_PROFILE_V1
                ),
            )?;
            check_stored(&self, name)?;
        }
        let mut covered = std::collections::HashSet::new();
        for root in ROOTS {
            let info = self
                .env()
                .get_const(&Name::from_string(root))
                .ok_or_else(|| SpecError::UnknownDefinition(root.into()))?;
            let audit = self
                .env()
                .audit_certification(&info.type_, &Expr::const_str(root));
            if !audit.is_certified() {
                return Err(SpecError::TypeError(format!(
                    "Nat/Bool reflection root {root} failed strict rooted certification: {:?}",
                    audit.issues
                )));
            }
            covered.extend(audit.dependencies);
        }
        for (name, _) in sources() {
            if !covered.contains(&Name::from_string(name)) {
                return Err(SpecError::TypeError(format!(
                    "Nat/Bool reflection helper {name} is outside its audited root closure"
                )));
            }
        }
        Ok(self)
    }
}
