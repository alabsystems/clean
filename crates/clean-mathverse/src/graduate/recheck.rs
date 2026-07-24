// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The single kernel-recheck trust verdict.
//!
//! [`recheck_and_classify`] is the ONE definition of "replay a declaration
//! into a kernel environment and classify its trust": it runs the real
//! `Environment::add_decl` path (the only honest road to a `KernelVerified`
//! verdict — the kernel type-checks the declaration WITH its value) and then
//! the transitive axiom closure (`Environment::axiom_deps`, the same walk
//! `proof_quality` is built on). The graduation intake gate
//! ([`super::intake`]) and the `addDecl` RPC are meant to share this verdict
//! rather than each re-spelling the `add_decl` → closure sequence.
//!
//! The verdict is FACTS, not policy: it reports whether the value
//! type-checked and the transitive non-foundational ("domain") axiom set.
//! Callers apply their own policy on top (the intake gate REJECTS a
//! candidate whose closure is non-empty; a carried definition RECORDS the
//! same closure but lets the dependent candidate's own check do the
//! rejecting). [`RecheckVerdict::is_foundational`] is the shared predicate
//! for the strict `kernel_verified` finish line.
//!
//! Fail-closed: any kernel rejection (`add_decl` error), a theorem the kernel
//! cannot classify after a successful add (no proof value / not-a-theorem /
//! vanished constant), or a missing post-add constant is an error, never a
//! silent pass.

use clean_kernel::{Declaration, EnvError, Environment, Name, ProofQuality};

/// What `add_decl` produced before the closure walk: the proof value
/// type-checked against the stated type. Always `true` on the success path
/// (the kernel would have errored otherwise) — carried for symmetry with the
/// gate's [`super::record::KernelFacts::value_typechecked`] field, which the
/// RPC and the gate both stamp from this.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct KernelCheck {
    pub(crate) value_typechecked: bool,
}

/// The kernel-recheck trust verdict for one declaration: the kernel facts
/// plus the transitive NON-foundational axiom closure. Empty closure ⇔ the
/// transitive closure is `⊆ FOUNDATIONAL_AXIOMS` (the `kernel_verified`
/// finish line). Domain axioms are returned sorted (stable for records and
/// reject messages).
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct RecheckVerdict {
    /// The kernel's `add_decl` outcome (value type-checked).
    pub(crate) kernel: KernelCheck,
    /// Transitive non-foundational axioms reachable from the declaration's
    /// type and value, sorted. Empty ⇔ foundational-only.
    pub(crate) domain_axioms: Vec<String>,
}

impl RecheckVerdict {
    /// The shared `kernel_verified` predicate: the value type-checked AND the
    /// transitive axiom closure is foundational-only.
    pub(crate) fn is_foundational(&self) -> bool {
        self.kernel.value_typechecked && self.domain_axioms.is_empty()
    }
}

/// Why a kernel re-check did not yield a clean verdict. Fail-closed: the gate
/// turns each variant into a reject reason; the RPC surfaces it as an error.
#[derive(Clone, Debug, thiserror::Error)]
pub(crate) enum RecheckError {
    /// `Environment::add_decl` rejected the declaration (type error, missing
    /// dependency, duplicate, etc.). The kernel's own message is preserved.
    #[error("kernel-rejected: {0}")]
    KernelRejected(String),

    /// `add_decl` succeeded but the constant is not present afterwards, or the
    /// kernel cannot classify the theorem's proof quality (no stored proof
    /// value / not-a-theorem). Should be unreachable on the success path;
    /// treated as a kernel rejection rather than a silent pass.
    #[error("kernel-rejected: unexpected proof quality after add_decl: {0}")]
    Unclassifiable(String),
}

impl RecheckError {
    /// The reject-reason string the intake gate records. Both variants are
    /// `kernel-rejected: …` (the gate's existing prefix), so callers can stamp
    /// `entry.reject_reason = Some(err.reject_reason())` verbatim.
    pub(crate) fn reject_reason(&self) -> String {
        self.to_string()
    }
}

/// Replay `decl` into `env` via the real kernel `add_decl` path, then classify
/// its transitive axiom closure. The single source of the kernel-recheck trust
/// verdict shared by the graduation intake gate and the `addDecl` RPC.
///
/// On success the declaration is registered in `env` (so later dependents
/// type-check and closure walks see through it) and the returned verdict
/// reports the transitive non-foundational axiom set. On any kernel rejection
/// — or, for a theorem, an inability to classify it after a successful add —
/// returns [`RecheckError`] WITHOUT having left a half-classified verdict.
///
/// Behaviour is identical for definitions, opaques, axioms, and theorems: the
/// closure is computed with `axiom_deps` uniformly. The theorem-only
/// classification fork (`ProofQuality::Constructive` / `AxiomDependent`) is
/// applied only to detect the not-a-theorem / unchecked / vanished cases that
/// the intake gate already treats as kernel rejections, preserving the
/// pre-refactor behaviour exactly.
pub(crate) fn recheck_and_classify(
    env: &mut Environment,
    decl: Declaration,
) -> Result<RecheckVerdict, RecheckError> {
    let name = decl_name(&decl);
    let is_theorem = matches!(decl, Declaration::Theorem { .. });

    // Step 1: kernel re-check WITH the value — the only honest path to
    // KernelVerified. Any error fails closed.
    env.add_decl(decl)
        .map_err(|e: EnvError| RecheckError::KernelRejected(e.to_string()))?;

    // Step 2: transitive non-foundational axiom closure. For theorems, route
    // through `proof_quality` so the not-a-theorem / unchecked / vanished
    // cases stay kernel rejections (never silent passes); the
    // `Constructive` / `AxiomDependent` arms agree with `axiom_deps`.
    let domain_axioms = if is_theorem {
        match env.proof_quality(&name) {
            Some(ProofQuality::Constructive) => Vec::new(),
            Some(ProofQuality::AxiomDependent { axioms, .. }) => sorted_names(axioms.iter()),
            other => {
                return Err(RecheckError::Unclassifiable(format!("{other:?}")));
            }
        }
    } else {
        // Definitions / opaques / axioms: `proof_quality` would report
        // `NotATheorem`, so read the closure directly. `axiom_deps` returns
        // `None` only if the constant is absent — impossible right after a
        // successful add, but fail closed anyway.
        match env.axiom_deps(&name) {
            Some(deps) => sorted_names(deps.iter()),
            None => {
                return Err(RecheckError::Unclassifiable(
                    "axiom_deps: constant absent after add_decl".to_string(),
                ));
            }
        }
    };

    Ok(RecheckVerdict {
        kernel: KernelCheck {
            value_typechecked: true,
        },
        domain_axioms,
    })
}

/// The declaration's name, for the post-add closure query.
fn decl_name(decl: &Declaration) -> Name {
    match decl {
        Declaration::Axiom { name, .. }
        | Declaration::Definition { name, .. }
        | Declaration::Theorem { name, .. }
        | Declaration::Opaque { name, .. } => name.clone(),
    }
}

/// Sort a set of axiom names into a stable `Vec<String>`.
fn sorted_names<'a>(names: impl Iterator<Item = &'a Name>) -> Vec<String> {
    let mut out: Vec<String> = names.map(Name::to_string).collect();
    out.sort();
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::{BinderInfo, Expr};

    /// `fun (p : Prop) (h : p) => h : ∀ (p : Prop), p → p` — a closed,
    /// foundational-only proof.
    fn imp_self() -> Declaration {
        Declaration::Theorem {
            name: Name::from_string("Recheck.imp_self"),
            level_params: vec![],
            type_: Expr::pi(
                BinderInfo::Default,
                Expr::prop(),
                Expr::pi(BinderInfo::Default, Expr::bvar(0), Expr::bvar(1)),
            ),
            value: Expr::lam(
                BinderInfo::Default,
                Expr::prop(),
                Expr::lam(BinderInfo::Default, Expr::bvar(0), Expr::bvar(0)),
            ),
        }
    }

    /// `∀ (p q : Prop), p → p` — statement reserved for the domain axiom.
    fn axiom_type() -> Expr {
        Expr::pi(
            BinderInfo::Default,
            Expr::prop(),
            Expr::pi(
                BinderInfo::Default,
                Expr::prop(),
                Expr::pi(BinderInfo::Default, Expr::bvar(1), Expr::bvar(2)),
            ),
        )
    }

    #[test]
    fn test_recheck_and_classify_foundational_theorem_is_verdict_clean() {
        let mut env = Environment::new();
        let verdict =
            recheck_and_classify(&mut env, imp_self()).expect("foundational theorem must verify");
        assert!(verdict.kernel.value_typechecked);
        assert!(verdict.domain_axioms.is_empty());
        assert!(verdict.is_foundational());
    }

    #[test]
    fn test_recheck_and_classify_axiom_dependent_theorem_reports_domain_axiom() {
        let mut env = Environment::new();
        // Seed a domain axiom, then a theorem that cites it.
        env.add_decl(Declaration::Axiom {
            name: Name::from_string("Recheck.bad_axiom"),
            level_params: vec![],
            type_: axiom_type(),
        })
        .expect("axiom must kernel-check");
        let dependent = Declaration::Theorem {
            name: Name::from_string("Recheck.bad_dependent"),
            level_params: vec![],
            type_: axiom_type(),
            value: Expr::const_str("Recheck.bad_axiom"),
        };
        let verdict =
            recheck_and_classify(&mut env, dependent).expect("axiom-citing theorem still verifies");
        assert!(verdict.kernel.value_typechecked);
        assert_eq!(verdict.domain_axioms, vec!["Recheck.bad_axiom".to_string()]);
        assert!(!verdict.is_foundational());
    }

    #[test]
    fn test_recheck_and_classify_kernel_rejection_fails_closed() {
        let mut env = Environment::new();
        recheck_and_classify(&mut env, imp_self()).expect("first add verifies");
        // Re-adding the same name is a kernel rejection (duplicate).
        let err = recheck_and_classify(&mut env, imp_self())
            .expect_err("duplicate declaration must fail closed");
        assert!(matches!(err, RecheckError::KernelRejected(_)));
        assert!(
            err.reject_reason().starts_with("kernel-rejected:"),
            "reject reason keeps the gate's prefix: {}",
            err.reject_reason()
        );
    }

    #[test]
    fn test_recheck_and_classify_definition_uses_axiom_deps_closure() {
        let mut env = Environment::new();
        // A definition `id_prop : Prop → Prop := fun p => p` — foundational.
        let def = Declaration::Definition {
            name: Name::from_string("Recheck.id_prop"),
            level_params: vec![],
            type_: Expr::pi(BinderInfo::Default, Expr::prop(), Expr::prop()),
            value: Expr::lam(BinderInfo::Default, Expr::prop(), Expr::bvar(0)),
            is_reducible: false,
        };
        let verdict =
            recheck_and_classify(&mut env, def).expect("foundational definition must verify");
        assert!(verdict.kernel.value_typechecked);
        assert!(verdict.domain_axioms.is_empty());
        assert!(verdict.is_foundational());
    }
}
