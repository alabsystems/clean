// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Admit F* SMT-backed facts as `KernelVerified` via **ay proof reconstruction**.
//!
//! F* discharges most lemmas with Z3 and carries no CIC proof term — importing
//! one can only *assume* it. The rigorous alternative (see
//! `docs/MATHVERSE_FSTAR_IMPORT.md`): have `ay` (Trust's SMT backend) prove the
//! goal in proof-producing mode, then reconstruct its certificate into a real
//! Clean CIC proof term via `clean_auto::SmtBridge`. The solver leaves the
//! trusted base — only the kernel checks the term.
//!
//! This drives that pipeline for the decidable-theory subset F* proves by SMT
//! (linear integer order to start): each fact is a UNIVERSAL lemma
//! `∀ vars, hyps → conclusion`. We prove the open conclusion for fresh free
//! variables, then abstract every variable/hypothesis witness into a closed
//! theorem. The kernel is the arbiter — a fact ay cannot prove, or whose proof
//! is not bedrock, is simply not admitted. `Eq.refl` cannot prove these
//! (`Int.le` is a Prop, not a computation); ay can, and the result reduces to
//! the 3 foundational axioms.

use clean_auto::SmtBridge;
use clean_kernel::expr::FVarId;
use clean_kernel::{BinderInfo, Declaration, Environment, Expr, Name};

/// `Int` and the order/eq relation constructors.
fn int_ty() -> Expr {
    Expr::const_(Name::from_string("Int"), vec![])
}
fn int_rel(rel: &str, a: Expr, b: Expr) -> Expr {
    Expr::apps(Expr::const_(Name::from_string(rel), vec![]), [a, b])
}
fn eq_int(a: Expr, b: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Eq"),
            vec![clean_kernel::level::Level::succ(
                clean_kernel::level::Level::zero(),
            )],
        ),
        [int_ty(), a, b],
    )
}

/// A universal F* order lemma to re-prove via ay: `∀ (v0..vn : Int), h0 → … → C`.
pub struct AyFact {
    /// Clean theorem name.
    pub name: &'static str,
    /// The F* lemma this mirrors.
    pub fstar: &'static str,
    /// Number of universally-quantified `Int` variables.
    pub n_vars: usize,
    /// Given the variable fvars, return `(hypothesis props, conclusion)`.
    pub build: fn(&[Expr]) -> (Vec<Expr>, Expr),
}

/// The catalog of decidable integer-order F* lemmas (all SMT-backed in F*).
pub fn ay_facts() -> Vec<AyFact> {
    vec![
        AyFact {
            name: "fstar_ay_int_le_refl",
            fstar: "val le_refl : a:int -> Lemma (a <= a)",
            n_vars: 1,
            build: |v| (vec![], int_rel("Int.le", v[0].clone(), v[0].clone())),
        },
        AyFact {
            name: "fstar_ay_int_le_trans",
            fstar: "val le_trans : a:int -> b:int -> c:int -> Lemma (requires a<=b /\\ b<=c) (ensures a<=c)",
            n_vars: 3,
            build: |v| {
                (
                    vec![
                        int_rel("Int.le", v[0].clone(), v[1].clone()),
                        int_rel("Int.le", v[1].clone(), v[2].clone()),
                    ],
                    int_rel("Int.le", v[0].clone(), v[2].clone()),
                )
            },
        },
        AyFact {
            name: "fstar_ay_int_le_antisymm",
            fstar: "val le_antisymm : a:int -> b:int -> Lemma (requires a<=b /\\ b<=a) (ensures a==b)",
            n_vars: 2,
            build: |v| {
                (
                    vec![
                        int_rel("Int.le", v[0].clone(), v[1].clone()),
                        int_rel("Int.le", v[1].clone(), v[0].clone()),
                    ],
                    eq_int(v[0].clone(), v[1].clone()),
                )
            },
        },
        AyFact {
            name: "fstar_ay_int_lt_trans",
            fstar: "val lt_trans : a:int -> b:int -> c:int -> Lemma (requires a<b /\\ b<c) (ensures a<c)",
            n_vars: 3,
            build: |v| {
                (
                    vec![
                        int_rel("Int.lt", v[0].clone(), v[1].clone()),
                        int_rel("Int.lt", v[1].clone(), v[2].clone()),
                    ],
                    int_rel("Int.lt", v[0].clone(), v[2].clone()),
                )
            },
        },
        AyFact {
            name: "fstar_ay_int_lt_irrefl",
            fstar: "val lt_irrefl : a:int -> Lemma (~(a < a))",
            n_vars: 1,
            build: |v| {
                (
                    vec![int_rel("Int.lt", v[0].clone(), v[0].clone())],
                    Expr::const_(Name::from_string("False"), vec![]),
                )
            },
        },
        AyFact {
            name: "fstar_ay_int_le_of_lt",
            fstar: "val le_of_lt : a:int -> b:int -> Lemma (requires a<b) (ensures a<=b)",
            n_vars: 2,
            build: |v| {
                (
                    vec![int_rel("Int.lt", v[0].clone(), v[1].clone())],
                    int_rel("Int.le", v[0].clone(), v[1].clone()),
                )
            },
        },
        AyFact {
            name: "fstar_ay_int_lt_of_lt_of_le",
            fstar: "val lt_of_lt_of_le : a:int -> b:int -> c:int -> Lemma (requires a<b /\\ b<=c) (ensures a<c)",
            n_vars: 3,
            build: |v| {
                (
                    vec![
                        int_rel("Int.lt", v[0].clone(), v[1].clone()),
                        int_rel("Int.le", v[1].clone(), v[2].clone()),
                    ],
                    int_rel("Int.lt", v[0].clone(), v[2].clone()),
                )
            },
        },
        AyFact {
            name: "fstar_ay_int_lt_of_le_of_lt",
            fstar: "val lt_of_le_of_lt : a:int -> b:int -> c:int -> Lemma (requires a<=b /\\ b<c) (ensures a<c)",
            n_vars: 3,
            build: |v| {
                (
                    vec![
                        int_rel("Int.le", v[0].clone(), v[1].clone()),
                        int_rel("Int.lt", v[1].clone(), v[2].clone()),
                    ],
                    int_rel("Int.lt", v[0].clone(), v[2].clone()),
                )
            },
        },
        AyFact {
            name: "fstar_ay_int_eq_trans",
            fstar: "val eq_trans : a:int -> b:int -> c:int -> Lemma (requires a==b /\\ b==c) (ensures a==c)",
            n_vars: 3,
            build: |v| {
                (
                    vec![
                        eq_int(v[0].clone(), v[1].clone()),
                        eq_int(v[1].clone(), v[2].clone()),
                    ],
                    eq_int(v[0].clone(), v[2].clone()),
                )
            },
        },
        AyFact {
            name: "fstar_ay_int_eq_symm",
            fstar: "val eq_symm : a:int -> b:int -> Lemma (requires a==b) (ensures b==a)",
            n_vars: 2,
            build: |v| {
                (
                    vec![eq_int(v[0].clone(), v[1].clone())],
                    eq_int(v[1].clone(), v[0].clone()),
                )
            },
        },
        AyFact {
            name: "fstar_ay_int_le_refl_of_eq",
            fstar: "val le_of_eq : a:int -> b:int -> Lemma (requires a==b) (ensures a<=b)",
            n_vars: 2,
            build: |v| {
                (
                    vec![eq_int(v[0].clone(), v[1].clone())],
                    int_rel("Int.le", v[0].clone(), v[1].clone()),
                )
            },
        },
    ]
}

/// An ay-reconstructed F* theorem: its closed type and kernel proof term.
pub struct AyTheorem {
    pub name: String,
    pub fstar: String,
    pub type_: Expr,
    pub value: Expr,
}

/// Build an environment in which the Int order lemmas (`Int.le_refl`, …) are
/// kernel-checked BEDROCK theorems, so ay's reconstructed proofs reduce to the
/// 3 axioms rather than resting on an assumed lemma.
pub fn ay_env() -> Environment {
    let mut env = Environment::try_with_prelude().expect("kernel prelude");
    env.init_int_ord_lemmas()
        .expect("Int order lemmas register as bedrock theorems");
    let _ = env.init_trusted_ay();
    env
}

/// Prove one universal fact via ay and abstract the witnesses into a closed
/// theorem. Returns `None` if ay does not verify it (over-generate + filter).
pub fn prove_ay_fact(env: &Environment, fact: &AyFact) -> Option<AyTheorem> {
    // Fresh fvars: variables 1000+i, hypotheses 2000+j.
    let var_ids: Vec<FVarId> = (0..fact.n_vars)
        .map(|i| FVarId::new(1000 + i as u64))
        .collect();
    let vars: Vec<Expr> = var_ids.iter().map(|id| Expr::fvar(*id)).collect();
    let (hyp_props, conclusion) = (fact.build)(&vars);
    let hyp_ids: Vec<FVarId> = (0..hyp_props.len())
        .map(|j| FVarId::new(2000 + j as u64))
        .collect();

    // Solve: assert each hypothesis, prove the conclusion.
    let proof = {
        let mut bridge = SmtBridge::new(env);
        for (prop, id) in hyp_props.iter().zip(&hyp_ids) {
            bridge.add_hypothesis_with_fvar(prop, Some(*id)).ok()?;
        }
        bridge
            .prove(&conclusion)
            .ok()?
            .verified()?
            .proof_term()
            .clone()
    };

    // Telescope: ∀ vars, hyps → conclusion, with proof λ vars hyps. <pf>.
    // Binders outer→inner: vars then hyps. Abstract innermost-first (reverse),
    // each `abstract_fvar` binds one witness and shifts the rest.
    let binders: Vec<(FVarId, Expr)> = var_ids
        .iter()
        .map(|id| (*id, int_ty()))
        .chain(hyp_ids.iter().cloned().zip(hyp_props.iter().cloned()))
        .collect();

    let mut ty = conclusion;
    let mut val = proof;
    for (id, dom) in binders.iter().rev() {
        ty = Expr::pi(BinderInfo::Default, dom.clone(), ty.abstract_fvar(*id));
        val = Expr::lam(BinderInfo::Default, dom.clone(), val.abstract_fvar(*id));
    }

    Some(AyTheorem {
        name: fact.name.to_string(),
        fstar: fact.fstar.to_string(),
        type_: ty,
        value: val,
    })
}

/// Prove the whole catalog and admit each bedrock theorem into a shard.
/// Returns `(builder, admitted, skipped)`.
pub fn prove_and_admit_ay() -> (
    crate::export::kernel_export::KernelShardBuilder,
    usize,
    usize,
) {
    use crate::export::kernel_export::KernelShardBuilder;
    use crate::types::SourceSystem;

    let mut env = ay_env();
    let mut builder = KernelShardBuilder::new().with_source_system(SourceSystem::FStar);
    let (mut admitted, mut skipped) = (0usize, 0usize);

    for fact in ay_facts() {
        let Some(thm) = prove_ay_fact(&env, &fact) else {
            skipped += 1;
            continue;
        };
        let nm = Name::from_string(&thm.name);
        let decl = Declaration::Theorem {
            name: nm.clone(),
            level_params: vec![],
            type_: thm.type_.clone(),
            value: thm.value.clone(),
        };
        let accepted = env.add_decl(decl.clone()).is_ok();
        let bedrock = accepted && env.axiom_deps(&nm).map(|d| d.is_empty()).unwrap_or(false);
        if bedrock
            && builder
                .add_declaration(&decl, &["fstar", "ay", "smt", "bedrock"])
                .is_ok()
        {
            admitted += 1;
        } else {
            skipped += 1;
        }
    }
    (builder, admitted, skipped)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::shard::ShardReader;
    use crate::verify::incremental::verify_shard_incremental_with_env;

    /// The rigorous SMT→kernel→mathverse path end to end: ay proves the F* order
    /// lemmas, we admit them as a shard, and EVERY admitted theorem re-verifies
    /// as KernelVerified against a fresh prelude (100% — what is admitted is
    /// exactly what the kernel re-checks; the SMT solver is not trusted).
    #[test]
    fn ay_proven_fstar_facts_admitted_and_reverify() {
        let (builder, admitted, skipped) = prove_and_admit_ay();
        eprintln!("ay-admitted F* SMT facts: {admitted} admitted, {skipped} skipped");
        assert!(
            admitted >= 1,
            "at least the Int.le_refl lemma must admit via ay"
        );

        let bytes = builder.write_to_bytes().expect("serialize shard");
        let reader = ShardReader::from_bytes(&bytes).expect("reload shard");
        // Re-verify against the same prelude tier the proofs were built over:
        // the Int order lemmas (`Int.le_refl`/…) are bedrock prelude THEOREMS the
        // ay proofs cite, so the env must provide them (not in the shard).
        let report = verify_shard_incremental_with_env(&reader, ay_env());
        eprintln!(
            "  re-verify: {} KernelVerified, {} fallback, {} failed",
            report.kernel_verified, report.axiom_fallback, report.failed
        );
        assert_eq!(
            report.kernel_verified, admitted,
            "every ay-admitted F* proof must re-verify as KernelVerified"
        );
        assert_eq!(
            report.axiom_fallback, 0,
            "no admitted proof may mask a failed value"
        );
        assert_eq!(
            report.failed, 0,
            "no admitted proof may fail kernel re-check"
        );
    }
}
