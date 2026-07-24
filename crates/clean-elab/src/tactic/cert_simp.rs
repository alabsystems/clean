// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Project-tuned certificate simplifier.
//!
//! `cert_simp` is a conservative wrapper around the proof-producing simp
//! engine. It selects certificate/list/arithmetic normalization declarations
//! explicitly, skips axiom-backed candidates by default, and reports remaining
//! certificate heads as blockers for downstream arithmetic tactics.

use clean_kernel::{ConstantKind, Expr, ExprKind, ExprVisitor, LevelVec, Name, ProofQuality};

use super::simp::{simp, simp_all_with_config};
use super::{ProofState, SimpConfig, TacticError, TacticResult};

const CERT_SIMP_BLOCKER_LIMIT: usize = 8;

const BASE_CERT_SIMP_CANDIDATES: &[&str] = &[
    "Nat.add_zero",
    "Nat.zero_add",
    "Nat.mul_one",
    "Nat.one_mul",
    "Nat.mul_zero",
    "Nat.zero_mul",
    "Nat.succ_eq_add_one",
    "Bool.not_not",
    "and_true",
    "true_and",
    "and_false",
    "false_and",
    "or_true",
    "true_or",
    "or_false",
    "false_or",
    "not_true",
    "not_false",
];

const LIST_CERT_SIMP_CANDIDATES: &[&str] = &[
    "List.append",
    "List.reverse",
    "List.map",
    "List.filter",
    "List.flatMap",
    "List.foldl",
    "List.foldr",
    "List.partition",
    "List.append_nil",
    "List.nil_append",
    "List.append_assoc",
    "List.map_nil",
    "List.map_cons",
    "List.map_append",
    "List.filter_nil",
    "List.filter_cons_true",
    "List.filter_cons_false",
    "List.filter_append",
    "List.flatMap_nil",
    "List.flatMap_cons",
    "List.flatMap_append",
    "List.foldl_nil",
    "List.foldl_cons",
    "List.foldr_nil",
    "List.foldr_cons",
    "Cert.List.sumByNat",
    "Cert.List.sumByNat_nil",
    "Cert.List.sumByNat_cons",
    "Cert.List.sumByNat_append",
    "Cert.List.sumByNat_map",
    "Cert.List.sumByInt",
    "Cert.List.sumByInt_nil",
    "Cert.List.sumByInt_cons",
    "Cert.List.sumByInt_append",
    "Cert.List.sumByInt_map",
    "Cert.List.sumByRat",
    "Cert.List.sumByRat_nil",
    "Cert.List.sumByRat_cons",
    "Cert.List.sumByRat_append",
    "Cert.List.sumByRat_map",
];

const SAT_PB_CERT_SIMP_CANDIDATES: &[&str] = &[
    "Cert.Syntax.evalLit",
    "Cert.Syntax.evalLit_pos",
    "Cert.Syntax.evalLit_neg",
    "Cert.Syntax.evalClause",
    "Cert.Syntax.evalClause_nil",
    "Cert.Syntax.evalClause_cons",
    "Cert.Syntax.evalCnf",
    "Cert.Syntax.evalCnf_nil",
    "Cert.Syntax.evalCnf_cons",
    "Cert.PB.linearEval",
    "Cert.PB.linearEval_nil",
    "Cert.PB.linearEval_cons",
    "Cert.PB.linearEval_append",
    "Cert.PB.checkBound",
    "Cert.PB.checkBound_true",
    "Cert.PB.checkBound_false",
    "Cert.Witness.accepted",
    "Cert.Witness.accepted_nil",
    "Cert.Witness.accepted_cons",
    "Cert.Witness.accepted_append",
    "VeriPB.satisfies_constraint",
    "VeriPB.cp_add",
    "VeriPB.cp_multiply",
    "VeriPB.cp_divide",
    "VeriPB.cp_saturate",
    "VeriPB.cp_weaken",
    "VeriPB.execute_step",
    "VeriPB.verify_certificate",
    "VeriPB.rup_check",
];

const NN_VERIFY_CERT_SIMP_CANDIDATES: &[&str] = &[
    "Fin.sum",
    "Fin.sum_zero",
    "Fin.sum_succ",
    "Fin.sum_add",
    "Fin.sum_zero_fn",
    "Fin.sum_smul",
    "Fin.sum_sub",
    "Fin.sum_single",
    "NNVec.dot",
    "NNMat.mulVec",
    "NNVerify.NNVec",
    "NNVerify.NNMat",
    "NNVerify.NNVec.add",
    "NNVerify.NNVec.smul",
    "NNVerify.NNVec.sub",
    "NNVerify.NNVec.dot",
    "NNVerify.NNVec.l1_norm",
    "NNVerify.NNMat.mulVec",
    "NNVerify.NNMat.transpose",
    "NNVerify.IntervalBounds",
    "NNVerify.IntervalBounds.mk",
    "NNVerify.IntervalBounds.contains",
    "NNVerify.IntervalBounds.subset",
    "NNVerify.IntervalBounds.width",
    "NNVerify.concrete_input",
    "NNVerify.linearEval",
    "NNVerify.checkBound",
    "NNVerify.linear_output",
    "NNVerify.ibp_linear_bounds",
    "NNVerify.ibp_relu_bounds",
    "NNVerify.eval_trace",
    "NNVerify.eval_certificate",
    "NNVerify.eval_matches_spec",
    "NNVerify.eval_within_bounds",
];

const CERTIFICATE_BLOCKER_HEADS: &[&str] = &[
    "List.filter",
    "List.flatMap",
    "List.foldl",
    "List.foldr",
    "List.partition",
    "Cert.List.sumByNat",
    "Cert.List.sumByInt",
    "Cert.List.sumByRat",
    "Cert.Syntax.evalLit",
    "Cert.Syntax.evalClause",
    "Cert.Syntax.evalCnf",
    "Cert.PB.linearEval",
    "Cert.PB.checkBound",
    "Cert.PB.boundHolds",
    "Cert.PB.evalTerm",
    "Cert.Witness.accepted",
    "Cert.Witness.accepts",
    "Fin.sum",
    "NNVerify.NNVec.dot",
    "NNVerify.NNVec.l1_norm",
    "NNVerify.NNMat.mulVec",
    "NNVerify.NNMat.transpose",
    "NNVerify.IntervalBounds",
    "NNVerify.IntervalBounds.mk",
    "NNVerify.IntervalBounds.contains",
    "NNVerify.IntervalBounds.subset",
    "NNVerify.IntervalBounds.width",
    "NNVerify.concrete_input",
    "NNVerify.linearEval",
    "NNVerify.checkBound",
    "NNVerify.linear_output",
    "NNVerify.ibp_linear_bounds",
    "NNVerify.ibp_relu_bounds",
    "NNVerify.eval_trace",
    "NNVerify.eval_certificate",
    "NNVerify.eval_matches_spec",
    "NNVerify.eval_within_bounds",
    "NNVerify.eval_trace_sound",
    "NNVerify.eval_certificate_complete",
    "VeriPB.satisfies_constraint",
    "VeriPB.cp_add",
    "VeriPB.cp_multiply",
    "VeriPB.cp_divide",
    "VeriPB.cp_saturate",
    "VeriPB.cp_weaken",
    "VeriPB.execute_step",
    "VeriPB.verify_certificate",
    "VeriPB.rup_check",
    "VeriPB.rup_sound",
    "VeriPB.step_sound",
    "VeriPB.verify_sound",
];

/// Domain-specific candidate packs that `cert_simp` may load.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum CertSimpCandidatePack {
    /// SAT, pseudo-Boolean, witness, LRAT/DRAT, and VeriPB certificate heads.
    SatPb,
    /// Neural-network verification and finite-sum certificate heads.
    NnVerify,
}

/// Configuration for `cert_simp`.
#[derive(Debug, Clone)]
pub struct CertSimpConfig {
    /// Maximum simplification steps before failing closed.
    pub max_steps: usize,
    /// Whether hypotheses are normalized together with the target.
    pub simplify_hypotheses: bool,
    /// Include SAT/PB certificate semantic declarations when present.
    pub include_sat_pb: bool,
    /// Include NN-verification/Fin.sum declarations when present.
    pub include_nn_verify: bool,
    /// Convert no-progress failures into certificate blocker diagnostics.
    pub diagnostics: bool,
}

impl CertSimpConfig {
    /// Select only the domain-specific candidate packs requested by a profile.
    ///
    /// This keeps the legacy config fields as the public compatibility surface,
    /// while giving profile adapters one place to avoid loading unrelated packs.
    pub(crate) fn with_candidate_packs(mut self, packs: &[CertSimpCandidatePack]) -> Self {
        self.include_sat_pb = false;
        self.include_nn_verify = false;
        for pack in packs {
            match pack {
                CertSimpCandidatePack::SatPb => self.include_sat_pb = true,
                CertSimpCandidatePack::NnVerify => self.include_nn_verify = true,
            }
        }
        self
    }

    fn includes_candidate_pack(&self, pack: CertSimpCandidatePack) -> bool {
        match pack {
            CertSimpCandidatePack::SatPb => self.include_sat_pb,
            CertSimpCandidatePack::NnVerify => self.include_nn_verify,
        }
    }
}

impl Default for CertSimpConfig {
    fn default() -> Self {
        Self {
            max_steps: 4000,
            simplify_hypotheses: true,
            include_sat_pb: true,
            include_nn_verify: true,
            diagnostics: true,
        }
    }
}

/// Normalize certificate/list expressions using the project lemma pack.
pub fn cert_simp(state: &mut ProofState) -> TacticResult {
    cert_simp_with_config(state, &CertSimpConfig::default())
}

/// Configurable implementation for tests and future command surfaces.
pub fn cert_simp_with_config(state: &mut ProofState, config: &CertSimpConfig) -> TacticResult {
    if state.current_goal().is_none() {
        return Err(TacticError::NoGoals);
    }

    let mut simp_config = SimpConfig::new();
    simp_config.max_steps = config.max_steps;
    simp_config.only = true;
    simp_config.use_hypotheses = config.simplify_hypotheses;
    simp_config.extra_lemmas = cert_simp_lemma_names(state, config);

    let result = if config.simplify_hypotheses {
        simp_all_with_config(state, simp_config)
    } else {
        simp(state, simp_config)
    };

    match result {
        Ok(()) => Ok(()),
        Err(TacticError::NoProgress { .. }) if config.diagnostics => {
            Err(TacticError::SearchExhausted {
                tactic: "cert_simp".to_string(),
                detail: cert_simp_blocker_detail(state),
            })
        }
        Err(TacticError::NoProgress { .. }) => Err(TacticError::NoProgress {
            tactic: "cert_simp".to_string(),
        }),
        Err(err) => Err(err),
    }
}

/// Names selected by `cert_simp` from the active environment.
///
/// Axiom-backed candidates are skipped: the tactic only selects existing
/// definitions with exposed bodies and constructive theorems.
pub(crate) fn cert_simp_lemma_names(state: &ProofState, config: &CertSimpConfig) -> Vec<String> {
    let mut out = Vec::new();
    push_existing_candidates(state, BASE_CERT_SIMP_CANDIDATES, &mut out);
    push_existing_candidates(state, LIST_CERT_SIMP_CANDIDATES, &mut out);
    if config.includes_candidate_pack(CertSimpCandidatePack::SatPb) {
        push_existing_candidates(state, SAT_PB_CERT_SIMP_CANDIDATES, &mut out);
    }
    if config.includes_candidate_pack(CertSimpCandidatePack::NnVerify) {
        push_existing_candidates(state, NN_VERIFY_CERT_SIMP_CANDIDATES, &mut out);
    }
    out
}

pub(crate) fn cert_simp_blocker_detail(state: &ProofState) -> String {
    let heads = cert_simp_blocker_heads(state, CERT_SIMP_BLOCKER_LIMIT);
    if heads.is_empty() {
        return "no progress; no certificate-specific blocker heads detected".to_string();
    }

    format!(
        "blocked certificate heads after normalization: {}; add checked cert_simp lemmas or normalize these definitions before arithmetic",
        heads.join(", ")
    )
}

pub(crate) fn cert_simp_blocker_heads(state: &ProofState, limit: usize) -> Vec<String> {
    let Some(goal) = state.current_goal() else {
        return Vec::new();
    };
    let mut visitor = CertBlockerVisitor {
        heads: Vec::new(),
        limit,
    };
    let target = state.metas.instantiate(&goal.target);
    visitor.visit_expr(&target);
    for decl in &goal.local_ctx {
        if visitor.heads.len() >= limit {
            break;
        }
        let ty = state.metas.instantiate(&decl.ty);
        visitor.visit_expr(&ty);
    }
    visitor.heads
}

fn push_existing_candidates(state: &ProofState, candidates: &[&str], out: &mut Vec<String>) {
    for candidate in candidates {
        let name = Name::from_string(candidate);
        let Some(decl) = state.env().get_const(&name) else {
            continue;
        };
        let eligible = match decl.kind {
            ConstantKind::Definition => decl.value.is_some(),
            ConstantKind::Theorem => {
                theorem_has_equality_conclusion(&decl.type_)
                    && matches!(
                        state.env().proof_quality(&name),
                        Some(ProofQuality::Constructive)
                    )
            }
            ConstantKind::Axiom | ConstantKind::Opaque => false,
        };
        if eligible {
            push_unique(out, (*candidate).to_string());
        }
    }
}

fn theorem_has_equality_conclusion(ty: &Expr) -> bool {
    match ty.kind() {
        ExprKind::Pi(_, _, body) => theorem_has_equality_conclusion(body),
        _ => {
            let head = ty.get_app_fn();
            let args = ty.get_app_args();
            matches!(head.kind(), ExprKind::Const(name, _) if name == &Name::from_string("Eq"))
                && args.len() == 3
        }
    }
}

fn push_unique(out: &mut Vec<String>, candidate: String) {
    if !out.iter().any(|existing| existing == &candidate) {
        out.push(candidate);
    }
}

fn is_certificate_blocker_head(name: &str) -> bool {
    CERTIFICATE_BLOCKER_HEADS.contains(&name)
}

struct CertBlockerVisitor {
    heads: Vec<String>,
    limit: usize,
}

impl ExprVisitor for CertBlockerVisitor {
    type Result = ();

    fn combine(&self, _a: (), _b: ()) {}

    fn visit_const(&mut self, name: &Name, _levels: &LevelVec) {
        if self.heads.len() >= self.limit {
            return;
        }
        let rendered = name.to_string();
        if is_certificate_blocker_head(&rendered) {
            push_unique(&mut self.heads, rendered);
        }
    }
}
