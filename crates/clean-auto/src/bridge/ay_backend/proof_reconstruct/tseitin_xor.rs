// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! XOR Tseitin clausification rule handlers for ay proof reconstruction.
//!
//! Reconstructs kernel proof terms for the 4 XOR Tseitin rules:
//! - `xor_pos1`: `{¬(xor a b), a, b}`
//! - `xor_pos2`: `{¬(xor a b), ¬a, ¬b}`
//! - `xor_neg1`: `{xor a b, a, ¬b}`
//! - `xor_neg2`: `{xor a b, ¬a, b}`
//!
//! clean translates `xor a b` as `(a ∧ ¬b) ∨ (¬a ∧ b)`, so the rules can be
//! reconstructed with `Classical.em`, `Or.rec`, `And.intro`, and conjunction
//! projections without introducing new trusted proof terms.

use ay_core::{ProofId, TermId};
use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Expr};

use super::expr_builders;
use super::trace::RuleView;
use super::{ReconstructResult, ReconstructionContext, ReconstructionError};
use crate::bridge::disjunction;

struct XorShapes {
    xor: Expr,
    not_a: Expr,
    not_b: Expr,
    left_conj: Expr,
    right_conj: Expr,
}

fn mk_false() -> Expr {
    Expr::const_(Name::from_string("False"), vec![])
}

fn mk_negation_pi(prop: &Expr) -> Expr {
    Expr::pi(BinderInfo::Default, prop.clone(), mk_false())
}

fn xor_shapes(a: &Expr, b: &Expr) -> XorShapes {
    let not_a = expr_builders::mk_not(a);
    let not_b = expr_builders::mk_not(b);
    let left_conj = expr_builders::mk_and(a, &not_b);
    let right_conj = expr_builders::mk_and(&not_a, b);
    let xor = expr_builders::mk_xor(a, b);
    XorShapes {
        xor,
        not_a,
        not_b,
        left_conj,
        right_conj,
    }
}

fn build_xor_from_a_not_b(
    shapes: &XorShapes,
    a: &Expr,
    a_proof: &Expr,
    not_b_proof: &Expr,
) -> Expr {
    let left_proof = disjunction::mk_and_intro(a, &shapes.not_b, a_proof, not_b_proof);
    disjunction::mk_or_inl(&shapes.left_conj, &shapes.right_conj, &left_proof)
}

fn build_xor_from_not_a_b(
    shapes: &XorShapes,
    b: &Expr,
    not_a_proof: &Expr,
    b_proof: &Expr,
) -> Expr {
    let right_proof = disjunction::mk_and_intro(&shapes.not_a, b, not_a_proof, b_proof);
    disjunction::mk_or_inr(&shapes.left_conj, &shapes.right_conj, &right_proof)
}

impl<'a> ReconstructionContext<'a> {
    /// Reconstruct an XOR Tseitin tautology clause.
    pub(super) fn reconstruct_xor_tautology(
        &mut self,
        rule: RuleView,
        clause: &[TermId],
        step_id: ProofId,
    ) -> ReconstructResult<Expr> {
        if clause.len() != 3 {
            return Err(ReconstructionError::UnsupportedStep {
                step_index: step_id.0,
                description: format!(
                    "xor tautology clause must have 3 literals, got {}",
                    clause.len()
                ),
            });
        }
        let trace = self
            .trace
            .as_ref()
            .ok_or(ReconstructionError::ProofNotAvailable)?;

        let xor_term = match rule {
            RuleView::XorPos1 | RuleView::XorPos2 => {
                trace
                    .as_not(clause[0])
                    .ok_or_else(|| ReconstructionError::UnsupportedStep {
                        step_index: step_id.0,
                        description: "xor_pos: first literal is not a negation".to_string(),
                    })?
            }
            RuleView::XorNeg1 | RuleView::XorNeg2 => clause[0],
            _ => unreachable!("non-xor rule in xor reconstruction"),
        };
        let (name, args) =
            trace
                .as_named_app(xor_term)
                .ok_or_else(|| ReconstructionError::UnsupportedStep {
                    step_index: step_id.0,
                    description: "xor clause source is not an application".to_string(),
                })?;
        if name != "xor" || args.len() != 2 {
            return Err(ReconstructionError::UnsupportedStep {
                step_index: step_id.0,
                description: "xor clause source is not a binary xor application".to_string(),
            });
        }

        let clause_props = self.translate_clause_props(clause)?;
        let a_prop = self.translate_term(args[0])?;
        let b_prop = self.translate_term(args[1])?;
        let clause_type = disjunction::or_chain_type(&clause_props);

        let proof = match rule {
            RuleView::XorPos1 => {
                Self::build_xor_pos1(&a_prop, &b_prop, &clause_props, &clause_type)
            }
            RuleView::XorPos2 => {
                Self::build_xor_pos2(&a_prop, &b_prop, &clause_props, &clause_type)
            }
            RuleView::XorNeg1 => {
                Self::build_xor_neg1(&a_prop, &b_prop, &clause_props, &clause_type)
            }
            RuleView::XorNeg2 => {
                Self::build_xor_neg2(&a_prop, &b_prop, &clause_props, &clause_type)
            }
            _ => unreachable!("non-xor rule in xor proof builder"),
        };

        Ok(proof)
    }

    fn build_xor_pos1(a: &Expr, b: &Expr, clause_props: &[Expr], clause_type: &Expr) -> Expr {
        let shapes = xor_shapes(a, b);
        let not_xor = mk_negation_pi(&shapes.xor);

        let em_xor = disjunction::mk_classical_em(&shapes.xor);
        let motive_em = disjunction::mk_constant_or_motive(&shapes.xor, &not_xor, clause_type);
        let motive_xor =
            disjunction::mk_constant_or_motive(&shapes.left_conj, &shapes.right_conj, clause_type);

        let f_inl_xor = Expr::lam(
            BinderInfo::Default,
            shapes.left_conj.clone(),
            disjunction::inject_into_or_chain(
                clause_props,
                1,
                disjunction::mk_and_left(&Expr::bvar(0)),
            ),
        );
        let f_inr_xor = Expr::lam(
            BinderInfo::Default,
            shapes.right_conj.clone(),
            disjunction::inject_into_or_chain(
                clause_props,
                2,
                disjunction::mk_and_right(&Expr::bvar(0)),
            ),
        );
        let xor_case = disjunction::mk_or_rec(
            &shapes.left_conj,
            &shapes.right_conj,
            &motive_xor,
            &f_inl_xor,
            &f_inr_xor,
            &Expr::bvar(0),
        );
        let f_inl_em = Expr::lam(BinderInfo::Default, shapes.xor.clone(), xor_case);
        let f_inr_em = Expr::lam(
            BinderInfo::Default,
            not_xor.clone(),
            disjunction::inject_into_or_chain(clause_props, 0, Expr::bvar(0)),
        );

        disjunction::mk_or_rec(
            &shapes.xor,
            &not_xor,
            &motive_em,
            &f_inl_em,
            &f_inr_em,
            &em_xor,
        )
    }

    fn build_xor_pos2(a: &Expr, b: &Expr, clause_props: &[Expr], clause_type: &Expr) -> Expr {
        let shapes = xor_shapes(a, b);
        let not_xor = mk_negation_pi(&shapes.xor);

        let em_xor = disjunction::mk_classical_em(&shapes.xor);
        let motive_em = disjunction::mk_constant_or_motive(&shapes.xor, &not_xor, clause_type);
        let motive_xor =
            disjunction::mk_constant_or_motive(&shapes.left_conj, &shapes.right_conj, clause_type);

        let f_inl_xor = Expr::lam(
            BinderInfo::Default,
            shapes.left_conj.clone(),
            disjunction::inject_into_or_chain(
                clause_props,
                2,
                disjunction::mk_and_right(&Expr::bvar(0)),
            ),
        );
        let f_inr_xor = Expr::lam(
            BinderInfo::Default,
            shapes.right_conj.clone(),
            disjunction::inject_into_or_chain(
                clause_props,
                1,
                disjunction::mk_and_left(&Expr::bvar(0)),
            ),
        );
        let xor_case = disjunction::mk_or_rec(
            &shapes.left_conj,
            &shapes.right_conj,
            &motive_xor,
            &f_inl_xor,
            &f_inr_xor,
            &Expr::bvar(0),
        );
        let f_inl_em = Expr::lam(BinderInfo::Default, shapes.xor.clone(), xor_case);
        let f_inr_em = Expr::lam(
            BinderInfo::Default,
            not_xor.clone(),
            disjunction::inject_into_or_chain(clause_props, 0, Expr::bvar(0)),
        );

        disjunction::mk_or_rec(
            &shapes.xor,
            &not_xor,
            &motive_em,
            &f_inl_em,
            &f_inr_em,
            &em_xor,
        )
    }

    fn build_xor_neg1(a: &Expr, b: &Expr, clause_props: &[Expr], clause_type: &Expr) -> Expr {
        let shapes = xor_shapes(a, b);
        let not_a_pi = mk_negation_pi(a);
        let not_b_pi = mk_negation_pi(b);

        let em_a = disjunction::mk_classical_em(a);
        let motive_a = disjunction::mk_constant_or_motive(a, &not_a_pi, clause_type);
        let f_inl_a = Expr::lam(
            BinderInfo::Default,
            a.clone(),
            disjunction::inject_into_or_chain(clause_props, 1, Expr::bvar(0)),
        );

        let em_b = disjunction::mk_classical_em(b);
        let motive_b = disjunction::mk_constant_or_motive(b, &not_b_pi, clause_type);
        let f_inl_b = Expr::lam(
            BinderInfo::Default,
            b.clone(),
            disjunction::inject_into_or_chain(
                clause_props,
                0,
                build_xor_from_not_a_b(&shapes, b, &Expr::bvar(1), &Expr::bvar(0)),
            ),
        );
        let f_inr_b = Expr::lam(
            BinderInfo::Default,
            not_b_pi.clone(),
            disjunction::inject_into_or_chain(clause_props, 2, Expr::bvar(0)),
        );
        let inner = disjunction::mk_or_rec(b, &not_b_pi, &motive_b, &f_inl_b, &f_inr_b, &em_b);
        let f_inr_a = Expr::lam(BinderInfo::Default, not_a_pi.clone(), inner);

        disjunction::mk_or_rec(a, &not_a_pi, &motive_a, &f_inl_a, &f_inr_a, &em_a)
    }

    fn build_xor_neg2(a: &Expr, b: &Expr, clause_props: &[Expr], clause_type: &Expr) -> Expr {
        let shapes = xor_shapes(a, b);
        let not_a_pi = mk_negation_pi(a);
        let not_b_pi = mk_negation_pi(b);

        let em_b = disjunction::mk_classical_em(b);
        let motive_b = disjunction::mk_constant_or_motive(b, &not_b_pi, clause_type);
        let f_inl_b = Expr::lam(
            BinderInfo::Default,
            b.clone(),
            disjunction::inject_into_or_chain(clause_props, 2, Expr::bvar(0)),
        );

        let em_a = disjunction::mk_classical_em(a);
        let motive_a = disjunction::mk_constant_or_motive(a, &not_a_pi, clause_type);
        let f_inl_a = Expr::lam(
            BinderInfo::Default,
            a.clone(),
            disjunction::inject_into_or_chain(
                clause_props,
                0,
                build_xor_from_a_not_b(&shapes, a, &Expr::bvar(0), &Expr::bvar(1)),
            ),
        );
        let f_inr_a = Expr::lam(
            BinderInfo::Default,
            not_a_pi.clone(),
            disjunction::inject_into_or_chain(clause_props, 1, Expr::bvar(0)),
        );
        let inner = disjunction::mk_or_rec(a, &not_a_pi, &motive_a, &f_inl_a, &f_inr_a, &em_a);
        let f_inr_b = Expr::lam(BinderInfo::Default, not_b_pi.clone(), inner);

        disjunction::mk_or_rec(b, &not_b_pi, &motive_b, &f_inl_b, &f_inr_b, &em_b)
    }
}
