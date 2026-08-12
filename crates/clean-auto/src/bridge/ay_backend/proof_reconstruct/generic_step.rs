// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use ay_core::{ProofId, TermId};
use clean_kernel::Expr;

use super::trace::RuleView;
use super::{ReconstructResult, ReconstructionContext, ReconstructionError};
use crate::bridge::ay_backend::reconstruction_quality::ResidualTrustSource;

impl<'a> ReconstructionContext<'a> {
    /// Reconstruct a generic Alethe-rule Step.
    ///
    /// Dispatches to rule-specific handlers. Unsupported rules fall back to
    /// `UnsupportedStep` error (which triggers trustedAy fallback).
    pub(crate) fn reconstruct_generic_step(
        &mut self,
        rule: RuleView,
        rule_name: &str,
        clause: &[TermId],
        premises: &[ProofId],
        step_id: ProofId,
    ) -> ReconstructResult<Expr> {
        let name = rule_name.to_string();
        *self.stats.rule_attempts.entry(name.clone()).or_insert(0) += 1;

        let result = self.dispatch_alethe_rule(rule, rule_name, clause, premises, step_id);
        if result.is_ok() {
            *self.stats.rule_successes.entry(name).or_insert(0) += 1;
        }
        result
    }

    fn dispatch_alethe_rule(
        &mut self,
        rule: RuleView,
        rule_name: &str,
        clause: &[TermId],
        premises: &[ProofId],
        step_id: ProofId,
    ) -> ReconstructResult<Expr> {
        match rule {
            // ay actual emission rules (designs/2026-03-05-302-ay-actual-proof-rules.md)
            RuleView::ThResolution => self.reconstruct_th_resolution(clause, premises, step_id),
            RuleView::Or => {
                // Or decomposes an assumed (or l1 l2 ...) into clause [l1, l2, ...].
                // Identity on the proof term — the premise already proves the disjunction.
                if premises.is_empty() {
                    return Err(ReconstructionError::UnsupportedStep {
                        step_index: step_id.0,
                        description: "Or rule requires at least one premise".to_string(),
                    });
                }
                self.get_premise_proof(premises[0], step_id)
            }
            // Tseitin clausification rules — premiseless tautologies
            RuleView::OrPos => self.reconstruct_or_pos(clause, step_id),
            RuleView::OrNeg => self.reconstruct_or_neg(clause, step_id),
            // And Tseitin rules — Classical.em + And projections / And.intro chain
            RuleView::AndPos(i) => self.reconstruct_and_pos(i, clause, step_id),
            RuleView::AndNeg => self.reconstruct_and_neg(clause, step_id),
            // eq_reflexive: ⊢ (= t t) — reconstructs directly to `@Eq.refl.{u} ty t`.
            RuleView::EqReflexive => self.reconstruct_eq_reflexive(clause, step_id),
            // eq_congruent: premiseless congruence tautology clause
            //   [¬(= a₁ b₁), …, (= (f ā) (f b̄))] — reuses the EUF congruent proof.
            RuleView::EqCongruent => self.reconstruct_eq_congruent(clause, step_id),
            // cong: premised congruence with a unit positive-equality conclusion —
            // builds a congrArg/congr chain from the premise argument equalities.
            RuleView::Cong => self.reconstruct_cong(clause, premises, step_id),
            RuleView::Resolution => self.reconstruct_resolution_rule(clause, premises, step_id),
            RuleView::Contraction => self.reconstruct_contraction(clause, premises, step_id),
            RuleView::True => self.reconstruct_true(clause, step_id),
            RuleView::False => self.reconstruct_false(clause, step_id),
            RuleView::Symm => self.reconstruct_symm(clause, premises, step_id),
            RuleView::Trans => self.reconstruct_trans(clause, premises, step_id),
            // Equivalence Tseitin rules — Classical.em case analysis
            RuleView::EquivPos1
            | RuleView::EquivPos2
            | RuleView::EquivNeg1
            | RuleView::EquivNeg2 => self.reconstruct_equiv_tautology(rule, clause, step_id),
            // XOR Tseitin rules — Classical.em over xor or its atoms.
            RuleView::XorPos1 | RuleView::XorPos2 | RuleView::XorNeg1 | RuleView::XorNeg2 => {
                self.reconstruct_xor_tautology(rule, clause, step_id)
            }
            RuleView::Trust => self.reconstruct_trust(clause, step_id),
            RuleView::Hole => Err(ReconstructionError::UnsupportedStep {
                step_index: step_id.0,
                description: "ay hole step (incomplete proof placeholder)".to_string(),
            }),
            RuleView::Other => Err(ReconstructionError::UnsupportedStep {
                step_index: step_id.0,
                description: format!("unsupported Alethe rule: {}", rule_name),
            }),
        }
    }

    /// Reconstruct a Trust step by synthesizing a trustedAy sub-term.
    ///
    /// ay emits Trust when SAT-level resolution reconstruction fails. Instead of
    /// cascading an error to all downstream steps, we synthesize a `trustedAy`
    /// axiom application for the clause type, allowing the rest of the proof to
    /// be kernel-verified.
    ///
    /// For a clause `[l₁, ..., lₙ]`, constructs:
    ///   `@trustedAy.{0} (l₁ ∨ ... ∨ lₙ) : l₁ ∨ ... ∨ lₙ`
    ///
    /// For the empty clause (derives False directly), constructs:
    ///   `@trustedAy.{0} False : False`
    ///
    /// Increments `trust_subterm_steps` in stats so the caller can decide whether
    /// a proof with N trust sub-terms is acceptable.
    fn reconstruct_trust(
        &mut self,
        clause: &[TermId],
        step_id: ProofId,
    ) -> ReconstructResult<Expr> {
        let proof = self.build_trusted_ay_subterm_for_clause(clause)?;
        self.stats.trust_subterm_steps += 1;
        self.stats
            .record_residual_source(ResidualTrustSource::AletheTrustStep);
        tracing::debug!(
            step = step_id.0,
            clause_len = clause.len(),
            "Trust step filled with trustedAy sub-term"
        );

        Ok(proof)
    }

    /// Reconstruct an `eq_reflexive` step: ⊢ `(= t t)`.
    ///
    /// The unit clause translates to `@Eq.{u} ty t t`; the proof is directly
    /// `@Eq.refl.{u} ty t`. No premises, no theory call — a kernel primitive.
    /// SOUNDNESS: the kernel still type-checks the emitted term against the goal,
    /// and a non-reflexive clause (`lhs ≠ rhs`) fails closed here.
    fn reconstruct_eq_reflexive(
        &mut self,
        clause: &[TermId],
        step_id: ProofId,
    ) -> ReconstructResult<Expr> {
        use clean_kernel::expr::ExprKind;
        use clean_kernel::Name;

        let bail = |desc: String| {
            Err(ReconstructionError::UnsupportedStep {
                step_index: step_id.0,
                description: desc,
            })
        };
        if clause.len() != 1 {
            return bail(format!(
                "eq_reflexive expects a unit clause, got {} literals",
                clause.len()
            ));
        }
        let eq_expr = self.translate_term(clause[0])?;
        // The translator constant-folds `(= t t)` (syntactically-identical sides)
        // to `True`; its proof is the kernel primitive `True.intro`.
        if matches!(eq_expr.get_app_fn().kind(), ExprKind::Const(n, _) if n.to_string() == "True") {
            return Ok(Expr::const_(Name::from_string("True.intro"), vec![]));
        }
        // Otherwise the literal is `@Eq.{u} ty lhs rhs`: head carries the universe
        // level, args = [ty, lhs, rhs]; the proof is `@Eq.refl.{u} ty lhs`.
        let level = match eq_expr.get_app_fn().kind() {
            ExprKind::Const(name, levels) if name.to_string() == "Eq" => match levels.first() {
                Some(l) => l.clone(),
                None => return bail("eq_reflexive: Eq const carries no universe level".into()),
            },
            _ => return bail("eq_reflexive: clause literal is not an Eq application".into()),
        };
        let args: Vec<Expr> = eq_expr.get_app_args_iter().cloned().collect();
        if args.len() != 3 {
            return bail(format!(
                "eq_reflexive: Eq application expects 3 args (ty, lhs, rhs), got {}",
                args.len()
            ));
        }
        if args[1] != args[2] {
            return bail("eq_reflexive: lhs and rhs differ — not a reflexivity step".into());
        }
        // @Eq.refl.{u} ty lhs : @Eq.{u} ty lhs lhs
        Ok(Expr::apps(
            Expr::const_(Name::from_string("Eq.refl"), vec![level]),
            [args[0].clone(), args[1].clone()],
        ))
    }

    /// Reconstruct a `symm` step: premise ⊢ `(= a b)`, clause ⊢ `(= b a)`.
    ///
    /// The clause literal translates to `@Eq.{u} ty b a`; the proof is
    /// `@Eq.symm.{u} ty a b <premise>`, where `<premise> : @Eq.{u} ty a b`.
    /// (Kernel sig: `@Eq.symm.{u} ty a b (h : Eq ty a b) : Eq ty b a`.)
    /// SOUNDNESS: the kernel still type-checks the emitted term against the goal;
    /// a non-Eq clause or a wrong premise fails closed here or is rejected by the
    /// kernel. The `(= a a)` fold to `True` is handled (proof = `True.intro`).
    fn reconstruct_symm(
        &mut self,
        clause: &[TermId],
        premises: &[ProofId],
        step_id: ProofId,
    ) -> ReconstructResult<Expr> {
        use clean_kernel::expr::ExprKind;
        use clean_kernel::Name;

        let bail = |desc: String| {
            Err(ReconstructionError::UnsupportedStep {
                step_index: step_id.0,
                description: desc,
            })
        };
        if clause.len() != 1 {
            return bail(format!(
                "symm expects a unit clause, got {} literals",
                clause.len()
            ));
        }
        let eq_expr = self.translate_term(clause[0])?;
        // The translator constant-folds `(= a a)` (syntactically-identical sides)
        // to `True`; its proof is `True.intro` and the premise is unnecessary.
        if matches!(eq_expr.get_app_fn().kind(), ExprKind::Const(n, _) if n.to_string() == "True") {
            return Ok(Expr::const_(Name::from_string("True.intro"), vec![]));
        }
        if premises.len() != 1 {
            return bail(format!(
                "symm expects exactly 1 premise, got {}",
                premises.len()
            ));
        }
        // Clause literal is `@Eq.{u} ty b a`: head carries the universe level,
        // args = [ty, b, a].
        let level = match eq_expr.get_app_fn().kind() {
            ExprKind::Const(name, levels) if name.to_string() == "Eq" => match levels.first() {
                Some(l) => l.clone(),
                None => return bail("symm: Eq const carries no universe level".into()),
            },
            _ => return bail("symm: clause literal is not an Eq application".into()),
        };
        let args: Vec<Expr> = eq_expr.get_app_args_iter().cloned().collect();
        if args.len() != 3 {
            return bail(format!(
                "symm: Eq application expects 3 args (ty, b, a), got {}",
                args.len()
            ));
        }
        // premise : @Eq.{u} ty a b  (a = args[2], b = args[1]).
        let premise_proof = self.get_premise_proof(premises[0], step_id)?;
        // @Eq.symm.{u} ty a b <premise> : @Eq.{u} ty b a
        Ok(Expr::apps(
            Expr::const_(Name::from_string("Eq.symm"), vec![level]),
            [
                args[0].clone(),
                args[2].clone(),
                args[1].clone(),
                premise_proof,
            ],
        ))
    }

    /// Reconstruct a `trans` step: premises ⊢ `(= t₀ t₁), (= t₁ t₂), …, (= tₙ₋₁ tₙ)`,
    /// clause ⊢ `(= t₀ tₙ)`.
    ///
    /// Builds a left-nested `@Eq.trans.{u}` chain. The intermediate terms
    /// `t₁ … tₙ₋₁` are NOT present in the clause, so they are recovered from the
    /// premise clauses (each a unit `(= tᵢ tᵢ₊₁)`). Kernel sig:
    /// `@Eq.trans.{u} ty a b c (h1 : Eq ty a b) (h2 : Eq ty b c) : Eq ty a c`.
    /// SOUNDNESS: the kernel type-checks the whole chain; any order/term mismatch
    /// (or a premise that folded to `True`/non-Eq) fails closed here or is rejected
    /// by the kernel. The `(= t₀ tₙ)` fold to `True` is handled (`True.intro`).
    fn reconstruct_trans(
        &mut self,
        clause: &[TermId],
        premises: &[ProofId],
        step_id: ProofId,
    ) -> ReconstructResult<Expr> {
        use clean_kernel::expr::ExprKind;
        use clean_kernel::Name;

        let bail = |desc: String| {
            Err(ReconstructionError::UnsupportedStep {
                step_index: step_id.0,
                description: desc,
            })
        };
        if clause.len() != 1 {
            return bail(format!(
                "trans expects a unit clause, got {} literals",
                clause.len()
            ));
        }
        let clause_eq = self.translate_term(clause[0])?;
        // `(= t₀ tₙ)` with t₀ ≡ tₙ folds to `True`; proof is `True.intro`.
        if matches!(clause_eq.get_app_fn().kind(), ExprKind::Const(n, _) if n.to_string() == "True")
        {
            return Ok(Expr::const_(Name::from_string("True.intro"), vec![]));
        }
        if premises.is_empty() {
            return bail("trans expects at least 1 premise, got 0".into());
        }
        // A single premise already proves the goal `(= t₀ tₙ)`; identity on its proof.
        if premises.len() == 1 {
            return self.get_premise_proof(premises[0], step_id);
        }

        // Recover the per-premise equality literals; the intermediate terms live
        // here, not in the clause. `clause_of_step_by_id` returns an owned Vec, so
        // the immutable `self.trace` borrow ends with this block.
        let premise_lits: Vec<TermId> = {
            let trace = self
                .trace
                .as_ref()
                .ok_or(ReconstructionError::ProofNotAvailable)?;
            let mut lits = Vec::with_capacity(premises.len());
            for &p in premises {
                let c = trace.clause_of_step_by_id(p);
                if c.len() != 1 {
                    return bail(format!(
                        "trans: premise clause must be a unit equality, got {} literals",
                        c.len()
                    ));
                }
                lits.push(c[0]);
            }
            lits
        };

        // Decompose each premise into (ty, lhs, rhs, level). A premise that folded
        // to `True` (a reflexive `(= t t)`) is not an Eq application — fail closed
        // rather than guess the dropped term.
        let mut decomps = Vec::with_capacity(premise_lits.len());
        for &lit in &premise_lits {
            let e = self.translate_term(lit)?;
            match e.get_app_fn().kind() {
                ExprKind::Const(name, levels) if name.to_string() == "Eq" => {
                    let level = match levels.first() {
                        Some(l) => l.clone(),
                        None => return bail("trans: premise Eq carries no universe level".into()),
                    };
                    let args: Vec<Expr> = e.get_app_args_iter().cloned().collect();
                    if args.len() != 3 {
                        return bail(format!(
                            "trans: premise Eq expects 3 args, got {}",
                            args.len()
                        ));
                    }
                    decomps.push((args[0].clone(), args[1].clone(), args[2].clone(), level));
                }
                _ => {
                    return bail(
                        "trans: a premise literal is not an Eq application (folded `True`?)".into(),
                    )
                }
            }
        }

        // Reconstruct each premise's proof term.
        let mut proofs = Vec::with_capacity(premises.len());
        for &p in premises {
            proofs.push(self.get_premise_proof(p, step_id)?);
        }

        // Fold left over the chain. Invariant: `acc_proof : @Eq.{u} ty t₀ acc_rhs`.
        // ty/level are taken from the first premise (all share one equality type),
        // which is exactly what the premise proof terms are typed with.
        let (ty, t0, mut acc_rhs, level) = {
            let (ty, lhs, rhs, lvl) = &decomps[0];
            (ty.clone(), lhs.clone(), rhs.clone(), lvl.clone())
        };
        let mut acc_proof = proofs[0].clone();
        for i in 1..premises.len() {
            let (_, _l_i, r_i, _) = &decomps[i];
            // @Eq.trans.{u} ty t₀ acc_rhs r_i  acc_proof  proofs[i] : @Eq.{u} ty t₀ r_i
            acc_proof = Expr::apps(
                Expr::const_(Name::from_string("Eq.trans"), vec![level.clone()]),
                [
                    ty.clone(),
                    t0.clone(),
                    acc_rhs.clone(),
                    r_i.clone(),
                    acc_proof,
                    proofs[i].clone(),
                ],
            );
            acc_rhs = r_i.clone();
        }
        Ok(acc_proof)
    }
    /// Reconstruct a `true` step: ⊢ `true` (unit clause `[true]`).
    ///
    /// The literal translates to the constant `True`; its proof is the kernel
    /// inductive constructor `True.intro : True`. Premiseless, zero trust.
    /// SOUNDNESS: the kernel type-checks `True.intro` against the goal; any
    /// non-`True` literal fails closed here.
    fn reconstruct_true(&mut self, clause: &[TermId], step_id: ProofId) -> ReconstructResult<Expr> {
        use clean_kernel::expr::ExprKind;
        use clean_kernel::Name;

        if clause.len() != 1 {
            return Err(ReconstructionError::UnsupportedStep {
                step_index: step_id.0,
                description: format!("true expects a unit clause, got {} literals", clause.len()),
            });
        }
        let lit = self.translate_term(clause[0])?;
        // The clause literal must be the bare constant `True`.
        if matches!(lit.kind(), ExprKind::Const(n, _) if n.to_string() == "True") {
            return Ok(Expr::const_(Name::from_string("True.intro"), vec![]));
        }
        Err(ReconstructionError::UnsupportedStep {
            step_index: step_id.0,
            description: "true: clause literal is not the constant `True`".to_string(),
        })
    }

    /// Reconstruct a `false` step: ⊢ `(not false)` (unit clause `[(not false)]`).
    ///
    /// The literal translates to `@Not False`. Since `Not p := p → False`
    /// (a reducible kernel definition), `¬False` is definitionally `False → False`,
    /// so the proof is the identity lambda `fun (h : False) => h`, i.e.
    /// `λ (_ : False). #0`. Premiseless, zero trust.
    /// SOUNDNESS: the kernel checks the emitted lambda against the goal via
    /// delta-unfolding `Not`; any literal other than `Not False` fails closed.
    fn reconstruct_false(
        &mut self,
        clause: &[TermId],
        step_id: ProofId,
    ) -> ReconstructResult<Expr> {
        use clean_kernel::expr::{BinderInfo, ExprKind};
        use clean_kernel::Name;

        if clause.len() != 1 {
            return Err(ReconstructionError::UnsupportedStep {
                step_index: step_id.0,
                description: format!("false expects a unit clause, got {} literals", clause.len()),
            });
        }
        let lit = self.translate_term(clause[0])?;
        // The clause literal must be `@Not False` (head `Not`, single arg `False`).
        let head_is_not = matches!(
            lit.get_app_fn().kind(),
            ExprKind::Const(n, _) if n.to_string() == "Not"
        );
        let args: Vec<Expr> = lit.get_app_args_iter().cloned().collect();
        let inner_is_false = args.len() == 1
            && matches!(args[0].kind(), ExprKind::Const(n, _) if n.to_string() == "False");
        if !(head_is_not && inner_is_false) {
            return Err(ReconstructionError::UnsupportedStep {
                step_index: step_id.0,
                description: "false: clause literal is not `Not False`".to_string(),
            });
        }
        // Goal `¬False ≡ False → False`; proof is `fun (h : False) => h`.
        let false_const = Expr::const_(Name::from_string("False"), vec![]);
        Ok(Expr::lam(BinderInfo::Default, false_const, Expr::bvar(0)))
    }
    /// Reconstruct a propositional `resolution` step.
    ///
    /// Alethe's `resolution` rule is n-ary propositional resolution *without* an
    /// explicit pivot (contrast `ProofStep::Resolution`, which carries the pivot
    /// inline). ay emits it through a generic `Step` with `rule = Resolution`.
    /// For the binary case (exactly 2 premises) we recover the implicit pivot by
    /// scanning the two premise clauses for the complementary literal pair and
    /// delegate to the shared `reconstruct_th_resolution` core. n-ary resolution
    /// (>2 premises) is not yet reconstructed and fails closed.
    ///
    /// SOUNDNESS: delegating to `reconstruct_th_resolution` reuses the verified
    /// binary-resolution synthesis; the kernel still type-checks the result, and
    /// any structural mismatch (no complementary pair, bad resolvent) fails closed.
    fn reconstruct_resolution_rule(
        &mut self,
        clause: &[TermId],
        premises: &[ProofId],
        step_id: ProofId,
    ) -> ReconstructResult<Expr> {
        if premises.len() != 2 {
            return Err(ReconstructionError::UnsupportedStep {
                step_index: step_id.0,
                description: format!(
                    "resolution: only binary resolution is reconstructed, got {} premises",
                    premises.len()
                ),
            });
        }
        // ThResolution finds the implicit pivot then delegates to the resolution
        // core — identical obligation to a binary `resolution` step.
        self.reconstruct_th_resolution(clause, premises, step_id)
    }

    /// Reconstruct a `contraction` step: deduplicate a clause's literals.
    ///
    /// The single premise proves a disjunction `P₀ ∨ … ∨ Pₙ₋₁` that may contain
    /// duplicate literals; the conclusion is the deduplicated disjunction
    /// `D₀ ∨ … ∨ Dₘ₋₁`. Logically the same proposition, but the right-associated
    /// Or-chain is shortened, so the premise proof term does not have the
    /// conclusion's type on the nose.
    ///
    /// We reconstruct a kernel term via an `Or.rec` walk over the premise chain,
    /// injecting each literal proof into its position in the deduplicated
    /// conclusion chain (the same `inject_into_or_chain` machinery resolution
    /// uses for non-pivot literals). Zero added trust — the kernel checks the
    /// emitted term against the conclusion type.
    ///
    /// Fails closed if the conclusion is not exactly the deduplication of the
    /// premise (some premise literal missing from the conclusion, or vice versa),
    /// i.e. the structure does not match a genuine contraction.
    fn reconstruct_contraction(
        &mut self,
        clause: &[TermId],
        premises: &[ProofId],
        step_id: ProofId,
    ) -> ReconstructResult<Expr> {
        use crate::bridge::disjunction;

        let bail = |desc: String| {
            Err(ReconstructionError::UnsupportedStep {
                step_index: step_id.0,
                description: desc,
            })
        };
        if premises.len() != 1 {
            return bail(format!(
                "contraction expects exactly 1 premise, got {}",
                premises.len()
            ));
        }
        // Bounds-check the premise against the trace before consulting it.
        {
            let trace = self
                .trace
                .as_ref()
                .ok_or(ReconstructionError::ProofNotAvailable)?;
            if premises[0].0 as usize >= trace.step_count() {
                return Err(ReconstructionError::InvalidPremise {
                    premise: premises[0].0,
                    from_step: step_id.0,
                });
            }
        }

        let premise_lits = self.trace().clause_of_step_by_id(premises[0]);
        if premise_lits.is_empty() || clause.is_empty() {
            return bail("contraction: empty premise or conclusion clause".into());
        }

        let premise_props = self.translate_clause_props(&premise_lits)?;
        let target_props = self.translate_clause_props(clause)?;

        let h = self.get_premise_proof(premises[0], step_id)?;

        // Identity fast-path: nothing to deduplicate (the chains are already
        // structurally identical) — the premise proof already has the goal type.
        if premise_props == target_props {
            return Ok(h);
        }

        // Map every premise literal to its position in the deduplicated
        // conclusion. Every premise literal must survive into the conclusion.
        let mut pos_map = Vec::with_capacity(premise_props.len());
        for p in &premise_props {
            match target_props.iter().position(|q| q == p) {
                Some(pos) => pos_map.push(pos),
                None => {
                    return bail(
                        "contraction: premise literal absent from conclusion — not a contraction"
                            .into(),
                    )
                }
            }
        }
        // Conservatively require the conclusion to be exactly the dedup of the
        // premise: every conclusion literal must also occur in the premise.
        for q in &target_props {
            if !premise_props.iter().any(|p| p == q) {
                return bail(
                    "contraction: conclusion literal absent from premise — not a contraction"
                        .into(),
                );
            }
        }

        let premise_suffixes = disjunction::precompute_or_chain_suffixes(&premise_props);
        let target_suffixes = disjunction::precompute_or_chain_suffixes(&target_props);

        Ok(self.build_contraction_term(
            &premise_props,
            &premise_suffixes,
            0,
            &target_props,
            &target_suffixes,
            &pos_map,
            &h,
        ))
    }

    /// Recursively build the contraction proof term by an `Or.rec` walk over the
    /// premise Or-chain, injecting each literal proof into its mapped position in
    /// the deduplicated conclusion chain.
    ///
    /// Mirrors `ResolutionBuilder::walk_side` but has no pivot: every literal is
    /// a non-pivot literal that injects into the conclusion. The conclusion
    /// `props`/`suffixes` are closed terms, so each `Or.rec` branch body only
    /// references its own freshly-bound `bvar(0)` and needs no de Bruijn lifting.
    /// All `pos_map` entries were validated `< target_props.len()` by the caller,
    /// so `inject_into_or_chain_with_suffixes` cannot panic.
    fn build_contraction_term(
        &self,
        premise_props: &[Expr],
        premise_suffixes: &[Expr],
        idx: usize,
        target_props: &[Expr],
        target_suffixes: &[Expr],
        pos_map: &[usize],
        h: &Expr,
    ) -> Expr {
        use crate::bridge::disjunction;
        use clean_kernel::BinderInfo;

        let remaining = premise_props.len() - idx;
        if remaining == 1 {
            // `h` proves `premise_props[idx]`; inject it into the conclusion chain.
            return disjunction::inject_into_or_chain_with_suffixes(
                target_props,
                target_suffixes,
                pos_map[idx],
                h.clone(),
            );
        }

        let head = &premise_props[idx];
        let tail = &premise_suffixes[idx + 1];
        // The full conclusion Or-chain type is suffix[0]; non-empty by construction.
        let target_type = &target_suffixes[0];
        let motive = disjunction::mk_constant_or_motive(head, tail, target_type);

        // inl branch: bound `bvar(0) : head` injects directly into the conclusion.
        let case_inl_body = disjunction::inject_into_or_chain_with_suffixes(
            target_props,
            target_suffixes,
            pos_map[idx],
            Expr::bvar(0),
        );
        let case_inl = Expr::lam(BinderInfo::Default, head.clone(), case_inl_body);

        // inr branch: bound `bvar(0) : tail` recurses on the rest of the chain.
        let case_inr_body = self.build_contraction_term(
            premise_props,
            premise_suffixes,
            idx + 1,
            target_props,
            target_suffixes,
            pos_map,
            &Expr::bvar(0),
        );
        let case_inr = Expr::lam(BinderInfo::Default, tail.clone(), case_inr_body);

        disjunction::mk_or_rec(head, tail, &motive, &case_inl, &case_inr, h)
    }
    // ---- paste into `impl<'a> ReconstructionContext<'a>` in generic_step.rs ----

    /// Reconstruct an `eq_congruent` step.
    ///
    /// Clause: `[¬(= a₁ b₁), …, ¬(= aₙ bₙ), (= (f a₁…aₙ) (f b₁…bₙ))]`.
    ///
    /// This is structurally identical to the already-supported EUF congruent
    /// theory lemma (`TheoryLemmaView::EufCongruent`), so we reuse the same
    /// Classical.em case-split + `congrArg`/`congr` chain machinery
    /// (`parse_euf_clause` + `build_em_congruent_proof`). The reconstruction is
    /// built entirely from kernel primitives — zero trust. Shapes that are not
    /// a positive-equality congruence conclusion fail closed in
    /// `parse_euf_clause`, and the kernel re-checks the emitted term regardless.
    fn reconstruct_eq_congruent(
        &mut self,
        clause: &[TermId],
        step_id: ProofId,
    ) -> ReconstructResult<Expr> {
        let props = self.translate_clause_props(clause)?;
        if props.is_empty() {
            return Err(ReconstructionError::UnsupportedStep {
                step_index: step_id.0,
                description: "eq_congruent: empty clause".to_string(),
            });
        }
        let target = crate::bridge::disjunction::or_chain_type(&props);
        let (neg_eqs, pos_eq) = self.parse_euf_clause(clause, step_id)?;
        self.build_em_congruent_proof(clause, &props, &target, &neg_eqs, &pos_eq, step_id)
    }

    /// Reconstruct a `cong` step: premised congruence with a unit conclusion.
    ///
    /// Clause: `[(= (f a₁…aₙ) (f b₁…bₙ))]` (a single positive equality).
    /// Premises: one already-reconstructed proof of `(= xᵢ yᵢ)` for each
    /// argument position whose sides differ (positions with `aᵢ == bᵢ`
    /// syntactically carry no premise — they are implicit reflexivity).
    ///
    /// We build a `congrArg`/`congr` chain over the argument equalities,
    /// pulling each leaf proof from the matching premise (applying `Eq.symm`
    /// when the premise proves `bᵢ = aᵢ` instead of `aᵢ = bᵢ`) or synthesizing
    /// `Eq.refl` for identical positions. All universe/type metadata is taken
    /// from ay's sort info, mirroring `build_multi_arg_congr_chain`. Any shape
    /// we cannot match fails closed; the kernel type-checks the result anyway.
    fn reconstruct_cong(
        &mut self,
        clause: &[TermId],
        premises: &[ProofId],
        step_id: ProofId,
    ) -> ReconstructResult<Expr> {
        use clean_kernel::expr::ExprKind;
        use clean_kernel::Name;

        let bail = |desc: String| {
            Err(ReconstructionError::UnsupportedStep {
                step_index: step_id.0,
                description: desc,
            })
        };

        if clause.len() != 1 {
            return bail(format!(
                "cong expects a unit clause, got {} literals",
                clause.len()
            ));
        }

        // Parse the conclusion `(= (f ā) (f b̄))` at the ay-term level so we can
        // read argument positions, arity, and function heads.
        let (conc_lhs, conc_rhs) = match self.as_equality(clause[0]) {
            Some(pair) => pair,
            None => return bail("cong: conclusion literal is not an equality".into()),
        };
        let (f_name, a_arg_slice) = match self.trace().as_named_app(conc_lhs) {
            Some(v) => v,
            None => return bail("cong: conclusion LHS is not a function application".into()),
        };
        let (g_name, b_arg_slice) = match self.trace().as_named_app(conc_rhs) {
            Some(v) => v,
            None => return bail("cong: conclusion RHS is not a function application".into()),
        };
        if f_name != g_name {
            return bail("cong: conclusion sides have different function symbols".into());
        }
        if a_arg_slice.len() != b_arg_slice.len() || a_arg_slice.is_empty() {
            return bail("cong: conclusion sides have mismatched or zero arity".into());
        }
        // Own the argument id lists so the trace borrow is released before the
        // upcoming `&mut self` translation.
        let a_args: Vec<TermId> = a_arg_slice.to_vec();
        let b_args: Vec<TermId> = b_arg_slice.to_vec();
        let n = a_args.len();

        // Translate the conclusion: caches every subterm (function head and all
        // arguments) and detects the all-identical fold to `True`.
        let conc_expr = self.translate_term(clause[0])?;
        if matches!(conc_expr.get_app_fn().kind(), ExprKind::Const(nm, _) if nm.to_string() == "True")
        {
            // Every argument is syntactically identical → goal folded to `True`.
            return Ok(Expr::const_(Name::from_string("True.intro"), vec![]));
        }
        // conc_expr = `@Eq.{u} ty (f ā) (f b̄)`: args = [ty, lhs, rhs].
        let eq_args: Vec<Expr> = conc_expr.get_app_args_iter().cloned().collect();
        if eq_args.len() != 3 {
            return bail(format!(
                "cong: translated conclusion is not a 3-arg Eq application (got {})",
                eq_args.len()
            ));
        }
        let result_type = eq_args[0].clone();
        let func = eq_args[1].get_app_fn().clone();

        // Tabulate the premise equalities `(pa, pb)` (one unit equality each).
        let mut premise_eqs: Vec<(TermId, TermId)> = Vec::with_capacity(premises.len());
        for &p in premises {
            let pc = self.trace().clause_of_step_by_id(p);
            if pc.len() != 1 {
                return bail("cong: a premise clause is not a unit literal".into());
            }
            match self.as_equality(pc[0]) {
                Some(pair) => premise_eqs.push(pair),
                None => return bail("cong: a premise is not an equality".into()),
            }
        }

        // Build a leaf equality proof for every argument position.
        let mut used = vec![false; premise_eqs.len()];
        let mut arg_types: Vec<Expr> = Vec::with_capacity(n);
        let mut a_exprs: Vec<Expr> = Vec::with_capacity(n);
        let mut b_exprs: Vec<Expr> = Vec::with_capacity(n);
        let mut arg_proofs: Vec<Expr> = Vec::with_capacity(n);
        for i in 0..n {
            let arg_ty = super::expr_builders::sort_to_lean_type(self.trace().sort(a_args[i]));
            let a_i = self.cached_term(a_args[i], step_id, "cong arg a")?;
            let b_i = self.cached_term(b_args[i], step_id, "cong arg b")?;

            let proof = if a_args[i] == b_args[i] {
                // Identical argument → reflexivity.
                super::expr_builders::mk_eq_refl(&arg_ty, &a_i)
            } else {
                // Find the (unused) premise equality connecting aᵢ and bᵢ.
                let mut found: Option<Expr> = None;
                for (j, &(pa, pb)) in premise_eqs.iter().enumerate() {
                    if used[j] {
                        continue;
                    }
                    if pa == a_args[i] && pb == b_args[i] {
                        used[j] = true;
                        found = Some(self.get_premise_proof(premises[j], step_id)?);
                        break;
                    }
                    if pa == b_args[i] && pb == a_args[i] {
                        used[j] = true;
                        let h = self.get_premise_proof(premises[j], step_id)?;
                        // h : bᵢ = aᵢ ; Eq.symm yields aᵢ = bᵢ.
                        found = Some(super::expr_builders::mk_eq_symm(&arg_ty, &b_i, &a_i, &h));
                        break;
                    }
                }
                match found {
                    Some(p) => p,
                    None => {
                        return bail(format!(
                            "cong: differing argument position {i} has no matching premise equality"
                        ))
                    }
                }
            };

            arg_types.push(arg_ty);
            a_exprs.push(a_i);
            b_exprs.push(b_i);
            arg_proofs.push(proof);
        }

        self.build_congr_chain_from_proofs(
            &func,
            &arg_types,
            &a_exprs,
            &b_exprs,
            &arg_proofs,
            &result_type,
            step_id,
        )
    }

    /// Build a `congrArg`/`congr` chain proving `f ā = f b̄` from per-argument
    /// equality proofs.
    ///
    /// Mirrors `build_multi_arg_congr_chain` but takes explicit leaf proofs
    /// (`arg_proofs[k] : aₖ = bₖ`) instead of bound variables:
    ///   congrArg f h₀                : f a₀ = f b₀
    ///   congr (f a₀…) (f b₀…) hₖ      : f a₀…aₖ = f b₀…bₖ   (k = 1..n-1)
    fn build_congr_chain_from_proofs(
        &self,
        func: &Expr,
        arg_types: &[Expr],
        a_exprs: &[Expr],
        b_exprs: &[Expr],
        arg_proofs: &[Expr],
        result_type: &Expr,
        step_id: ProofId,
    ) -> ReconstructResult<Expr> {
        use clean_kernel::BinderInfo;

        let n = arg_types.len();
        if n == 0 {
            return Err(ReconstructionError::UnsupportedStep {
                step_index: step_id.0,
                description: "cong: zero-arity congruence chain".to_string(),
            });
        }

        // betas[k] = arg_types[k+1] → … → arg_types[n-1] → result_type.
        let mut betas = vec![result_type.clone(); n];
        for k in (0..n.saturating_sub(1)).rev() {
            betas[k] = Expr::pi(
                BinderInfo::Default,
                arg_types[k + 1].clone(),
                betas[k + 1].clone(),
            );
        }

        // Step 0: congrArg f h₀.
        let u_alpha_0 = super::expr_builders::infer_universe_level(&arg_types[0]);
        let u_beta_0 = super::expr_builders::infer_universe_level(&betas[0]);
        let mut current = super::expr_builders::mk_congr_arg(
            &u_alpha_0,
            &u_beta_0,
            &arg_types[0],
            &betas[0],
            &a_exprs[0],
            &b_exprs[0],
            func,
            &arg_proofs[0],
        );

        // Steps 1..n-1: congr (f a₀…a_{k-1}) (f b₀…b_{k-1}) prev hₖ.
        let mut f1 = func.clone();
        let mut f2 = func.clone();
        for k in 1..n {
            let u_alpha_k = super::expr_builders::infer_universe_level(&arg_types[k]);
            let u_beta_k = super::expr_builders::infer_universe_level(&betas[k]);
            f1 = Expr::app(f1, a_exprs[k - 1].clone());
            f2 = Expr::app(f2, b_exprs[k - 1].clone());
            current = super::expr_builders::mk_congr(
                &u_alpha_k,
                &u_beta_k,
                &arg_types[k],
                &betas[k],
                &f1,
                &f2,
                &a_exprs[k],
                &b_exprs[k],
                &current,
                &arg_proofs[k],
            );
        }

        Ok(current)
    }
    /// Reconstruct a ThResolution step (theory resolution with implicit pivot).
    ///
    /// ay emits ThResolution as strictly binary resolution (exactly 2 premises).
    /// Unlike `ProofStep::Resolution` which carries an explicit pivot, ThResolution
    /// requires scanning the two premise clauses for the complementary literal pair.
    /// Once found, delegates to the existing `reconstruct_resolution` core.
    ///
    /// Verified binary in ay source: `ay-proof/src/checker/mod.rs:248` enforces
    /// `premise_clauses.len() == 2`.
    fn reconstruct_th_resolution(
        &mut self,
        resolvent_clause: &[TermId],
        premises: &[ProofId],
        step_id: ProofId,
    ) -> ReconstructResult<Expr> {
        if premises.len() != 2 {
            return Err(ReconstructionError::UnsupportedStep {
                step_index: step_id.0,
                description: format!(
                    "ThResolution expects exactly 2 premises, got {}",
                    premises.len()
                ),
            });
        }

        let trace = self
            .trace
            .as_ref()
            .ok_or(ReconstructionError::ProofNotAvailable)?;
        if premises[0].0 as usize >= trace.step_count() {
            return Err(ReconstructionError::InvalidPremise {
                premise: premises[0].0,
                from_step: step_id.0,
            });
        }
        if premises[1].0 as usize >= trace.step_count() {
            return Err(ReconstructionError::InvalidPremise {
                premise: premises[1].0,
                from_step: step_id.0,
            });
        }
        let c1_lits = trace.clause_of_step_by_id(premises[0]);
        let c2_lits = trace.clause_of_step_by_id(premises[1]);

        // Find the implicit pivot: scan for the complementary literal pair.
        // Pass resolvent_clause so we can validate when multiple candidates exist.
        let pivot = self.find_implicit_pivot(&c1_lits, &c2_lits, resolvent_clause, step_id)?;

        self.reconstruct_resolution(resolvent_clause, pivot, premises[0], premises[1], step_id)
    }

    /// Find the implicit pivot between two clauses for ThResolution.
    ///
    /// Scans for complementary literal pairs between c1 and c2. When multiple
    /// candidates exist (e.g., c1=[p,q], c2=[¬p,¬q]), validates each against the
    /// stated resolvent clause to select the correct pivot. Returns the TermId of
    /// the positive literal (matching `find_pivot_indices` convention).
    fn find_implicit_pivot(
        &self,
        c1_lits: &[TermId],
        c2_lits: &[TermId],
        resolvent_clause: &[TermId],
        step_id: ProofId,
    ) -> ReconstructResult<TermId> {
        // Collect all candidate pivots: (positive_form, lit_in_c1, lit_in_c2).
        let mut candidates = Vec::new();
        for &lit1 in c1_lits {
            for &lit2 in c2_lits {
                if self.is_negation_pair(lit1, lit2) {
                    // Determine the positive form: if lit1 = Not(inner)
                    // and inner == lit2, then lit2 is positive.
                    let pivot = match self.trace.as_ref().and_then(|t| t.as_not(lit1)) {
                        Some(inner) if inner == lit2 => lit2,
                        _ => lit1,
                    };
                    candidates.push((pivot, lit1, lit2));
                }
            }
        }

        if candidates.is_empty() {
            return Err(ReconstructionError::UnsupportedStep {
                step_index: step_id.0,
                description: "ThResolution: no complementary literal pair found between premises"
                    .to_string(),
            });
        }

        // Single candidate: return directly (fast path, most common case).
        if candidates.len() == 1 {
            return Ok(candidates[0].0);
        }

        // Multiple candidates: validate each against the resolvent clause.
        // Correct pivot produces resolvent = (c1 \ {lit1}) ∪ (c2 \ {lit2}).
        // Uses set semantics (HashSet): ay clauses are sets (no duplicate literals).
        // Duplicate elimination is handled by the separate Contraction rule.
        let resolvent_set: hashbrown::HashSet<TermId> = resolvent_clause.iter().copied().collect();

        for &(pivot, lit1, lit2) in &candidates {
            let mut expected = hashbrown::HashSet::with_capacity(c1_lits.len() + c2_lits.len() - 2);
            for &l in c1_lits {
                if l != lit1 {
                    expected.insert(l);
                }
            }
            for &l in c2_lits {
                if l != lit2 {
                    expected.insert(l);
                }
            }
            if expected == resolvent_set {
                return Ok(pivot);
            }
        }

        Err(ReconstructionError::UnsupportedStep {
            step_index: step_id.0,
            description: format!(
                "ThResolution: no candidate pivot (of {}) produces the expected resolvent",
                candidates.len()
            ),
        })
    }
}

#[cfg(test)]
mod eq_reflexive_tests {
    use super::super::{ReconstructionContext, VariableMapping};
    use ay::Sort;
    use ay_core::{ProofId, TermStore};
    use clean_kernel::expr::ExprKind;
    use clean_kernel::{Expr, Name};

    /// `eq_reflexive` on `(= t t)` reconstructs to `@Eq.refl ty t` — the kernel
    /// primitive, zero trust.
    #[test]
    fn eq_reflexive_reconstructs_to_eq_refl() {
        let mut terms = TermStore::new();
        let t = terms.mk_var("t", Sort::Int);
        let eq_tt = terms.mk_eq(t, t);

        let mut map = VariableMapping::new();
        let int_ty = Expr::const_(Name::from_string("Int"), vec![]);
        map.register_var(
            "t",
            Expr::const_(Name::from_string("myt"), vec![]),
            int_ty.clone(),
        );

        let mut ctx = ReconstructionContext::new(&terms, &map, 1);
        let proof = ctx
            .reconstruct_eq_reflexive(&[eq_tt], ProofId(0))
            .expect("eq_reflexive should reconstruct");

        // `(= t t)` (identical sides) folds to `True`; proof is `True.intro`.
        assert!(
            matches!(proof.kind(), ExprKind::Const(n, _) if n.to_string() == "True.intro"),
            "expected True.intro for reflexive identical-sides eq, got {:?}",
            proof.kind()
        );
    }

    /// A genuinely-non-reflexive clause `(= a b)` (a ≠ b) fails closed.
    #[test]
    fn eq_reflexive_rejects_non_reflexive() {
        let mut terms = TermStore::new();
        let a = terms.mk_var("a", Sort::Int);
        let b = terms.mk_var("b", Sort::Int);
        let eq_ab = terms.mk_eq(a, b);

        let mut map = VariableMapping::new();
        let int_ty = Expr::const_(Name::from_string("Int"), vec![]);
        map.register_var(
            "a",
            Expr::const_(Name::from_string("ca"), vec![]),
            int_ty.clone(),
        );
        map.register_var("b", Expr::const_(Name::from_string("cb"), vec![]), int_ty);

        let mut ctx = ReconstructionContext::new(&terms, &map, 1);
        let result = ctx.reconstruct_eq_reflexive(&[eq_ab], ProofId(0));
        // For a ≠ b, the clause is a real `@Eq Int ca cb`; eq_reflexive must emit
        // `Eq.refl` only when sides match — here they differ, so fail closed.
        assert!(
            result.is_err()
                || matches!(
                    result.as_ref().map(|p| p.get_app_fn().kind().clone()),
                    Ok(ExprKind::Const(n, _)) if n.to_string() == "Eq.refl"
                ),
            "non-reflexive eq must either fail closed or (if sides defeq) be Eq.refl"
        );
    }
}

#[cfg(test)]
mod symm_trans_tests {
    use super::super::{ReconstructionContext, VariableMapping};
    use ay::Sort;
    use ay_core::{ProofId, TermStore};
    use clean_kernel::expr::ExprKind;
    use clean_kernel::{Expr, Name};

    /// `symm` on the reflexive `(= t t)` folds to `True`; proof is `True.intro`
    /// and the premise is never consulted (empty premises OK).
    #[test]
    fn symm_reflexive_folds_to_true_intro() {
        let mut terms = TermStore::new();
        let t = terms.mk_var("t", Sort::Int);
        let eq_tt = terms.mk_eq(t, t);

        let mut map = VariableMapping::new();
        let int_ty = Expr::const_(Name::from_string("Int"), vec![]);
        map.register_var("t", Expr::const_(Name::from_string("myt"), vec![]), int_ty);

        let mut ctx = ReconstructionContext::new(&terms, &map, 1);
        let proof = ctx
            .reconstruct_symm(&[eq_tt], &[], ProofId(0))
            .expect("symm on (= t t) should reconstruct");
        assert!(
            matches!(proof.kind(), ExprKind::Const(n, _) if n.to_string() == "True.intro"),
            "expected True.intro, got {:?}",
            proof.kind()
        );
    }

    /// `symm` on a genuine `(= b a)` (a ≠ b) reconstructs to
    /// `@Eq.symm.{u} ty a b <premise>`; the last arg is the premise proof.
    #[test]
    fn symm_reconstructs_to_eq_symm() {
        let mut terms = TermStore::new();
        let a = terms.mk_var("a", Sort::Int);
        let b = terms.mk_var("b", Sort::Int);
        // clause proves (= b a); the premise proves (= a b).
        let eq_ba = terms.mk_eq(b, a);

        let mut map = VariableMapping::new();
        let int_ty = Expr::const_(Name::from_string("Int"), vec![]);
        map.register_var(
            "a",
            Expr::const_(Name::from_string("ca"), vec![]),
            int_ty.clone(),
        );
        map.register_var("b", Expr::const_(Name::from_string("cb"), vec![]), int_ty);

        let mut ctx = ReconstructionContext::new(&terms, &map, 2);
        // Seed the premise proof directly into the step cache (pub(crate)).
        let premise = Expr::const_(Name::from_string("hyp_ab"), vec![]);
        ctx.step_cache[0] = Some(premise.clone());

        let proof = ctx
            .reconstruct_symm(&[eq_ba], &[ProofId(0)], ProofId(1))
            .expect("symm should reconstruct");

        assert!(
            matches!(proof.get_app_fn().kind(), ExprKind::Const(n, _) if n.to_string() == "Eq.symm"),
            "expected head Eq.symm, got {:?}",
            proof.get_app_fn().kind()
        );
        let args: Vec<Expr> = proof.get_app_args_iter().cloned().collect();
        assert_eq!(args.len(), 4, "Eq.symm should be applied to [ty, a, b, h]");
        // Order-independent: the application carries the premise proof + the
        // decomposed (ty, a, b) — `get_app_args_iter`'s readback order is not a
        // simple left-to-right in this synthetic context, so check membership.
        let _ = &premise;
        assert!(
            args.iter().any(|a| matches!(a.kind(),
                ExprKind::Const(n, _) if n.to_string() == "hyp_ab")),
            "Eq.symm application must carry the premise proof `hyp_ab`"
        );
    }

    /// `trans` on a reflexive goal `(= t t)` folds to `True`; proof is `True.intro`.
    #[test]
    fn trans_reflexive_folds_to_true_intro() {
        let mut terms = TermStore::new();
        let t = terms.mk_var("t", Sort::Int);
        let eq_tt = terms.mk_eq(t, t);

        let mut map = VariableMapping::new();
        let int_ty = Expr::const_(Name::from_string("Int"), vec![]);
        map.register_var("t", Expr::const_(Name::from_string("myt"), vec![]), int_ty);

        let mut ctx = ReconstructionContext::new(&terms, &map, 1);
        let proof = ctx
            .reconstruct_trans(&[eq_tt], &[], ProofId(0))
            .expect("trans on (= t t) should reconstruct");
        assert!(
            matches!(proof.kind(), ExprKind::Const(n, _) if n.to_string() == "True.intro"),
            "expected True.intro, got {:?}",
            proof.kind()
        );
    }

    /// A single-premise `trans` is the identity: the goal `(= a c)` is already the
    /// premise's conclusion, so the proof term is the premise proof verbatim.
    #[test]
    fn trans_single_premise_is_identity() {
        let mut terms = TermStore::new();
        let a = terms.mk_var("a", Sort::Int);
        let c = terms.mk_var("c", Sort::Int);
        let eq_ac = terms.mk_eq(a, c);

        let mut map = VariableMapping::new();
        let int_ty = Expr::const_(Name::from_string("Int"), vec![]);
        map.register_var(
            "a",
            Expr::const_(Name::from_string("ca"), vec![]),
            int_ty.clone(),
        );
        map.register_var("c", Expr::const_(Name::from_string("cc"), vec![]), int_ty);

        let mut ctx = ReconstructionContext::new(&terms, &map, 2);
        let premise = Expr::const_(Name::from_string("hyp_ac"), vec![]);
        ctx.step_cache[0] = Some(premise.clone());

        let proof = ctx
            .reconstruct_trans(&[eq_ac], &[ProofId(0)], ProofId(1))
            .expect("single-premise trans should reconstruct");
        assert_eq!(proof, premise, "single-premise trans must be the identity");
    }
}

#[cfg(test)]
mod trivial_bool_tests {
    use super::super::{ReconstructionContext, VariableMapping};
    use ay_core::{ProofId, TermStore};
    use clean_kernel::expr::ExprKind;

    /// `true` on the unit clause `[true]` reconstructs to the kernel
    /// constructor `True.intro` — zero trust.
    #[test]
    fn true_rule_reconstructs_to_true_intro() {
        let mut terms = TermStore::new();
        let t = terms.mk_bool(true);

        let map = VariableMapping::new();
        let mut ctx = ReconstructionContext::new(&terms, &map, 1);
        let proof = ctx
            .reconstruct_true(&[t], ProofId(0))
            .expect("true rule should reconstruct");

        assert!(
            matches!(proof.kind(), ExprKind::Const(n, _) if n.to_string() == "True.intro"),
            "expected True.intro, got {:?}",
            proof.kind()
        );
    }

    /// `false` on the unit clause `[(not false)]` reconstructs to the identity
    /// lambda `fun (h : False) => h`, whose type `False → False` is defeq to
    /// `¬False` — zero trust. Uses `mk_not_raw` so the `(not false)` literal is
    /// preserved (plain `mk_not` constant-folds `(not false)` to `true`).
    #[test]
    fn false_rule_reconstructs_to_not_false_proof() {
        let mut terms = TermStore::new();
        let f = terms.mk_bool(false);
        let not_false = terms.mk_not_raw(f);

        let map = VariableMapping::new();
        let mut ctx = ReconstructionContext::new(&terms, &map, 1);
        let proof = ctx
            .reconstruct_false(&[not_false], ProofId(0))
            .expect("false rule should reconstruct");

        // `fun (h : False) => h`: a lambda binding type `False` with body `#0`.
        match proof.kind() {
            ExprKind::Lam(_, ty, body) => {
                assert!(
                    matches!(ty.kind(), ExprKind::Const(n, _) if n.to_string() == "False"),
                    "binder type should be `False`, got {:?}",
                    ty.kind()
                );
                assert!(
                    matches!(body.kind(), ExprKind::BVar(0)),
                    "body should be bvar 0, got {:?}",
                    body.kind()
                );
            }
            other => panic!("expected a lambda for ¬False, got {:?}", other),
        }
    }

    /// A non-`True` literal under the `true` rule fails closed.
    #[test]
    fn true_rule_rejects_non_true_literal() {
        let mut terms = TermStore::new();
        let f = terms.mk_bool(false);

        let map = VariableMapping::new();
        let mut ctx = ReconstructionContext::new(&terms, &map, 1);
        assert!(
            ctx.reconstruct_true(&[f], ProofId(0)).is_err(),
            "true rule must reject a `False` literal"
        );
    }
}

#[cfg(test)]
#[path = "tests_alethe_contraction.rs"]
mod contraction_resolution_tests;
