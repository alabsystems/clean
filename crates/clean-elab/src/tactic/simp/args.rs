// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Lean's `elabSimpArgs`: turning a surface `simp [a, ← b, -c]` lemma list
//! into the three channels [`SimpConfig`] carries.
//!
//! Lean's element grammar is `simpLemma := (simpPre <|> simpPost)? "← "? term`
//! and `simpErase := "-" ident` (`Lean/Elab/Tactic/Simp.lean`), and
//! `elabSimpArg` dispatches on it: an element that resolves as an identifier
//! takes the by-name path (`mkSimpTheoremFromConst`), everything else is
//! elaborated as a TERM (`elabSimpTheorem` → `mkSimpTheoremFromExpr`), and a
//! `simpErase` element removes its lemma from the set.
//!
//! Clean used to funnel every element through `surface_expr_to_name`, so an
//! applied argument (`@xor_not_right a`, `dif_pos h`) was refused loud, a
//! dotted name on a LOCAL (`h.symm`) minted a global name that resolves to
//! nothing and was dropped silent, and the two modifiers were eaten by the
//! parser — which made `simp [← h]` rewrite FORWARD and `simp [-h]` *add* the
//! lemma Lean removes.

use std::collections::HashSet;

use clean_kernel::{Expr, Level, Name};
use clean_parser::{SurfaceExpr, SurfaceName, SurfaceSimpArg};

use super::lean_builtin_simprocs::{resolve_simp_ident, NamedSimprocs, SimpIdent};
use super::lean_names::names_unminted_lean_name;
use super::lemmas::{
    extract_local_equality_template, mk_local_proof_template, prop_simp_lemmas_from_proof,
    type_is_prop,
};
use super::types::{SimpIndexMode, SimpLemma};
use crate::tactic::registry::TacticEval;
use crate::tactic::{ProofState, TacticError};

/// Priority of a user-written simp argument, matching the by-name path
/// (`collect_extra_lemmas`): below the `@[simp]` registry (100) and below
/// `simp [*]`'s hypothesis rules (75).
pub(crate) const SIMP_ARG_PRIORITY: u32 = 50;

/// A `simp` lemma list resolved into the channels [`super::SimpConfig`] has.
#[derive(Debug, Default)]
pub(crate) struct ResolvedSimpArgs {
    /// Arguments that name a constant or local: the by-name path, which also
    /// drives `resolve_unfold_defs`' delta-unfolding of a `simp [myDef]`.
    pub(crate) extra_lemmas: Vec<SurfaceName>,
    /// `-lemma` arguments, as `SimpConfig::exclude` expects them (both the
    /// spelling written and its resolved global name, so an unqualified
    /// erasure of an opened-namespace lemma still bites).
    pub(crate) exclude: HashSet<SurfaceName>,
    /// Arguments elaborated as TERMS, and every `←`-reversed argument, built
    /// into rules here because the by-name path has no channel for either.
    pub(crate) prebuilt: Vec<SimpLemma>,
    /// Parallel to [`Self::prebuilt`]: the GLOBAL declaration a `←`-reversed
    /// element NAMED, when it named one.
    ///
    /// Lean's origin for such an element is `.decl <name> post (inv := true)`
    /// (`elabDeclToUnfoldOrTheorem`'s `e.isConst` arm hands the declaration
    /// name to `mkSimpTheoremFromConst`), and `Origin.converse` flips `inv`,
    /// so a later `<name>` or `-<name>` element erases it. A term-shaped
    /// element carries a `.stx` origin that no `-` can name, and so carries
    /// `None` here.
    prebuilt_origin: Vec<Option<SurfaceName>>,
    /// The simprocs the list names (`↓reduceIte`, `-Nat.reduceAdd`), which
    /// add no rule: they decide which simplification procedures run
    /// (`lean_builtin_simprocs::simproc_scope`, which also refuses any Clean
    /// cannot honour).
    pub(crate) simprocs: NamedSimprocs,
}

impl ResolvedSimpArgs {
    /// Drop every already-built rule whose `←` element named `origin` — the
    /// `Origin.converse` half of Lean's erasure.
    fn forget_reversed(&mut self, origin: &SurfaceName) {
        let rules = std::mem::take(&mut self.prebuilt);
        let origins = std::mem::take(&mut self.prebuilt_origin);
        for (rule, rule_origin) in rules.into_iter().zip(origins) {
            if rule_origin.as_ref() == Some(origin) {
                continue;
            }
            self.prebuilt.push(rule);
            self.prebuilt_origin.push(rule_origin);
        }
    }
}

/// The GLOBAL declaration an element names, when Lean would give it a `.decl`
/// origin: a bare name that is not a local and does resolve to a constant.
///
/// A LOCAL hypothesis is deliberately `None`. Lean routes it through the
/// `e.isFVar` arm of `elabDeclToUnfoldOrTheorem`, which keeps the `.stx`
/// origin `elabSimpArg` minted — an origin whose `converse` is `none`, so no
/// later element of the list can erase it by name.
fn decl_origin(ps: &ProofState, term: &SurfaceExpr) -> Option<SurfaceName> {
    if !crate::tactic::builtins_phase3d_rewrite::rw_rule_is_name(term) {
        return None;
    }
    let name = crate::tactic::builtins::surface_expr_to_name(term).ok()?;
    let goal = ps.current_goal()?;
    if goal
        .local_ctx
        .iter()
        .any(|decl| crate::tactic::pattern::names::hypothesis_named(&decl.name, &name))
    {
        return None;
    }
    let global = crate::tactic::core::resolve_global_name(ps, &name).ok()?;
    ps.env().get_const(&global)?;
    Some(SurfaceName::from_name(global))
}

/// Resolve a surface simp lemma list — Lean's `elabSimpArgs`.
///
/// REQUIRES: `ps` has a current goal whenever a term-path argument is present
///   (its elaboration and type inference happen in that goal's context).
/// ENSURES: every element lands in exactly one channel of the result, or is
///   cancelled by a LATER element naming it (Lean processes the list in
///   order: `-x` erases an earlier `[x]`, and `[x]` un-erases an earlier
///   `-x`).
/// ENSURES: an element that is neither name-resolvable nor elaborable raises,
///   as Lean's `elabSimpArg` does: an identifier that names no local,
///   constant or simproc raises `UnknownIdent` (G48), except a name Lean
///   would accept that Clean does not declare (`names_unminted_lean_name`),
///   which reaches `collect_extra_lemmas` and is skipped there with a
///   warning. A
///   `-x` erasure whose `x` names nothing raises too (Lean's
///   `realizeGlobalConstNoOverloadWithInfo`: "unknown constant").
/// ENSURES: at most ONE direction of a named global declaration survives the
///   list. Lean's `addSimpTheorem` opens with `eraseFwdIfBwd`, so adding
///   `← r` erases a forward `r` and adding `r` erases a `← r`; `Origin`'s
///   `BEq` compares `inv`, which is what makes them two entries rather than
///   one.
pub(crate) fn resolve_simp_args(
    eval: &mut dyn TacticEval,
    ps: &mut ProofState,
    args: &[SurfaceSimpArg],
) -> Result<ResolvedSimpArgs, TacticError> {
    let world = super::lean_builtin_simprocs::source_world(eval, ps)?;
    let mut out = ResolvedSimpArgs::default();
    for arg in args {
        if arg.erase {
            // Lean's `simpErase` takes an `ident`, never a term.
            let name = crate::tactic::builtins::surface_expr_to_name(&arg.term)?;
            // A simproc is erased from the simprocs, not the lemmas
            // (`elabSimpArgs`: `simprocs.erase declName`).
            match resolve_simp_ident(ps, &name, world) {
                SimpIdent::Simproc(simproc) => {
                    out.simprocs.erase(simproc);
                    continue;
                }
                // Lean resolves the erased ident with
                // `realizeGlobalConstNoOverloadWithInfo`, which throws
                // "unknown constant" on a name nothing declares; erasing it
                // is not a no-op there.
                SimpIdent::Unknown if !names_unminted_lean_name(ps, &name) => {
                    return Err(TacticError::UnknownIdent(name.to_string()));
                }
                SimpIdent::Unknown | SimpIdent::LocalOrConstant => {}
            }
            let global = crate::tactic::core::resolve_global_name(ps, &name)
                .ok()
                .map(SurfaceName::from_name);
            // Lean walks the list IN ORDER (`elabSimpArgs`' second loop), so a
            // `-x` AFTER an `[x]` erases what that element added. Pinned
            // v4.30.0-rc2 refuses `simp only [plain, -plain]` ("`simp` made no
            // progress") and accepts `simp only [-plain, plain]`; two
            // order-free sets would accept both, and the `only` mode makes the
            // difference observable rather than academic.
            out.extra_lemmas
                .retain(|n| n != &name && Some(n) != global.as_ref());
            // `SimpTheorems.erase` falls back to `thmId.converse` when the
            // origin it was handed is not in the set, so `-r` removes the
            // `← r` an earlier element added. Pinned v4.30.0-rc2 reports
            // "`simp` made no progress" for `simp only [← rab, -rab]` and
            // accepts `simp only [← rab]`.
            if let Some(global) = &global {
                out.forget_reversed(global);
            }
            if let Some(global) = global {
                out.exclude.insert(global);
            }
            out.exclude.insert(name);
            continue;
        }
        // A forward, name-resolvable argument keeps the by-name path: it is
        // what `resolve_unfold_defs` reads for `simp [myDef]`, and what the
        // `@[simp]` registry interaction is stated over.
        if !arg.reverse && name_path_applies(ps, &arg.term) {
            let name = crate::tactic::builtins::surface_expr_to_name(&arg.term)?;
            match resolve_simp_ident(ps, &name, world) {
                SimpIdent::LocalOrConstant => {}
                // A simproc adds no rule: it joins the simprocs the call runs
                // (`simprocs.add`), which the caller turns into a scope or a
                // refusal by name (`lean_builtin_simprocs::simproc_scope`).
                SimpIdent::Simproc(simproc) => {
                    out.simprocs.add(simproc);
                    continue;
                }
                // Lean's `elabSimpArg` elaborates an identifier that is
                // neither a local, a constant nor a simproc as a term, and
                // that THROWS `unknown identifier '<name>'` (G48, ledger
                // (118): `simp [totally_bogus_name_xyz]` used to be accepted
                // with a warning, as if the element were not there). A name
                // Lean WOULD accept and Clean does not declare
                // (`names_unminted_lean_name`: a generated `f.eq_1` /
                // `C.injEq`, or an `Init` lemma the builtin prelude lacks)
                // is still dropped with `collect_extra_lemmas`' diagnostic —
                // a weaker rule set, never a bigger one.
                SimpIdent::Unknown if !names_unminted_lean_name(ps, &name) => {
                    return Err(TacticError::UnknownIdent(name.to_string()));
                }
                SimpIdent::Unknown => {}
            }
            // The other half of the ordering rule: Lean's add arm runs
            // `uneraseSimpEntry` before `addSimpEntry`, so an `[x]` after a
            // `-x` puts `x` back.
            if let Ok(global) = crate::tactic::core::resolve_global_name(ps, &name) {
                // Adding a definition adds each of its realized equation
                // theorems, undoing earlier exclusions of those entries.
                if let Some(equations) =
                    super::declared_equations::collect(ps.env(), &global, SIMP_ARG_PRIORITY)
                {
                    for equation in equations {
                        out.exclude.remove(&SurfaceName::from_name(equation.name));
                    }
                }
                let global = SurfaceName::from_name(global);
                // `eraseFwdIfBwd` in the forward direction: adding `r` erases
                // the `← r` an earlier element added. Pinned v4.30.0-rc2
                // reports "`simp` made no progress" for
                // `simp only [← rab, rab]`.
                out.forget_reversed(&global);
                out.exclude.remove(&global);
            }
            out.exclude.remove(&name);
            out.extra_lemmas.push(name);
            continue;
        }
        let rules = term_arg_lemmas(eval, ps, arg, SIMP_ARG_PRIORITY)?;
        let origin = if arg.reverse {
            decl_origin(ps, &arg.term)
        } else {
            None
        };
        if let Some(global) = &origin {
            // `eraseFwdIfBwd` (`SimpTheorems.lean`, issue #4290): a BACKWARD
            // rule erases the forward one, wherever it came from — an earlier
            // element of this list or the `@[simp]` registry. Without it
            // `simp [← r]` over a registered `r` leaves both directions live,
            // the registry's priority 100 beats this rule's 50, and the
            // reversed request loses to the rule it was written to override
            // (measured: the goal came back unmoved).
            out.extra_lemmas.retain(|n| n != global);
            if let Ok(written) = crate::tactic::builtins::surface_expr_to_name(&arg.term) {
                out.extra_lemmas.retain(|n| n != &written);
            }
            out.exclude.insert(global.clone());
        }
        for _ in &rules {
            out.prebuilt_origin.push(origin.clone());
        }
        out.prebuilt.extend(rules);
    }
    Ok(out)
}

/// Whether the by-name simp path can use this argument.
///
/// The same split `rw` has carried since class (25)/(36): a bare identifier or
/// a dotted chain that names a local or a resolvable global. Everything else —
/// an application, a `@`-explicit head, field notation on a local — is a term.
fn name_path_applies(ps: &ProofState, term: &SurfaceExpr) -> bool {
    crate::tactic::builtins_phase3d_rewrite::rw_rule_is_name(term)
        && crate::tactic::builtins_phase3d_rewrite::rw_name_resolves(ps, term)
}

/// Elaborate a simp argument as a TERM and build its rewrite rules —
/// Lean's `elabSimpTheorem` → `mkSimpTheoremFromExpr (inv := inv)`.
///
/// The metavariables elaboration leaves open become the rule's PATTERN
/// variables (Lean's `abstractMVars`), not proof-state side goals: `simp
/// [@forall_eq _ p a]` must gain no goal. They are abstracted to the loose
/// de Bruijn indices the matcher re-mints as fresh pattern metas
/// (`convert_bvars_to_metas`), which is the same representation the by-name
/// and local-hypothesis rules already use.
fn term_arg_lemmas(
    eval: &mut dyn TacticEval,
    ps: &mut ProofState,
    arg: &SurfaceSimpArg,
    priority: u32,
) -> Result<Vec<SimpLemma>, TacticError> {
    let refined = eval.elaborate_open(ps, &arg.term)?;
    // The side goals are deliberately DROPPED rather than pushed: an open
    // metavariable of a simp argument is a pattern variable, where `rw`'s
    // identical bridge turns one into a side goal.
    let (proof, _side_goals) = crate::tactic::term_close::import_open_term(
        ps,
        refined.term,
        eval.metas(),
        &refined.pending_goals,
    )?;
    let goal = ps.current_goal().cloned().ok_or(TacticError::NoGoals)?;
    let proof = ps.metas.instantiate(&proof);
    let ty = ps
        .infer_type(&goal, &proof)
        .map_err(|e| TacticError::InvalidTarget {
            tactic: "simp".into(),
            detail: format!("cannot infer the type of this simp argument: {e}"),
        })?;
    let ty = ps.metas.instantiate(&ty);

    // The Prop test must run BEFORE abstraction: `infer_type` cannot read a
    // type carrying loose de Bruijn indices.
    let is_prop = type_is_prop(ps, &goal, &ty);
    let (proof, ty) = abstract_open_metas(&proof, &ty);
    let name = simp_arg_rule_name(&arg.term);
    let lemmas = rules_from_proof(ps, &name, &proof, &ty, is_prop, arg, priority);
    if lemmas.is_empty() {
        return Err(TacticError::InvalidTarget {
            tactic: "simp".into(),
            detail: if arg.reverse {
                "`←` needs an equation, an iff, or a proposition to reverse".into()
            } else {
                "simp argument is not an equation, an iff, or a proposition".into()
            },
        });
    }
    Ok(lemmas)
}

/// The rules a term simp argument of type `ty`, proved by `proof`, stands for.
///
/// The abstracted metavariables already occupy the low loose indices of
/// `proof`/`ty`; the `∀` binders `ty` still carries are layered BELOW them by
/// [`apply_statement_binders`].
fn rules_from_proof(
    ps: &ProofState,
    name: &Name,
    proof: &Expr,
    ty: &Expr,
    is_prop: bool,
    arg: &SurfaceSimpArg,
    priority: u32,
) -> Vec<SimpLemma> {
    // The `∀` binders of the statement itself, applied to the proof exactly as
    // a local hypothesis rule's template does.
    if let Some((pi_binders, eq_type, lhs, rhs, levels)) = extract_local_equality_template(ty) {
        let proof = apply_statement_binders(proof, pi_binders);
        return vec![eq_rule(
            ps, name, &eq_type, &lhs, &rhs, &levels, proof, arg, priority,
        )];
    }
    if let Some((pi_binders, lhs, rhs)) = super::expr::extract_iff_with_binders(ty) {
        let proof = apply_statement_binders(proof, pi_binders);
        // `propext lhs rhs h : lhs = rhs` — Clean's `propext` takes the `Iff`
        // witness directly (`clean-kernel/src/env/logic.rs`).
        let eq_proof = Expr::apps(
            Expr::const_(Name::from_string("propext"), vec![]),
            [lhs.clone(), rhs.clone(), proof],
        );
        // `propext` is declared to return `@Eq.{1} Prop a b`
        // (`canonical_propext_type`, `clean-kernel/src/env/axiom_audit.rs`):
        // the ELEMENTS are propositions, so the equality's carrier is `Prop`
        // and `Prop : Sort 1`. `Eq.symm.{0}` here type-checked as far as the
        // rule's own shape and then died at `close_goal` with a mismatch whose
        // two sides PRINT the same (`A = B` vs `A = B`) because only the level
        // differs — which is why `←` over an iff has to be pinned e2e.
        return vec![eq_rule(
            ps,
            name,
            &Expr::prop(),
            &lhs,
            &rhs,
            &[Level::succ(Level::zero())],
            eq_proof,
            arg,
            priority,
        )];
    }
    // Every other proposition is Lean's `preprocess` form: `P = True`,
    // `¬P` as `P = False` (`P → False` is the conditional `False = True`),
    // a conjunction split into its halves.
    // `←` has nothing to reverse there, which is Lean's refusal too.
    if arg.reverse || !is_prop {
        return Vec::new();
    }
    prop_simp_lemmas_from_proof(ps, name, proof, ty, priority)
}

/// Apply a proof whose loose indices are the abstracted metavariables to the
/// `pi_binders` further binders its STATEMENT quantifies.
///
/// `extract_local_equality_template` peels those `∀`s without instantiating,
/// so inside the equation the statement's binders hold indices `0 ..
/// pi_binders` and every abstracted metavariable has shifted up by
/// `pi_binders`. The proof is lifted to match and then applied outermost-first,
/// the layout [`mk_local_proof_template`] fixes and the matcher's
/// `convert_bvars_to_metas` reads.
fn apply_statement_binders(proof: &Expr, pi_binders: u32) -> Expr {
    if pi_binders == 0 {
        return proof.clone();
    }
    mk_local_proof_template(
        crate::tactic::bvar_ops::lift_bvars(proof, pi_binders),
        pi_binders,
    )
}

/// One `lhs = rhs` rule, oriented by `arg.reverse`.
#[allow(clippy::too_many_arguments)]
fn eq_rule(
    ps: &ProofState,
    name: &Name,
    eq_type: &Expr,
    lhs: &Expr,
    rhs: &Expr,
    levels: &[Level],
    proof: Expr,
    arg: &SurfaceSimpArg,
    priority: u32,
) -> SimpLemma {
    let eq_type = ps.metas.instantiate(eq_type);
    let lhs = ps.metas.instantiate(lhs);
    let rhs = ps.metas.instantiate(rhs);
    let proof = ps.metas.instantiate(&proof);
    if arg.reverse {
        // `@Eq.symm α a b h : b = a` — the sides swap with the proof, so the
        // rule stays a kernel-checkable equality.
        let symm = Expr::apps(
            Expr::const_(Name::from_string("Eq.symm"), levels.to_vec()),
            [eq_type.clone(), lhs.clone(), rhs.clone(), proof],
        );
        return SimpLemma {
            name: name.clone(),
            lhs: rhs,
            rhs: lhs,
            eq_type: Some(eq_type),
            proof_expr: Some(symm),
            index_mode: SimpIndexMode::NoIndexAtArgs,
            priority,
        };
    }
    SimpLemma {
        name: name.clone(),
        lhs,
        rhs,
        eq_type: Some(eq_type),
        proof_expr: Some(proof),
        index_mode: SimpIndexMode::NoIndexAtArgs,
        priority,
    }
}

/// Abstract every still-unassigned metavariable of `proof`/`ty` into a loose
/// de Bruijn index — Lean's `abstractMVars`.
///
/// Index `0` is the innermost binder, so metavariable `i` is abstracted at
/// depth `i`: each new binder is added OUTSIDE the ones already introduced,
/// which leaves their indices untouched.
fn abstract_open_metas(proof: &Expr, ty: &Expr) -> (Expr, Expr) {
    let mut metas: Vec<Expr> = Vec::new();
    collect_open_metas(proof, &mut metas);
    collect_open_metas(ty, &mut metas);
    let mut proof = proof.clone();
    let mut ty = ty.clone();
    for (index, meta) in metas.iter().enumerate() {
        let Ok(depth) = u32::try_from(index) else {
            break;
        };
        proof = crate::tactic::bvar_ops::abstract_bvar(&proof, meta, depth);
        ty = crate::tactic::bvar_ops::abstract_bvar(&ty, meta, depth);
    }
    (proof, ty)
}

/// Every distinct unassigned-metavariable FVar in `e`, in first-seen order.
fn collect_open_metas(e: &Expr, out: &mut Vec<Expr>) {
    use clean_kernel::ExprKind;
    crate::stack_safe(|| match e.kind() {
        ExprKind::FVar(id) => {
            if crate::unify::MetaState::from_fvar(*id).is_some() {
                let expr = Expr::fvar(*id);
                if !out.contains(&expr) {
                    out.push(expr);
                }
            }
        }
        ExprKind::App(f, a) => {
            collect_open_metas(f, out);
            collect_open_metas(a, out);
        }
        ExprKind::Lam(_, t, b) | ExprKind::Pi(_, t, b) => {
            collect_open_metas(t, out);
            collect_open_metas(b, out);
        }
        ExprKind::Let(_, t, v, b, _) => {
            collect_open_metas(t, out);
            collect_open_metas(v, out);
            collect_open_metas(b, out);
        }
        ExprKind::Proj(_, _, inner) | ExprKind::MData(_, inner) => collect_open_metas(inner, out),
        _ => {}
    });
}

/// The name a term-path rule carries.
///
/// It must NOT resolve in the environment: `LemmaLevels::for_lemma`,
/// `binding_violates_declared_domain` and `bind_undetermined_binders` all read
/// `env.get_const(&lemma.name)` and would pair this rule's own BVar layout
/// with the declaration's telescope — the documented hazard a synthesized
/// lemma carrying a real constant's name causes. The head's spelling is kept
/// as a suffix so `CLEAN_SIMP_MATCH_TRACE` stays readable.
fn simp_arg_rule_name(term: &SurfaceExpr) -> Name {
    let prefix = Name::from_string("_simpArg");
    match surface_head_name(term) {
        // The head's own kernel name, appended component-wise — never its
        // DISPLAY spelling re-parsed by `Name::from_string`, which would
        // flatten `Function.comp` into one component and lose an escaped
        // component's identity.
        Some(head) => crate::namespace::append_names(&prefix, &head),
        None => prefix.str("term"),
    }
}

/// The kernel name of an argument's head identifier, if it has one.
fn surface_head_name(term: &SurfaceExpr) -> Option<Name> {
    match term {
        SurfaceExpr::Ident(_, name) => Some(name.name().clone()),
        SurfaceExpr::App(_, f, _) | SurfaceExpr::Explicit(_, f) | SurfaceExpr::Paren(_, f) => {
            surface_head_name(f)
        }
        SurfaceExpr::Proj(_, base, _) => surface_head_name(base),
        _ => None,
    }
}
