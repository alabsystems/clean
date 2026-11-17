// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Recursor ι-reduction (design §5.2).

use super::*;

/// Recursor ι-reduction (design §5.2): for a saturated application
/// `I.rec <levels> params motive minors... indices... major`, when `major`
/// whnf's to a literal constructor `C args` of `I`, fire the matching ι-rule.
///
/// The rule RHS is `λ params. λ motive. λ minors. λ fields. body`; we apply it
/// to `[params..., motive, minors..., (C's fields)]`. Only fires on a literal
/// saturated constructor of `I`.
pub(super) fn try_iota(
    env: &dyn Env,
    ctx: &[Term],
    e: &Term,
    budget: &mut Budget,
) -> Result<Option<Term>, BudgetError> {
    // The head is either an `Elim` reference (the form the validation chokepoint
    // produces — recursors are never plain Consts across the untrusted boundary,
    // design §4.2) or a `Const` recursor name (the form the kernel-DERIVED ι-rule
    // RHSs use internally for their recursive IH calls — never crosses the
    // boundary). Both resolve to the inductive via the env's recursor registry.
    let (head, args) = e.unfold_apps();
    // The firing head carries the *concrete* universe levels of this Elim/recursor
    // application. The rule RHS is built over the recursor's generic level params
    // (`Param(0)…` — motive level then inductive levels, design §5.2 /
    // `recursor_rules::build_rule_rhs`), and its embedded IH sub-recursor is at
    // those generic params. We MUST instantiate the RHS's level params with these
    // concrete levels before applying it, in the SAME order the recursor signature
    // dictates (`[motive_lvl?, ind_levels…]`, matching `ElimRef::derived_levels`
    // and `ConstRef::levels()`). Without this, a recursive ι-reduction at concrete
    // levels `L` leaves the result's IH recursor at `Param(0)…` → a downstream
    // `TypeMismatch` (Incident: the recursive-ι level gap; surfaced on
    // `List.rec`-with-IH lemmas such as `Clean.Res.allSatSnoc`).
    let (ind, head_levels): (Name, &[Level]) = match head.kind() {
        TermKind::Elim(eref) => (eref.inductive().clone(), eref.levels()),
        TermKind::Const(cref) if env.is_recursor(cref.name()) => {
            // Resolve the inductive from the recursor name via recursor_shape's
            // keying (it accepts both inductive and recursor names).
            (cref.name().clone(), cref.levels())
        }
        _ => return Ok(None),
    };
    let Some(shape) = env.recursor_shape(&ind) else {
        return Ok(None);
    };
    let np = usize::try_from(shape.num_params).unwrap_or(usize::MAX);
    let nm = usize::try_from(shape.num_minors).unwrap_or(usize::MAX);
    let ni = usize::try_from(shape.num_indices).unwrap_or(usize::MAX);
    let n_motives = usize::try_from(shape.num_motives).unwrap_or(usize::MAX);
    // major-premise position = params + motives + minors + indices.
    let major_pos = np
        .checked_add(n_motives)
        .and_then(|x| x.checked_add(nm))
        .and_then(|x| x.checked_add(ni));
    let Some(major_pos) = major_pos else {
        return Ok(None);
    };
    if args.len() <= major_pos {
        return Ok(None); // not saturated to the major premise
    }
    // Reduce the major premise. The standard ι-rule fires when it is a literal
    // constructor of `I`. STRUCTURE-η IN ι: if `I` is a genuine η-structure (1
    // ctor, no indices, non-recursive — see `inductive::is_eta_structure`, which
    // gates `structure_info`) and the major is instead a NEUTRAL term `m : I`
    // (e.g. a variable `s : Step`), then `m ≡ I.mk (m.0) … (m.{n-1})`
    // definitionally, so we fire the single ι-rule with `proj_i m` as the fields.
    // This is exactly the major-premise η-expansion Lean's kernel performs; it is
    // sound *precisely because* `structure_info(I)` is restricted to η-structures
    // and is what lets two stuck `Step.rec … s` terms converge. As in Lean, it
    // fires only when `m`'s type is headed by `I` and is not a proposition
    // (`major_admits_structure_eta`).
    let major = whnf_in_context(env, ctx, &args[major_pos], budget)?;
    let (maj_head, maj_args) = major.unfold_apps();
    let Some(rules) = env.recursor_rules(&ind) else {
        return Ok(None);
    };
    // `fields` is either the literal constructor's field slice (borrowed) or the
    // η-expanded projections (owned). `owned_fields` keeps the latter alive.
    let owned_fields: Vec<Term>;
    let (rule, fields): (&crate::recursor::IotaRule, &[Term]) = match maj_head.kind() {
        // A `Nat` literal major premise of `Nat`'s recursor: Lean's kernel reads
        // the literal as its constructor form (`0` is `Nat.zero`, `n + 1` is
        // `Nat.succ n`), the conversion its `Nat` literal extension rests on
        // (R162). Only for the inductive named `Nat`, whose constructors the
        // literal's type names; any other inductive leaves the recursor stuck.
        // (`ind` is the inductive for an `Elim` head and the recursor's own name
        // for the kernel-derived IH call `Nat.rec`; both name `Nat`'s recursor.)
        TermKind::Lit(Lit::Nat(v))
            if ind == Name::from_dotted("Nat") || ind == Name::from_dotted("Nat.rec") =>
        {
            let (ctor, field) = if v.is_zero() {
                ("Nat.zero", None)
            } else {
                // The predecessor is native arithmetic like any other: the work
                // meter charges its size before it is built (R166).
                let one = crate::BigNat::one();
                budget.charge(crate::bignat::result_words::sum(v, &one))?;
                ("Nat.succ", Some(Term::lit(Lit::Nat(v.sub(&one)))))
            };
            let Some(rule) = rules
                .iter()
                .find(|r| r.constructor == Name::from_dotted(ctor))
            else {
                return Ok(None);
            };
            owned_fields = field.into_iter().collect();
            if usize::try_from(rule.num_fields).ok() != Some(owned_fields.len()) {
                return Ok(None);
            }
            (rule, owned_fields.as_slice())
        }
        // A constructor application, of any inductive (Lean's
        // `is_constructor_app`): the rule its constructor names, or stuck.
        TermKind::Const(c) if env.constructor_arity(c.name()).is_some() => {
            let Some(rule) = rules.iter().find(|r| r.constructor == *c.name()) else {
                return Ok(None);
            };
            // Constructor args are `params ++ fields`; the RHS expects the fields.
            let nf = usize::try_from(rule.num_fields).unwrap_or(usize::MAX);
            // Too few args (or a saturated end) leaves the recursor stuck.
            let Some(arity) = env.constructor_arity(c.name()) else {
                return Ok(None);
            };
            let ctor_np = usize::try_from(arity.num_params).unwrap_or(usize::MAX);
            if arity.num_fields != rule.num_fields
                || ctor_np.checked_add(nf) != Some(maj_args.len())
            {
                return Ok(None);
            }
            let Some(fields) = maj_args.get(ctor_np..ctor_np.saturating_add(nf)) else {
                return Ok(None);
            };
            (rule, fields)
        }
        // K-like reduction (Lean's `to_cnstr_when_K`, which its
        // `inductive_reduce_rec` applies inside whnf): the eliminator of a
        // K-target whose major has its sole constructor's type fires that
        // constructor's rule, which binds no fields. Only for an `Elim` head,
        // whose `ind` names the inductive (a K-target has no fields, so no
        // kernel-derived IH call names its recursor).
        _ if matches!(head.kind(), TermKind::Elim(_))
            && major_is_k_constructor(env, ctx, &ind, &rules, np, ni, &major, budget)? =>
        {
            let [rule] = rules.as_slice() else {
                return Ok(None);
            };
            (rule, &[])
        }
        _ => {
            // Non-constructor major (a neutral term or a constant): only
            // structure-η can fire, and only when `I` is an η-structure (its
            // single ctor is the sole ι-rule). `try_proj` soundness:
            // `structure_info` is registered ONLY for η-structures, so
            // `I.proj_i major` def-eq-recovers field `i` of `major`. Fail-closed
            // otherwise (leave the recursor stuck).
            let Some(info) = env.structure_info(&ind) else {
                return Ok(None);
            };
            // The sole rule must be the structure constructor's rule.
            let Some(rule) = rules.iter().find(|r| r.constructor == info.ctor) else {
                return Ok(None);
            };
            if rules.len() != 1 {
                return Ok(None);
            }
            // A field count past the derivation limit is a forged rule: leave
            // the recursor stuck instead of sizing a vector by it.
            let nf = rule.num_fields;
            if nf > crate::recursor::MAX_DERIVED_ARITY {
                return Ok(None);
            }
            if !major_admits_structure_eta(env, ctx, &ind, &major, budget)? {
                return Ok(None);
            }
            // η-expand: fields := [ I.proj_0 major, …, I.proj_{nf-1} major ].
            owned_fields = (0..nf)
                .map(|idx| Term::proj(ind.clone(), idx, major.clone()))
                .collect();
            (rule, owned_fields.as_slice())
        }
    };

    // Apply rule.rhs to [params..., motives..., minors..., fields...].
    // rec args layout: [params(np), motives(N), minors(nm), indices(ni), major, ...trailing].
    // The RHS lambda binds params · motives · minors · fields positionally.
    let params = args.get(0..np).unwrap_or(&[]);
    let motives = args.get(np..np.saturating_add(n_motives)).unwrap_or(&[]);
    if motives.len() != n_motives {
        return Ok(None); // not saturated to the motives
    }
    let minors = args
        .get(np.saturating_add(n_motives)..np.saturating_add(n_motives).saturating_add(nm))
        .unwrap_or(&[]);
    if minors.len() != nm {
        return Ok(None); // not saturated to the minors
    }
    // Instantiate the rule RHS's generic level params with the firing head's
    // concrete levels BEFORE applying it (soundness-critical for recursive minors;
    // see the head_levels comment above). The substitution preserves the term
    // structure and is total — `instantiate_levels` is a no-op when `head_levels`
    // is empty (small-elim / level-param-free inductives), which is exactly right.
    // The count is `rec_num_levels = num_level_params(I) + (1 iff large_elim)`,
    // identical for the rule RHS and the firing head by construction
    // (`recursor::derive` / `ElimRef::mk`); a mismatch would be an internal
    // derivation inconsistency, asserted in debug builds.
    debug_assert!(
        rule.rec_num_levels == head_levels.len(),
        "recursive-ι level arity mismatch: rule expects {} levels, head carries {}",
        rule.rec_num_levels,
        head_levels.len(),
    );
    let mut applied = rule.rhs.instantiate_levels(head_levels)?;
    applied = Term::apply(applied, params);
    applied = Term::apply(applied, motives);
    applied = Term::apply(applied, minors);
    applied = Term::apply(applied, fields);
    // Re-apply any trailing args beyond the major premise.
    if let Some(trailing) = args.get(major_pos.saturating_add(1)..) {
        applied = Term::apply(applied, trailing);
    }
    Ok(Some(applied))
}

/// Lean's K-like reduction at a recursor's major premise (`to_cnstr_when_K`,
/// `src/kernel/inductive.h`). R162 applied it in `def_eq`, the one place
/// ck0 then had a local context. `whnf` has one since R147, and Lean applies
/// the rule inside whnf, so a K-eliminator in a whnf-only position (a head
/// that must be a function type, a sort) reduces as in Lean. `ind` must be a
/// K-target: a `Prop` inductive with one constructor that binds no fields.
/// The major's type, in whnf, must be `ind ps is`, and the constructor applied
/// to `ps` must have a type definitionally equal to it. Then proof irrelevance
/// makes the major that constructor. Any other shape, or a step that cannot
/// be typed, answers `false`, and the recursor stays stuck.
#[allow(clippy::too_many_arguments)]
pub(super) fn major_is_k_constructor(
    env: &dyn Env,
    ctx: &[Term],
    ind: &Name,
    rules: &[crate::recursor::IotaRule],
    np: usize,
    ni: usize,
    major: &Term,
    budget: &mut Budget,
) -> Result<bool, BudgetError> {
    if !env.recursor_shape(ind).is_some_and(|s| s.num_motives == 1) {
        return Ok(false);
    }
    let [rule] = rules else {
        return Ok(false);
    };
    if rule.num_fields != 0 {
        return Ok(false);
    }
    // `I : (params) → (indices) → Prop`.
    let Some(mut ind_ty) = env.const_type(ind) else {
        return Ok(false);
    };
    while let TermKind::Pi(_, _, body) = ind_ty.kind() {
        let next = body.clone();
        ind_ty = next;
    }
    if !matches!(ind_ty.kind(), TermKind::Sort(l) if l.is_zero()) {
        return Ok(false);
    }
    let major_ty = match crate::infer::infer_for_conversion(env, ctx, major, budget) {
        Ok(ty) => ty,
        Err(InferError::OutOfBudget) => return Err(BudgetError::OutOfBudget),
        Err(_) => return Ok(false),
    };
    let major_ty = whnf_in_context(env, ctx, &major_ty, budget)?;
    let (ty_head, ty_args) = major_ty.unfold_apps();
    let TermKind::Const(ty_ref) = ty_head.kind() else {
        return Ok(false);
    };
    if ty_ref.name() != ind || Some(ty_args.len()) != np.checked_add(ni) {
        return Ok(false);
    }
    let Some(params) = ty_args.get(..np) else {
        return Ok(false);
    };
    let Ok(ctor) =
        crate::term::ConstRef::mk(env, rule.constructor.clone(), ty_ref.levels().to_vec())
    else {
        return Ok(false);
    };
    let ctor_app = Term::apply(Term::const_ref(ctor), params);
    let ctor_ty = match crate::infer::infer_for_conversion(env, ctx, &ctor_app, budget) {
        Ok(ty) => ty,
        Err(InferError::OutOfBudget) => return Err(BudgetError::OutOfBudget),
        Err(_) => return Ok(false),
    };
    crate::def_eq::is_def_eq_in_context(env, ctx, &ctor_ty, &major_ty, budget)
}

/// Lean's guard on structure η at a recursor's major premise
/// (`to_cnstr_when_structure`, `src/kernel/inductive.h`; decision R147): the
/// major's type, in weak head normal form, is headed by the recursor's
/// structure `ind`, and that type is not a proposition. v4.33.1 asks `is_prop`
/// (leanprover/lean4#14843), which tests the sort's level for zero up to
/// normalization; ck0's canonical [`Level::is_zero`] is that test. A type
/// whose own type is not a sort makes Lean's `is_prop` throw; here, as for
/// any other failure to type the major, the recursor stays stuck.
pub(super) fn major_admits_structure_eta(
    env: &dyn Env,
    ctx: &[Term],
    ind: &Name,
    major: &Term,
    budget: &mut Budget,
) -> Result<bool, BudgetError> {
    let major_ty = match crate::infer::infer_for_conversion(env, ctx, major, budget) {
        Ok(ty) => ty,
        Err(InferError::OutOfBudget) => return Err(BudgetError::OutOfBudget),
        Err(_) => return Ok(false),
    };
    let major_ty = whnf_in_context(env, ctx, &major_ty, budget)?;
    let (head, _) = major_ty.unfold_apps();
    if !matches!(head.kind(), TermKind::Const(c) if c.name() == ind) {
        return Ok(false);
    }
    match infer_sort_in_context(env, ctx, &major_ty, budget) {
        Ok(level) => Ok(!level.is_zero()),
        Err(InferError::OutOfBudget) => Err(BudgetError::OutOfBudget),
        Err(_) => Ok(false),
    }
}
