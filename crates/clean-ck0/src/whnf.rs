// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Weak-head normalization — **one outer reduction relation** (design §5.1).
//!
//! ```text
//! whnf(e):  loop {
//!     e = whnf_core(e)      // β, ζ (let), proj-of-constructor, native Nat/String
//!     match try_delta(e), try_quot(e):
//!         progressed -> continue
//!         stuck      -> return e
//! }
//! ```
//!
//! `whnf_core` performs the head-structural reductions that need no env lookup
//! (β, ζ) plus the env-light ones (proj-of-constructor, native literal
//! reduction). δ (transparency-gated unfolding) and the `Quot.lift/ind` ι-rules
//! are applied in the outer loop and then re-fed to `whnf_core`. There is
//! exactly one relation, budget-threaded and `Result`-returning; **recursor**
//! (inductive ι) reduction is **M2** — a recursor application is left *stuck*.

use crate::budget::{Budget, BudgetError};
use crate::level::Level;
use crate::name::Name;
use crate::term::{Lit, Term, TermKind};
use crate::validate::{Env, QuotKind, Transparency};

/// Weak-head-normalize `e` to a fixpoint (or until the budget is exhausted).
///
/// Returns `Err(OutOfBudget)` on exhaustion — callers in soundness *rejection*
/// positions collapse that to reject (never fail open).
pub fn whnf(env: &dyn Env, e: &Term, budget: &mut Budget) -> Result<Term, BudgetError> {
    let mut cur = whnf_core(env, e, budget)?;
    loop {
        budget.step()?;
        // δ: transparency-gated unfolding of the head constant.
        if let Some(unfolded) = try_delta(env, &cur)? {
            cur = whnf_core(env, &unfolded, budget)?;
            continue;
        }
        // Quot.lift/ind ι-rule.
        if let Some(reduced) = try_quot(env, &cur, budget)? {
            cur = whnf_core(env, &reduced, budget)?;
            continue;
        }
        // Recursor (inductive) ι-rule (M2).
        if let Some(reduced) = try_iota(env, &cur, budget)? {
            cur = whnf_core(env, &reduced, budget)?;
            continue;
        }
        return Ok(cur);
    }
}

/// Recursor ι-reduction (design §5.2): for a saturated application
/// `I.rec <levels> params motive minors... indices... major`, when `major`
/// whnf's to a literal constructor `C args` of `I`, fire the matching ι-rule.
///
/// The rule RHS is `λ params. λ motive. λ minors. λ fields. body`; we apply it
/// to `[params..., motive, minors..., (C's fields)]`. Only fires on a literal
/// saturated constructor of `I`.
fn try_iota(env: &dyn Env, e: &Term, budget: &mut Budget) -> Result<Option<Term>, BudgetError> {
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
    // and is what lets two stuck `Step.rec … s` terms converge.
    let major = whnf(env, &args[major_pos], budget)?;
    let (maj_head, maj_args) = major.unfold_apps();
    let Some(rules) = env.recursor_rules(&ind) else {
        return Ok(None);
    };
    // `fields` is either the literal constructor's field slice (borrowed) or the
    // η-expanded projections (owned). `owned_fields` keeps the latter alive.
    let owned_fields: Vec<Term>;
    let (rule, fields): (&crate::recursor::IotaRule, &[Term]) = match maj_head.kind() {
        TermKind::Const(c) => {
            let Some(rule) = rules.iter().find(|r| r.constructor == *c.name()) else {
                return Ok(None);
            };
            // Constructor args are `params ++ fields`; the RHS expects the fields.
            let nf = usize::try_from(rule.num_fields).unwrap_or(usize::MAX);
            if maj_args.len() < np.saturating_add(nf) {
                return Ok(None);
            }
            (rule, &maj_args[np..np.saturating_add(nf)])
        }
        _ => {
            // Non-constructor major: only structure-η can fire, and only when `I`
            // is an η-structure (its single ctor is the sole ι-rule). `try_proj`
            // soundness: `structure_info` is registered ONLY for η-structures, so
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
            let nf = usize::try_from(rule.num_fields).unwrap_or(usize::MAX);
            // η-expand: fields := [ I.proj_0 major, …, I.proj_{nf-1} major ].
            owned_fields = (0..nf)
                .map(|i| {
                    let idx = u32::try_from(i).unwrap_or(u32::MAX);
                    Term::proj(ind.clone(), idx, major.clone())
                })
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
    let mut applied = rule.rhs.instantiate_levels(head_levels);
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

/// The env-light core: β, ζ (let), proj-of-constructor, native Nat/String.
/// Reduces the head to fixpoint over *these* rules only.
fn whnf_core(env: &dyn Env, e: &Term, budget: &mut Budget) -> Result<Term, BudgetError> {
    let mut cur = e.clone();
    loop {
        budget.step()?;
        match cur.kind() {
            // ζ: let _ : ty := val; body  ~>  body[val]
            TermKind::Let(_, val, body) => {
                cur = body.instantiate(val);
            }
            // β / native head reductions on an application spine.
            TermKind::App(_, _) => {
                let (head, args) = cur.unfold_apps();
                // β: (λ x. body) a rest..  ~>  (body[a]) rest..
                if let TermKind::Lam(_, _, body) = head.kind() {
                    if let Some((first, rest)) = args.split_first() {
                        let beta = body.instantiate(first);
                        cur = Term::apply(beta, rest);
                        continue;
                    }
                }
                // native Nat reduction (succ / binary ops on literals).
                if let Some(reduced) = try_native_nat(env, &head, &args, budget)? {
                    cur = reduced;
                    continue;
                }
                return Ok(cur);
            }
            // proj-of-constructor: S.i (C p.. f..)  ~>  f_i
            TermKind::Proj(struct_name, idx, inner) => {
                let inner_whnf = whnf(env, inner, budget)?;
                if let Some(field) = try_proj_ctor(env, struct_name, *idx, &inner_whnf) {
                    cur = field;
                    continue;
                }
                // stuck on the (reduced) inner term.
                return Ok(Term::proj(struct_name.clone(), *idx, inner_whnf));
            }
            _ => return Ok(cur),
        }
    }
}

/// δ: if the head is a `Const` with a [`Transparency::Transparent`] definition,
/// substitute its level args into the body and replace the head. Returns the
/// whole spine with the head unfolded, or `None` if the head is δ-stuck.
fn try_delta(env: &dyn Env, e: &Term) -> Result<Option<Term>, BudgetError> {
    let (head, args) = e.unfold_apps();
    let TermKind::Const(cref) = head.kind() else {
        return Ok(None);
    };
    let Some(def) = env.const_def(cref.name()) else {
        return Ok(None);
    };
    if def.transparency != Transparency::Transparent {
        return Ok(None);
    }
    let body = def.body.instantiate_levels(cref.levels());
    Ok(Some(Term::apply(body, &args)))
}

/// The `Quot.lift`/`Quot.ind` ι-rules (design §5.1):
/// `Quot.lift α r β f h (Quot.mk α r a) ~> f a`
/// `Quot.ind  α r β f   (Quot.mk α r a) ~> f a`
/// The head and the `Quot.mk` are recognized via the *closed* [`QuotKind`]
/// classification, never by free name lookup.
fn try_quot(env: &dyn Env, e: &Term, budget: &mut Budget) -> Result<Option<Term>, BudgetError> {
    let (head, args) = e.unfold_apps();
    let TermKind::Const(cref) = head.kind() else {
        return Ok(None);
    };
    let Some(kind) = env.quot_kind(cref.name()) else {
        return Ok(None);
    };
    // Argument layout (Lean): lift = [α, r, β, f, h, q]; ind = [α, r, β, f, q].
    // The major premise `q` is the last argument; `f` sits two before it for
    // lift (after `h`) and one before for ind.
    let (f_idx, q_idx) = match kind {
        QuotKind::Lift => (3usize, 5usize),
        QuotKind::Ind => (3usize, 4usize),
        QuotKind::Type | QuotKind::Mk => return Ok(None),
    };
    if args.len() <= q_idx {
        return Ok(None);
    }
    // The major premise must whnf to `Quot.mk α r a`.
    let q = whnf(env, &args[q_idx], budget)?;
    let (q_head, q_args) = q.unfold_apps();
    let TermKind::Const(q_cref) = q_head.kind() else {
        return Ok(None);
    };
    if env.quot_kind(q_cref.name()) != Some(QuotKind::Mk) {
        return Ok(None);
    }
    // Quot.mk layout: [α, r, a]; the value `a` is the last argument.
    let Some(a) = q_args.last() else {
        return Ok(None);
    };
    let f = args[f_idx].clone();
    // f a, then re-apply any trailing args beyond the major premise.
    let mut result = Term::app(f, a.clone());
    if let Some(trailing) = args.get(q_idx.saturating_add(1)..) {
        result = Term::apply(result, trailing);
    }
    Ok(Some(result))
}

/// proj-of-constructor: if `inner` (already whnf'd) is a constructor application
/// `C p_0..p_{k-1} f_0..f_{m-1}`, return field `idx` (`f_idx`). Uses the env's
/// recorded `(num_params, num_fields)` so the field offset is `num_params+idx`.
fn try_proj_ctor(env: &dyn Env, _struct: &Name, idx: u32, inner: &Term) -> Option<Term> {
    let (head, args) = inner.unfold_apps();
    let TermKind::Const(cref) = head.kind() else {
        return None;
    };
    let arity = env.constructor_arity(cref.name())?;
    if idx >= arity.num_fields {
        return None;
    }
    let offset = usize::try_from(arity.num_params).ok()?;
    let field_idx = usize::try_from(idx).ok()?.checked_add(offset)?;
    args.get(field_idx).cloned()
}

/// Native `Nat` literal reduction (design §5.1 "native Nat/String reduction").
/// Recognizes `Nat.succ (Lit n)` and the binary `Nat.{add,sub,mul,...}` ops on
/// two `Nat` literals, reducing them in arbitrary precision via [`crate::BigNat`]
/// (no fixed-width arithmetic on values). Anything else is `None` (stuck).
fn try_native_nat(
    env: &dyn Env,
    head: &Term,
    args: &[Term],
    budget: &mut Budget,
) -> Result<Option<Term>, BudgetError> {
    let TermKind::Const(cref) = head.kind() else {
        return Ok(None);
    };
    let name = cref.name();
    // Only `Nat.*` ops participate; the leading `Nat` component gates this.
    if name.parent().as_ref().map(Name::last_str) != Some(Some("Nat")) {
        return Ok(None);
    }
    let op = match name.last_str() {
        Some(op) => op,
        None => return Ok(None),
    };
    // Nat.succ n  ~>  Lit(n+1)
    if op == "succ" {
        let [arg] = args else { return Ok(None) };
        let arg = whnf(env, arg, budget)?;
        if let Some(n) = nat_lit(&arg) {
            return Ok(Some(Term::lit(Lit::Nat(n.add(&crate::BigNat::one())))));
        }
        return Ok(None);
    }
    // Binary ops on two literals.
    let bin: Option<fn(&crate::BigNat, &crate::BigNat) -> NatResult> = match op {
        "add" => Some(|a, b| NatResult::Nat(a.add(b))),
        "sub" => Some(|a, b| NatResult::Nat(a.sub(b))),
        "mul" => Some(|a, b| NatResult::Nat(a.mul(b))),
        "div" => Some(|a, b| NatResult::Nat(a.div(b))),
        "mod" => Some(|a, b| NatResult::Nat(a.rem(b))),
        "pow" => Some(|a, b| NatResult::Nat(a.pow(b))),
        "beq" => Some(|a, b| NatResult::Bool(a.dec_eq(b))),
        "ble" => Some(|a, b| NatResult::Bool(a.dec_le(b))),
        _ => None,
    };
    let Some(bin) = bin else { return Ok(None) };
    let [a0, a1] = args else { return Ok(None) };
    let a0 = whnf(env, a0, budget)?;
    let a1 = whnf(env, a1, budget)?;
    match (nat_lit(&a0), nat_lit(&a1)) {
        (Some(x), Some(y)) => Ok(Some(match bin(&x, &y) {
            NatResult::Nat(n) => Term::lit(Lit::Nat(n)),
            NatResult::Bool(b) => bool_term(b),
        })),
        _ => Ok(None),
    }
}

enum NatResult {
    Nat(crate::BigNat),
    Bool(bool),
}

/// `Bool.true` / `Bool.false` as 0-level `Const`s (the corpus `Bool` ctors).
fn bool_term(b: bool) -> Term {
    let name = if b {
        Name::from_dotted("Bool.true")
    } else {
        Name::from_dotted("Bool.false")
    };
    // These constructors are nullary and level-param-free; we mint the bare
    // ConstRef directly (the native reducer is trusted TCB, design §3.2).
    Term::native_const(name)
}

/// Extract a `Nat` literal value from a whnf'd term.
fn nat_lit(t: &Term) -> Option<crate::BigNat> {
    match t.kind() {
        TermKind::Lit(Lit::Nat(n)) => Some(n.clone()),
        _ => None,
    }
}

/// Helper for tests / level instantiation parity: a `Sort` head check.
#[must_use]
pub fn is_sort(t: &Term) -> Option<Level> {
    match t.kind() {
        TermKind::Sort(l) => Some(l.clone()),
        _ => None,
    }
}
