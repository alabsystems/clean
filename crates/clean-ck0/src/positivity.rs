// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Strict-**positivity** checking (design §5.2 #2) — iterative (explicit work
//! stack, stack-safe past 20k nesting depth), fail-closed. Extracted from
//! `inductive.rs` to keep both files under the 500-line convention.

use crate::name::Name;
use crate::term::{Term, TermKind};
use crate::validate::Env;

/// True iff `t` mentions `Const(n)` for ANY `n` in `names` (iterative).
pub(crate) fn term_mentions_any(t: &Term, names: &[Name]) -> bool {
    let mut stack = vec![t.clone()];
    while let Some(cur) = stack.pop() {
        match cur.kind() {
            TermKind::Const(c) => {
                if names.iter().any(|n| n == c.name()) {
                    return true;
                }
            }
            TermKind::App(f, a) => {
                stack.push(f.clone());
                stack.push(a.clone());
            }
            TermKind::Lam(_, ty, b) | TermKind::Pi(_, ty, b) => {
                stack.push(ty.clone());
                stack.push(b.clone());
            }
            TermKind::Let(ty, v, b) => {
                stack.push(ty.clone());
                stack.push(v.clone());
                stack.push(b.clone());
            }
            TermKind::Proj(_, _, e) => stack.push(e.clone()),
            TermKind::BVar(_) | TermKind::Sort(_) | TermKind::Elim(_) | TermKind::Lit(_) => {}
        }
    }
    false
}

/// True iff `t` mentions `Const(name)` anywhere (iterative).
pub(crate) fn term_mentions(t: &Term, name: &Name) -> bool {
    let mut stack = vec![t.clone()];
    while let Some(cur) = stack.pop() {
        match cur.kind() {
            TermKind::Const(c) => {
                if c.name() == name {
                    return true;
                }
            }
            TermKind::App(f, a) => {
                stack.push(f.clone());
                stack.push(a.clone());
            }
            TermKind::Lam(_, ty, b) | TermKind::Pi(_, ty, b) => {
                stack.push(ty.clone());
                stack.push(b.clone());
            }
            TermKind::Let(ty, v, b) => {
                stack.push(ty.clone());
                stack.push(v.clone());
                stack.push(b.clone());
            }
            TermKind::Proj(_, _, e) => stack.push(e.clone()),
            TermKind::BVar(_) | TermKind::Sort(_) | TermKind::Elim(_) | TermKind::Lit(_) => {}
        }
    }
    false
}

// ---------------------------------------------------------------------------
// Strict positivity (iterative, stack-safe, fail-closed).
// ---------------------------------------------------------------------------

/// One unit of positivity work: check `term` for occurrences of `ind` under the
/// given *polarity rule*.
enum PosTask {
    /// Constructor-type level: walk the Pi telescope; each domain is checked
    /// strictly-positive, the codomain continues at ctor-type level.
    CtorType(Term),
    /// Strict-positive context: `ind` may appear, but never to the left of an
    /// arrow (any Pi domain encountered here must contain *no* occurrence).
    StrictPos(Term),
    /// No-occurrence context: `ind` may not appear at all (the domain of an arrow
    /// inside a strict-positive position).
    NoOccur(Term),
}

/// Strict-positivity check for one constructor type. Explicit work stack (no
/// native recursion), so it is stack-safe well past 20k nesting depth. Returns
/// `Err(())` on the first non-strictly-positive / negative occurrence.
///
/// `env` is consulted to resolve the **per-argument variance** of any foreign
/// container the inductive is nested through (see [`check_positivity_ctor_block`]).
pub(crate) fn check_positivity_ctor(env: &dyn Env, ind: &Name, ctor_ty: &Term) -> Result<(), ()> {
    check_positivity_ctor_block(env, std::slice::from_ref(ind), ctor_ty)
}

/// Block-aware strict positivity: every type in `block_names` must occur
/// strictly-positively in `ctor_ty`. Mirrors [`check_positivity_ctor`] but the
/// "self" set is the whole mutual block (a field that puts ANY block type to
/// the left of an arrow, or inside an argument of a block-type application, is
/// rejected). For a single-element block this is the M2 check verbatim.
///
/// **Container variance (soundness-critical).** When a block type appears as an
/// argument of a *foreign* container application `C a0 a1 …` (head `C` is a
/// known inductive, NOT a block type), the argument is only strict-positive if
/// the parent occupies a **strictly-positive parameter slot** of `C`. We do NOT
/// assume every container is covariant: a contravariant slot (e.g. the `X` of
/// `Hom (X Y) where mk : (X -> Y) -> Hom X Y`) puts the parent in a negative
/// position. We consult `env` for `C`'s constructors and verify, per slot, that
/// the parent's slot is strictly-positive in `C`; any non-strictly-positive
/// slot holding a block occurrence is rejected (fail-closed). This is what
/// catches a contravariant container nested one (or more) layers inside a
/// covariant one (`List (Hom (Tree A) (Tree A))`), where the inner container
/// stays folded and its contravariance would otherwise never be exposed.
pub(crate) fn check_positivity_ctor_block(
    env: &dyn Env,
    block_names: &[Name],
    ctor_ty: &Term,
) -> Result<(), ()> {
    let mut stack: Vec<PosTask> = vec![PosTask::CtorType(ctor_ty.clone())];
    while let Some(task) = stack.pop() {
        match task {
            PosTask::CtorType(t) => {
                // A Pi splits into a strict-positive domain and a ctor-level
                // codomain; the return type (non-Pi) permits any occurrence.
                if let TermKind::Pi(_, dom, codom) = t.kind() {
                    stack.push(PosTask::CtorType(codom.clone()));
                    stack.push(PosTask::StrictPos(dom.clone()));
                }
            }
            PosTask::StrictPos(t) => match t.kind() {
                TermKind::Pi(_, dom, codom) => {
                    // (A -> B): no block type may appear in A; B continues
                    // strict-positive.
                    stack.push(PosTask::StrictPos(codom.clone()));
                    stack.push(PosTask::NoOccur(dom.clone()));
                }
                TermKind::App(_, _) => {
                    let (head, args) = t.unfold_apps();
                    let head_is_block = matches!(head.kind(),
                        TermKind::Const(c) if block_names.iter().any(|n| n == c.name()));
                    if head_is_block {
                        // a block type applied to args: each arg must contain no
                        // occurrence of any block type (a nested/illegal use here
                        // — nesting is handled by the auxiliary construction
                        // BEFORE this block-level check runs).
                        for a in args {
                            stack.push(PosTask::NoOccur(a));
                        }
                    } else if let TermKind::Const(c) = head.kind() {
                        // Foreign container application `C a0 a1 …`. Continue
                        // strict-positive into the head, but each argument's
                        // polarity is governed by `C`'s variance in that slot:
                        // a block occurrence in a non-strictly-positive slot of
                        // `C` is rejected (fail-closed). Non-block-mentioning
                        // args stay strict-positive (their own structure may
                        // legitimately contain other strict-positive material).
                        stack.push(PosTask::StrictPos(head.clone()));
                        for (i, a) in args.iter().enumerate() {
                            if term_mentions_any(a, block_names) {
                                let slot_ok = container_param_strictly_positive(
                                    env,
                                    c.name(),
                                    i,
                                    block_names,
                                );
                                if !slot_ok {
                                    // parent sits in a non-covariant slot of `C`
                                    // ⇒ negative occurrence. Reject.
                                    return Err(());
                                }
                            }
                            stack.push(PosTask::StrictPos(a.clone()));
                        }
                    } else {
                        // general application (head is not a Const): every part
                        // is strict-positive. A block occurrence inside an
                        // argument here is conservatively allowed only if it is
                        // itself strict-positive; a block occurrence whose
                        // polarity we cannot resolve is rejected.
                        if args.iter().any(|a| term_mentions_any(a, block_names)) {
                            // Unknown head with a block occurrence in an argument:
                            // we cannot establish covariance ⇒ fail-closed.
                            return Err(());
                        }
                        stack.push(PosTask::StrictPos(head));
                        for a in args {
                            stack.push(PosTask::StrictPos(a));
                        }
                    }
                }
                TermKind::Lam(_, ty, body) => {
                    stack.push(PosTask::StrictPos(ty.clone()));
                    stack.push(PosTask::StrictPos(body.clone()));
                }
                TermKind::Let(ty, val, body) => {
                    stack.push(PosTask::StrictPos(ty.clone()));
                    stack.push(PosTask::StrictPos(val.clone()));
                    stack.push(PosTask::StrictPos(body.clone()));
                }
                TermKind::Proj(_, _, e) => stack.push(PosTask::StrictPos(e.clone())),
                TermKind::BVar(_) | TermKind::Sort(_) | TermKind::Lit(_) | TermKind::Elim(_) => {}
                TermKind::Const(_) => {} // direct occurrence is fine
            },
            PosTask::NoOccur(t) => {
                if term_mentions_any(&t, block_names) {
                    return Err(());
                }
            }
        }
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// Container variance (per-parameter strict positivity of a FOREIGN inductive).
// ---------------------------------------------------------------------------

/// True iff parameter slot `param_idx` of the already-admitted inductive
/// `container` is **strictly-positive**: across every constructor of
/// `container`, the parameter appears only strictly-positively (never to the
/// left of an arrow, and — recursively — never inside a non-strictly-positive
/// slot of a deeper container). Fail-closed: any inability to establish this
/// (unknown container, unresolvable slot, recursion-depth/visited limits)
/// returns `false`, so the caller rejects the nesting rather than admit it.
///
/// This is the variance oracle that exposes a contravariant container even when
/// it is nested (folded) inside a covariant one.
fn container_param_strictly_positive(
    env: &dyn Env,
    container: &Name,
    param_idx: usize,
    _block_names: &[Name],
) -> bool {
    let mut visited: Vec<(Name, usize)> = Vec::new();
    param_pos_in_container(env, container, param_idx, &mut visited)
}

/// Recursive worker for [`container_param_strictly_positive`]. `visited` breaks
/// cycles among mutually-referential admitted containers: a `(container, slot)`
/// already on the stack is treated as strictly-positive (it was admitted, so its
/// own recursion is positive by construction), preventing nontermination.
fn param_pos_in_container(
    env: &dyn Env,
    container: &Name,
    param_idx: usize,
    visited: &mut Vec<(Name, usize)>,
) -> bool {
    let key = (container.clone(), param_idx);
    if visited.contains(&key) {
        return true;
    }
    let n_params = match env.inductive_num_params(container) {
        Some(n) => n,
        None => return false, // unknown container ⇒ fail-closed
    };
    if u32::try_from(param_idx)
        .map(|p| p >= n_params)
        .unwrap_or(true)
    {
        // The parent is applied at an INDEX (or out-of-range) slot, not a
        // parameter. Indices are not abstracted by the aux construction and we
        // cannot certify their variance ⇒ fail-closed.
        return false;
    }
    let ctors = match env.inductive_constructors(container) {
        Some(cs) => cs,
        None => return false,
    };
    visited.push(key);
    let ok = ctors.iter().all(|(_, ctor_ty)| {
        // The parameter `param_idx` is bound by the `param_idx`-th leading Pi of
        // the ctor type (0 = outermost). Scan the ctor for strict-positivity of
        // that bound variable.
        param_pos_in_ctor(env, ctor_ty, param_idx, n_params, visited)
    });
    visited.pop();
    ok
}

/// Strict-positivity of the bound variable that the `param_idx`-th leading Pi of
/// `ctor_ty` introduces, scanned over the whole ctor type. `n_params` leading
/// Pis are the container's parameters; fields follow. Returns `false` on the
/// first non-strictly-positive use.
fn param_pos_in_ctor(
    env: &dyn Env,
    ctor_ty: &Term,
    param_idx: usize,
    n_params: u32,
    visited: &mut Vec<(Name, usize)>,
) -> bool {
    // `level` = number of binders enclosing the current subterm, counted from
    // the ctor top. The parameter introduced by leading Pi `param_idx` is, at a
    // point under `level` binders, the de Bruijn index `level - 1 - param_idx`.
    // We track `level` explicitly; a use of that index left-of-arrow (NoOccur),
    // or in a non-strictly-positive slot of a deeper container, is a failure.
    let n_params_usize = usize::try_from(n_params).unwrap_or(usize::MAX);
    let mut level: usize = 0;
    let mut cur = ctor_ty.clone();
    // Descend the parameter Pis (their domains may not mention an earlier param
    // negatively, but params-of-params are out of scope here: a parameter type
    // mentioning `param_idx` would itself be a higher-order use; treat any such
    // mention conservatively via the field scan below by including the domains).
    let mut domains: Vec<(Term, usize)> = Vec::new();
    while let TermKind::Pi(_, dom, codom) = cur.kind() {
        domains.push((dom.clone(), level));
        level = level.saturating_add(1);
        cur = codom.clone();
        if domains.len() >= n_params_usize {
            // remaining telescope (fields + codomain) scanned below from here.
            break;
        }
    }
    // Scan every parameter domain for strict-positivity of the target variable.
    // (Parameter domains are themselves left-of-nothing here; a parameter type
    // mentioning the target left-of-arrow would be a higher-order negative use.)
    for (dom, lvl) in &domains {
        if !bvar_pos_strict(env, dom, param_idx, *lvl, visited) {
            return false;
        }
    }
    // Walk the remaining FIELD telescope at ctor-type polarity: each field domain
    // is a *strictly-positive* position (the parameter may appear there directly,
    // e.g. `head : A` in `List.cons`), the codomain continues at ctor-type
    // polarity. Crucially this is NOT the same as `bvar_pos_strict`, whose Pi
    // branch treats a domain as left-of-arrow (NoOccur). Conflating the two is
    // what made the oracle misread a plain field of type `A` as a negative
    // occurrence (over-rejecting covariant nestings like `List (Box (Tree A))`).
    bvar_ctortype_strict(env, &cur, param_idx, level, visited)
}

/// Walk a constructor FIELD telescope at "ctor-type" polarity, checking
/// strict-positivity of the target parameter variable. Each Pi here introduces a
/// constructor field: its DOMAIN is a strictly-positive position (checked by
/// [`bvar_pos_strict`], which allows the target to appear but never left of an
/// arrow *inside* that field), and its CODOMAIN continues at ctor-type polarity.
/// The final non-Pi (the constructor's return type) permits any occurrence of the
/// parameter, so it needs no further scan. Returns `false` on the first violation.
fn bvar_ctortype_strict(
    env: &dyn Env,
    t: &Term,
    param_idx: usize,
    level: usize,
    visited: &mut Vec<(Name, usize)>,
) -> bool {
    let mut cur = t.clone();
    let mut lvl = level;
    while let TermKind::Pi(_, dom, codom) = cur.kind() {
        // Field domain: strictly-positive position (target may appear, but not
        // left-of-arrow within the field, and only in covariant container slots).
        if !bvar_pos_strict(env, dom, param_idx, lvl, visited) {
            return false;
        }
        lvl = lvl.saturating_add(1);
        cur = codom.clone();
    }
    // Constructor return type: any occurrence of the parameter is fine.
    true
}

/// Strict-positivity scan for the parameter variable `param_idx` (introduced by
/// the `param_idx`-th leading Pi of the enclosing ctor) within `t`, where `t`
/// sits under `level` binders from the ctor top. Mirrors the StrictPos rules:
/// the variable may appear, but not left-of-arrow, and inside a deeper container
/// only in a strictly-positive slot. Returns `false` on any violation.
fn bvar_pos_strict(
    env: &dyn Env,
    t: &Term,
    param_idx: usize,
    level: usize,
    visited: &mut Vec<(Name, usize)>,
) -> bool {
    match t.kind() {
        TermKind::Pi(_, dom, codom) => {
            // domain is left-of-arrow ⇒ no occurrence of the target permitted.
            if bvar_mentions(dom, param_idx, level) {
                return false;
            }
            bvar_pos_strict(env, codom, param_idx, level.saturating_add(1), visited)
        }
        TermKind::App(_, _) => {
            let (head, args) = t.unfold_apps();
            match head.kind() {
                TermKind::Const(c) => {
                    for (i, a) in args.iter().enumerate() {
                        if bvar_mentions(a, param_idx, level) {
                            // target appears in slot `i` of foreign container `c`:
                            // that slot must itself be strictly-positive.
                            if !param_pos_in_container(env, c.name(), i, visited) {
                                return false;
                            }
                        }
                        if !bvar_pos_strict(env, a, param_idx, level, visited) {
                            return false;
                        }
                    }
                    true
                }
                _ => {
                    // non-Const head applied to args: if the target appears in any
                    // argument we cannot certify covariance ⇒ fail-closed.
                    if args.iter().any(|a| bvar_mentions(a, param_idx, level)) {
                        return false;
                    }
                    bvar_pos_strict(env, &head, param_idx, level, visited)
                        && args
                            .iter()
                            .all(|a| bvar_pos_strict(env, a, param_idx, level, visited))
                }
            }
        }
        TermKind::Lam(_, ty, body) => {
            bvar_pos_strict(env, ty, param_idx, level, visited)
                && bvar_pos_strict(env, body, param_idx, level.saturating_add(1), visited)
        }
        TermKind::Let(ty, val, body) => {
            bvar_pos_strict(env, ty, param_idx, level, visited)
                && bvar_pos_strict(env, val, param_idx, level, visited)
                && bvar_pos_strict(env, body, param_idx, level.saturating_add(1), visited)
        }
        TermKind::Proj(_, _, e) => bvar_pos_strict(env, e, param_idx, level, visited),
        TermKind::BVar(_)
        | TermKind::Sort(_)
        | TermKind::Lit(_)
        | TermKind::Elim(_)
        | TermKind::Const(_) => true,
    }
}

/// True iff the de Bruijn variable that refers to the ctor's `param_idx`-th
/// leading-Pi parameter occurs anywhere in `t`, where `t` sits under `level`
/// binders from the ctor top. The target index *at this level* is
/// `level - 1 - param_idx`; it shifts as we descend further binders inside `t`.
fn bvar_mentions(t: &Term, param_idx: usize, level: usize) -> bool {
    // target index at the enclosing level, if representable.
    let base = match level.checked_sub(param_idx).and_then(|x| x.checked_sub(1)) {
        Some(b) => b,
        None => return false, // parameter not yet in scope here
    };
    // Walk with an explicit extra-binder counter so the target index shifts by
    // the number of binders descended INSIDE `t`.
    let mut stack: Vec<(Term, usize)> = vec![(t.clone(), 0)];
    while let Some((cur, extra)) = stack.pop() {
        let target = base.saturating_add(extra);
        match cur.kind() {
            TermKind::BVar(i) => {
                if usize::try_from(*i).map(|iv| iv == target).unwrap_or(false) {
                    return true;
                }
            }
            TermKind::App(f, a) => {
                stack.push((f.clone(), extra));
                stack.push((a.clone(), extra));
            }
            TermKind::Lam(_, ty, b) | TermKind::Pi(_, ty, b) => {
                stack.push((ty.clone(), extra));
                stack.push((b.clone(), extra.saturating_add(1)));
            }
            TermKind::Let(ty, v, b) => {
                stack.push((ty.clone(), extra));
                stack.push((v.clone(), extra));
                stack.push((b.clone(), extra.saturating_add(1)));
            }
            TermKind::Proj(_, _, e) => stack.push((e.clone(), extra)),
            TermKind::Const(_) | TermKind::Sort(_) | TermKind::Elim(_) | TermKind::Lit(_) => {}
        }
    }
    false
}
