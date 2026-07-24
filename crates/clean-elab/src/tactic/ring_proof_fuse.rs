// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Coefficient-merging (`x + x + … → n*x`) for proof-carrying ring
//! normalization (#ring-coeff-merge / #32).
//!
//! After [`ring_proof_sort::merge_sorted_chains`] flattens and sorts an
//! addition chain, same-base monomials are adjacent (e.g.
//! `a*a + a*b + a*b + b*b`). This module fuses each maximal run of `n >= 2`
//! same-base addends into a single coefficient monomial `n * base`, carrying a
//! **kernel-valid** equality proof built only from the registered,
//! zero-domain-axiom semiring lemmas (`one_mul`, `right_distrib`, `mul_assoc`,
//! `add_assoc`). No `trustedArith`, no `sorry`, no `add_decl_unchecked`.
//!
//! ## n-ary fusion by iterative folding
//!
//! Recursive bottom-up normalization may already have collapsed sub-sums into
//! coefficient monomials, so a "run" is NOT a block of def-eq-identical terms in
//! general — it is a block of terms that share one **variable base** (the
//! coefficient-stripped monomial) with possibly distinct literal coefficients.
//! For `a + a + a` the outer normalizer hands the fuser `[a, 2*a]`; for
//! `a + a*2 + a` it hands `[a, 2*a, a]` after sorting. The run is folded
//! left-to-right, one pair per step (`fuse_pair`), summing coefficients:
//!
//! ```text
//!   a   + a            = 2*a            (coeffs 1 + 1)
//!   (2*a) + a          = 3*a            (coeffs 2 + 1)
//!   …
//!   ((n-1)*base) + base = n*base
//! ```
//!
//! Each pair step `cx*base + cy*base = (cx+cy)*base`:
//!
//! 1. [`monomial_base`] gives `cx`, `cy`, and proofs that each addend equals
//!    `cx*base` / `cy*base` (peeling `one_mul` for a unit coefficient and
//!    `mul_assoc` for a product base).
//! 2. Lift those by congruence over the two addends:
//!    `cx*base + cy*base`.
//! 3. `(right_distrib cx cy base).symm : cx*base + cy*base = (cx+cy)*base`.
//!    The coefficient literal `cx+cy` appears in the proof as `Nat.add cx cy`,
//!    which the kernel reduces def-eq to the succ-literal; the emitted monomial
//!    uses the clean literal so it matches the syntactic normalizer's
//!    `Mul([Const(cx+cy), …vars])`.
//! 4. If `base` is a product `f * g`, re-associate the emitted monomial to the
//!    canonical literal-led, left-associated `((cx+cy)*f)*g`:
//!    `(mul_assoc (cx+cy) f g).symm : (cx+cy)*(f*g) = ((cx+cy)*f)*g`.
//!
//! ## Placement inside a longer chain
//!
//! A run in the middle/tail of a left-associated chain is rewritten with the
//! same congruence-lifting machinery used by `ring_proof_sort::swap_at_position`
//! (see [`lift_pair_proof`]): a tail pair `(prefix + x) + y` is re-associated
//! with `add_assoc` to `prefix + (x + y)`, the fusion is applied under
//! `congrArg (prefix +)`, and the result is lifted over any trailing addends.
//!
//! Any run with a non-literal coefficient, a missing lemma, or an unavailable
//! coefficient sum fails-closed (`None`) so `ring` reports an honest
//! `ArithmeticFailed` instead of fabricating a proof.

use super::ring_proof_carry::chain_optional;
use super::ring_proof_sort::build_op_chain;
use super::ring_proof_surface::{assoc_name, coeff_merge_entry};
use super::simp::{mk_congr_arg, mk_congr_fun, mk_eq_refl_expr, mk_eq_symm_expr, mk_eq_trans_expr};
use super::{Goal, ProofState};
use clean_kernel::name::Name;
use clean_kernel::{Expr, ExprKind};

/// Shared context for fusion, mirroring `ring_proof_sort::MergeCtx`.
pub(super) struct FuseCtx<'a> {
    pub state: &'a ProofState,
    pub goal: &'a Goal,
    /// The addition operator joining the monomials (`Nat.add`, ...).
    pub add_op: &'a str,
    /// `Expr::const_` head for the addition operator (e.g. `Nat.add`).
    pub head: &'a Expr,
    /// Implicit-argument prefix applied before the two explicit operands
    /// (empty for concrete carrier operators).
    pub prefix: &'a [Expr],
}

/// Fuse maximal runs of same-base adjacent addends in `terms`, returning the
/// rewritten term list and a proof `chain(terms) = chain(result)`.
///
/// `terms` is the already-sorted addend list (so same-base monomials are
/// adjacent). A run of `n >= 2` same-base addends is folded to one coefficient
/// monomial for ANY `n` (#32). Returns `None` if a run is encountered that the
/// fuser cannot soundly handle (non-literal coefficient or missing lemma), so
/// the caller fails-closed.
///
/// ENSURES: On `Some((new_terms, proof))`, `proof` (when present) is a
/// kernel-checkable term of type `chain(terms) = chain(new_terms)` and
/// `new_terms` has no two same-base adjacent elements.
pub(super) fn fuse_like_terms(
    ctx: &FuseCtx<'_>,
    terms: &[Expr],
) -> Option<(Vec<Expr>, Option<Expr>)> {
    let entry = coeff_merge_entry(ctx.add_op)?;
    let mut i = 0usize;
    while i < terms.len() {
        // A "run" is a maximal block of adjacent addends that share the same
        // *variable base* (coefficient-stripped monomial), e.g. `a`, `2*a`,
        // `a` all have base `a`. Recursive bottom-up normalization already
        // collapsed some sub-sums into coefficient monomials, so a run is NOT
        // a block of def-eq-identical terms in general — it is a block of
        // same-base terms with possibly distinct literal coefficients.
        let base_i = match monomial_base(ctx, &terms[i], entry.mul_op) {
            Some((_, base, _)) => base,
            None => {
                i += 1;
                continue;
            }
        };
        let mut j = i + 1;
        while j < terms.len() {
            match monomial_base(ctx, &terms[j], entry.mul_op) {
                Some((_, base_j, _)) if ctx.state.is_def_eq(ctx.goal, &base_i, &base_j) => {
                    j += 1;
                }
                _ => break,
            }
        }
        let run_len = j - i;
        if run_len >= 2 {
            // Fold the run `terms[i..j]` into a single coefficient monomial,
            // then lift it into the full chain at position [i, j).
            let (rewritten, step_proof) = fuse_run_at(ctx, terms, i, run_len)?;
            // Recurse: the rewritten chain may expose further fusable runs.
            let (final_terms, rest_proof) = fuse_like_terms(ctx, &rewritten)?;
            let total = chain_optional(ctx.state, ctx.goal, step_proof, rest_proof);
            return Some((final_terms, total));
        }
        i = j;
    }
    Some((terms.to_vec(), None))
}

/// Fuse the run `terms[start .. start+run_len]` (all sharing one variable base)
/// into a single coefficient monomial `n * base`, producing the rewritten term
/// list and a proof `chain(terms) = chain(rewritten)`.
///
/// Generalized from `k = 2` to ANY `n >= 2` by ITERATIVE left-to-right folding
/// (#ring-coeff-merge / #32). Because recursive bottom-up normalization may
/// already have collapsed sub-sums into coefficient monomials, the run is a
/// block of same-base addends with possibly distinct literal coefficients,
/// e.g. for `a + a + a` the outer normalizer hands the fuser `[a, 2*a]`. Each
/// step collapses one adjacent pair via [`fuse_pair`], summing coefficients:
///
/// ```text
///   a   + a            = 2*a           (coeffs 1 + 1)
///   (2*a) + a          = 3*a           (coeffs 2 + 1)
///   …
/// ```
///
/// Each step collapses the pair at positions `(start, start+1)` of the working
/// chain (the left element is the running coefficient monomial, the right the
/// next same-base addend). Each pair fusion is lifted into the full chain by
/// the existing [`lift_pair_proof`] machinery and the per-step proofs are
/// chained with `Eq.trans`. Any missing lemma / unavailable coefficient makes a
/// step return `None`, so the whole fuser fails-closed.
fn fuse_run_at(
    ctx: &FuseCtx<'_>,
    terms: &[Expr],
    start: usize,
    run_len: usize,
) -> Option<(Vec<Expr>, Option<Expr>)> {
    if run_len < 2 {
        return None;
    }

    // `working` is the current term list; the running coefficient monomial
    // lives at index `start`, and the same-base addends still to be folded
    // occupy `start+1 ..`. We fold one addend per iteration.
    let mut working: Vec<Expr> = terms.to_vec();
    let mut proof: Option<Expr> = None;
    for _ in 0..(run_len - 1) {
        // The pair to collapse is `(working[start], working[start+1])`, two
        // same-base addends (the left is the accumulator `c*base`).
        let left = working[start].clone();
        let right = working[start + 1].clone();
        let (fused, pair_proof) = fuse_pair(ctx, &left, &right)?;

        // Lift `pair_proof : left + right = fused` into the working chain. The
        // pair occupies (start, start+1); `lift_pair_proof` takes the index of
        // the *second* run element.
        let lifted = lift_pair_proof(ctx, &working, start + 1, &fused, pair_proof?)?;

        // Collapse the pair in the working term list: [.., fused, ..rest].
        let mut next: Vec<Expr> = Vec::with_capacity(working.len() - 1);
        next.extend_from_slice(&working[..start]);
        next.push(fused);
        next.extend_from_slice(&working[start + 2..]);
        working = next;

        proof = chain_optional(ctx.state, ctx.goal, proof, Some(lifted));
    }

    Some((working, proof))
}

/// Lift a standalone pair-fusion proof `(terms[j-1] + terms[j]) = fused` to the
/// full chain `chain(terms) = chain(terms with [j-1,j] → fused)`.
///
/// Mirrors `ring_proof_sort::swap_at_position`: recurse into the prefix
/// sub-chain ending at the pair, then lift congruence over each trailing addend.
fn lift_pair_proof(
    ctx: &FuseCtx<'_>,
    terms: &[Expr],
    j: usize,
    fused: &Expr,
    pair_proof: Expr,
) -> Option<Expr> {
    let n = terms.len();

    if j == n - 1 {
        // The pair is the tail: `(chain(terms[..n-2]) + a) + b`.
        let a = &terms[n - 2];
        let b = &terms[n - 1];
        if n == 2 {
            // Whole expression is just `a + b`; the standalone proof already
            // proves `a + b = fused`.
            return Some(pair_proof);
        }
        let inner_prefix = build_op_chain(ctx.head, ctx.prefix, &terms[..n - 2]);
        return fuse_tail_pair(ctx, &inner_prefix, a, b, fused, &pair_proof);
    }

    // The pair is in the middle: recurse on `terms[..j+1]` (pair now at its
    // tail), producing the rewritten inner sub-chain, then lift over the
    // remaining trailing addends `terms[j+1..]`.
    let inner_terms = &terms[..j + 1];
    let inner_proof = lift_pair_proof(ctx, inner_terms, j, fused, pair_proof)?;

    // After fusing the pair at (j-1, j), the inner term list shrinks by one:
    // [t0..t_{j-2}, fused].
    let fused_inner: Vec<Expr> = {
        let mut v: Vec<Expr> = terms[..j - 1].to_vec();
        v.push(fused.clone());
        v
    };

    let mut lifted = inner_proof;
    for k in (j + 1)..n {
        let head_fn = apply_head(ctx, &[]);
        let old_inner = build_op_chain(ctx.head, ctx.prefix, &terms[..k]);
        // new inner up to k: fused_inner ++ terms[j+1..k]
        let new_inner = {
            let mut v: Vec<Expr> = fused_inner.clone();
            v.extend_from_slice(&terms[j + 1..k]);
            build_op_chain(ctx.head, ctx.prefix, &v)
        };
        let h_f = mk_congr_arg(
            ctx.state, ctx.goal, &head_fn, &old_inner, &new_inner, &lifted,
        )?;
        let f_old = apply_head(ctx, &[old_inner]);
        let f_new = apply_head(ctx, &[new_inner]);
        lifted = mk_congr_fun(ctx.state, ctx.goal, &f_old, &f_new, &terms[k], &h_f)?;
    }
    Some(lifted)
}

/// Fuse a tail pair `(prefix + a) + b` into `prefix + fused` given the
/// standalone `pair_proof : a + b = fused`.
///
/// Proof:
/// 1. `add_assoc prefix a b : (prefix + a) + b = prefix + (a + b)`.
/// 2. `congrArg (prefix +) pair_proof : prefix + (a + b) = prefix + fused`.
///
/// The emitted `prefix + fused` chain equals `build_op_chain(prefix_terms ++ [fused])`.
fn fuse_tail_pair(
    ctx: &FuseCtx<'_>,
    inner_prefix: &Expr,
    a: &Expr,
    b: &Expr,
    fused: &Expr,
    pair_proof: &Expr,
) -> Option<Expr> {
    let assoc = assoc_name(ctx.add_op)?;
    ctx.state.env().get_const(&Name::from_string(assoc))?;

    // Step 1: add_assoc inner_prefix a b : (inner_prefix + a) + b = inner_prefix + (a + b)
    let assoc_proof = Expr::apps(
        Expr::const_(Name::from_string(assoc), vec![]),
        [inner_prefix.clone(), a.clone(), b.clone()],
    );

    // Step 2: congrArg (inner_prefix +) (a + b = fused).
    let prefix_fn = apply_head(ctx, std::slice::from_ref(inner_prefix));
    let ab = apply_head(ctx, &[a.clone(), b.clone()]);
    let congr = mk_congr_arg(ctx.state, ctx.goal, &prefix_fn, &ab, fused, pair_proof)?;

    mk_eq_trans_expr(ctx.state, ctx.goal, &assoc_proof, &congr)
}

/// Decompose an addend into its literal coefficient `c`, its canonical
/// variable base `base`, and a proof `addend = c * base` (in the **un-**
/// reassociated `c * base` form, where `base` is the bare product `f * g …`
/// or an atom).
///
/// Recognizes the canonical monomial layouts the normalizer/fuser produce:
/// - atom `a`              → `(1, a,   (one_mul a).symm : a = 1*a)`
/// - `c * a` (c literal)   → `(c, a,   refl : c*a = c*a)`
/// - product `f * g`       → `(1, f*g, (one_mul (f*g)).symm : f*g = 1*(f*g))`
/// - `(c * f) * g`         → `(c, f*g, (mul_assoc c f g) : (c*f)*g = c*(f*g))`
///
/// Returns `None` for any shape outside this surface (e.g. a non-literal
/// coefficient), so the fuser fails-closed.
fn monomial_base(ctx: &FuseCtx<'_>, addend: &Expr, mul_op: &str) -> Option<(u64, Expr, Expr)> {
    let env = ctx.state.env();
    let entry = coeff_merge_entry(ctx.add_op)?;

    if let Some((f, g)) = as_binary_mul(addend, mul_op) {
        // `f * g`: either a literal-led `(c*f')*g` or a bare product `f*g`.
        if let Some(c) = as_nat_lit(&f) {
            // `c * g` (atom base `g`): already `c*base`, proof refl.
            let refl = mk_eq_refl_expr(ctx.state, ctx.goal, addend)?;
            return Some((c, g, refl));
        }
        if let Some((cf, ff)) = as_binary_mul(&f, mul_op) {
            if let Some(c) = as_nat_lit(&cf) {
                // `(c * ff) * g` → `(c, ff*g, mul_assoc c ff g : (c*ff)*g = c*(ff*g))`.
                env.get_const(&Name::from_string(entry.mul_assoc))?;
                let base = mk_mul(mul_op, &ff, &g);
                let assoc_proof = Expr::apps(
                    Expr::const_(Name::from_string(entry.mul_assoc), vec![]),
                    [cf.clone(), ff.clone(), g.clone()],
                );
                return Some((c, base, assoc_proof));
            }
        }
        // Bare product `f * g`, coefficient 1: `f*g = 1*(f*g)`.
        env.get_const(&Name::from_string(entry.one_mul))?;
        let base = mk_mul(mul_op, &f, &g);
        let one_mul = Expr::apps(
            Expr::const_(Name::from_string(entry.one_mul), vec![]),
            [base.clone()],
        );
        let proof = mk_eq_symm_expr(ctx.state, ctx.goal, &one_mul)?;
        return Some((1, base, proof));
    }

    // Atom (variable/const), coefficient 1: `a = 1*a`.
    if as_nat_lit(addend).is_some() {
        // A bare literal addend has empty variable base — not a coefficient
        // monomial; leave it for the syntactic constant-folding path.
        return None;
    }
    env.get_const(&Name::from_string(entry.one_mul))?;
    let one_mul = Expr::apps(
        Expr::const_(Name::from_string(entry.one_mul), vec![]),
        [addend.clone()],
    );
    let proof = mk_eq_symm_expr(ctx.state, ctx.goal, &one_mul)?;
    Some((1, addend.clone(), proof))
}

/// Fuse two same-base addends `x + y` into one coefficient monomial
/// `(cx + cy) * base`, returning the canonical fused expression and the proof.
///
/// Generalizes the old `k = 2` `fuse_two` to ANY same-base pair with literal
/// coefficients `cx, cy >= 1` (#ring-coeff-merge / #32):
///
/// 1. [`monomial_base`] gives `px : x = cx*base` and `py : y = cy*base`.
/// 2. Lift `px`/`py` by congruence over the two addends:
///    `x + y = cx*base + cy*base`.
/// 3. `(right_distrib cx cy base).symm : cx*base + cy*base = (cx+cy)*base`. The
///    coefficient literal `cx+cy` appears in the proof as `Nat.add cx cy`,
///    which the kernel reduces def-eq to the literal; the emitted monomial uses
///    the clean literal `(cx+cy)` so it matches the normalizer's
///    `Mul([Const(cx+cy), …vars])`.
/// 4. If `base` is a product `f * g`, re-associate the emitted monomial to the
///    canonical literal-led, left-associated form `((cx+cy)*f)*g`:
///    `(mul_assoc (cx+cy) f g).symm : (cx+cy)*(f*g) = ((cx+cy)*f)*g`.
fn fuse_pair(ctx: &FuseCtx<'_>, x: &Expr, y: &Expr) -> Option<(Expr, Option<Expr>)> {
    let entry = coeff_merge_entry(ctx.add_op)?;
    let env = ctx.state.env();
    env.get_const(&Name::from_string(entry.right_distrib))?;

    let (cx, base_x, px) = monomial_base(ctx, x, entry.mul_op)?;
    let (cy, base_y, py) = monomial_base(ctx, y, entry.mul_op)?;
    // The run grouping guarantees same base; re-check def-eq for safety.
    if !ctx.state.is_def_eq(ctx.goal, &base_x, &base_y) {
        return None;
    }
    let base = base_x;
    let cx_lit = Expr::nat_lit(cx);
    let cy_lit = Expr::nat_lit(cy);
    let sum = cx.checked_add(cy)?;
    let sum_lit = Expr::nat_lit(sum);

    let cx_base = mk_mul(entry.mul_op, &cx_lit, &base);
    let cy_base = mk_mul(entry.mul_op, &cy_lit, &base);

    // Right addend: `x + y = x + cy*base` via congrArg over `(x +) ·`.
    let add_x = apply_head(ctx, std::slice::from_ref(x));
    let right_step = mk_congr_arg(ctx.state, ctx.goal, &add_x, y, &cy_base, &py)?;

    // Left addend: lift `x = cx*base` under `λ z => z + cy*base`.
    let add_head = apply_head(ctx, &[]);
    let add_x_to_cx = mk_congr_arg(ctx.state, ctx.goal, &add_head, x, &cx_base, &px)?;
    let f_old = apply_head(ctx, std::slice::from_ref(x));
    let f_new = apply_head(ctx, std::slice::from_ref(&cx_base));
    let left_step = mk_congr_fun(ctx.state, ctx.goal, &f_old, &f_new, &cy_base, &add_x_to_cx)?;

    // x + y = x + cy*base = cx*base + cy*base.
    let to_distrib_form = mk_eq_trans_expr(ctx.state, ctx.goal, &right_step, &left_step)?;

    // (right_distrib cx cy base).symm : cx*base + cy*base = (cx+cy)*base.
    let right_distrib_proof = Expr::apps(
        Expr::const_(Name::from_string(entry.right_distrib), vec![]),
        [cx_lit.clone(), cy_lit.clone(), base.clone()],
    );
    let distrib_symm = mk_eq_symm_expr(ctx.state, ctx.goal, &right_distrib_proof)?;
    let to_coeff = mk_eq_trans_expr(ctx.state, ctx.goal, &to_distrib_form, &distrib_symm)?;

    if let Some((f, g)) = as_binary_mul(&base, entry.mul_op) {
        env.get_const(&Name::from_string(entry.mul_assoc))?;
        // mul_assoc (cx+cy) f g : ((cx+cy)*f)*g = (cx+cy)*(f*g)  ⇒
        //   symm : (cx+cy)*(f*g) = ((cx+cy)*f)*g.
        let mul_assoc_proof = Expr::apps(
            Expr::const_(Name::from_string(entry.mul_assoc), vec![]),
            [sum_lit.clone(), f.clone(), g.clone()],
        );
        let assoc_symm = mk_eq_symm_expr(ctx.state, ctx.goal, &mul_assoc_proof)?;
        let total = mk_eq_trans_expr(ctx.state, ctx.goal, &to_coeff, &assoc_symm)?;
        let fused = mk_mul(entry.mul_op, &mk_mul(entry.mul_op, &sum_lit, &f), &g);
        return Some((fused, Some(total)));
    }

    let fused = mk_mul(entry.mul_op, &sum_lit, &base);
    Some((fused, Some(to_coeff)))
}

/// If `expr` is a `Nat`/literal, return its value.
fn as_nat_lit(expr: &Expr) -> Option<u64> {
    match expr.kind() {
        ExprKind::Lit(clean_kernel::Literal::Nat(clean_kernel::BigNat::Small(n))) => Some(*n),
        _ => None,
    }
}

/// Apply the addition head to its implicit prefix and the given explicit args.
fn apply_head(ctx: &FuseCtx<'_>, args: &[Expr]) -> Expr {
    let mut all: Vec<Expr> = ctx.prefix.to_vec();
    all.extend_from_slice(args);
    Expr::apps_ref(ctx.head.clone(), &all)
}

/// Build `op lhs rhs` for a concrete two-argument carrier operator.
fn mk_mul(op_name: &str, lhs: &Expr, rhs: &Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string(op_name), vec![]),
        [lhs.clone(), rhs.clone()],
    )
}

/// If `expr` is `mul_op f g`, return `(f, g)`.
fn as_binary_mul(expr: &Expr, mul_op: &str) -> Option<(Expr, Expr)> {
    let head = expr.get_app_fn();
    let is_mul = matches!(head.kind(), ExprKind::Const(n, _) if n.to_string() == mul_op);
    if !is_mul {
        return None;
    }
    let args = expr.get_app_args();
    if args.len() < 2 {
        return None;
    }
    let n = args.len();
    Some((args[n - 2].clone(), args[n - 1].clone()))
}
