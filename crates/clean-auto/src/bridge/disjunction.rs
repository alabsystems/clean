// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Shared disjunction proof term construction helpers.
//!
//! Free functions for building Or.inl, Or.inr, Or.rec, absurd,
//! and right-associative Or chain types. Extracted from
//! `superposition_reconstruction/disjunction_helpers.rs` so both the
//! superposition and ay backend proof reconstructors can reuse them.

use clean_kernel::name::Name;
use clean_kernel::Level;
use clean_kernel::{BinderInfo, Expr};

/// Build the type of a right-associative Or chain from a slice of propositions.
///
/// `[]` → `False`
/// `[P₀]` → `P₀`
/// `[P₀, P₁]` → `Or P₀ P₁`
/// `[P₀, P₁, P₂]` → `Or P₀ (Or P₁ P₂)`
///
/// The empty chain is the empty disjunction, i.e. `False`. This makes the
/// function total: reconstruction paths that reach it with an empty tail
/// (e.g. a pivot in last position, or an empty resolvent) build a
/// `False`-typed candidate instead of aborting the whole process — the
/// kernel re-check then accepts or rejects that one declaration. This
/// replaced a production `assert!` that a Mathlib `clean check` run tripped
/// (SIGABRT on `Mathlib/Data/Subtype.lean`, SRCELAB gate 2026-08-10).
pub(crate) fn or_chain_type(props: &[Expr]) -> Expr {
    if props.is_empty() {
        return Expr::const_(Name::from_string("False"), vec![]);
    }
    if props.len() == 1 {
        props[0].clone()
    } else {
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Or"), vec![]),
                props[0].clone(),
            ),
            or_chain_type(&props[1..]),
        )
    }
}

/// Precompute suffix chain types for all positions in O(n) (#2441).
///
/// Returns a Vec where `result[i] = or_chain_type(props[i..])`.
/// Built via a single right-to-left fold instead of O(n) recursive calls.
pub(crate) fn precompute_or_chain_suffixes(props: &[Expr]) -> Vec<Expr> {
    let n = props.len();
    if n == 0 {
        return vec![];
    }
    let mut suffixes = Vec::with_capacity(n);
    suffixes.resize(n, props[n - 1].clone());
    for i in (0..n - 1).rev() {
        suffixes[i] = Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Or"), vec![]),
                props[i].clone(),
            ),
            suffixes[i + 1].clone(),
        );
    }
    suffixes
}

/// Inject a proof into a specific position of a right-associative Or chain.
///
/// Given `result_props = [R₀, R₁, R₂]` and a proof of `R_pos`,
/// builds a proof of `Or R₀ (Or R₁ R₂)` using Or.inl/Or.inr chains.
///
/// Internally precomputes suffix types for O(n) total instead of O(n²) (#2441).
pub(crate) fn inject_into_or_chain(result_props: &[Expr], position: usize, proof: Expr) -> Expr {
    let suffixes = precompute_or_chain_suffixes(result_props);
    inject_into_or_chain_with_suffixes(result_props, &suffixes, position, proof)
}

/// Inject a proof into an Or chain using caller-provided precomputed suffixes.
pub(crate) fn inject_into_or_chain_with_suffixes(
    result_props: &[Expr],
    suffixes: &[Expr],
    position: usize,
    proof: Expr,
) -> Expr {
    assert!(
        position < result_props.len(),
        "inject_into_or_chain: position {} out of range (len {})",
        position,
        result_props.len()
    );
    assert_eq!(
        suffixes.len(),
        result_props.len(),
        "inject_into_or_chain: suffixes length mismatch"
    );
    if result_props.len() == 1 {
        return proof;
    }
    inject_into_or_chain_inner(result_props, suffixes, 0, position, proof)
}

/// Inner implementation using precomputed suffix types.
fn inject_into_or_chain_inner(
    result_props: &[Expr],
    suffixes: &[Expr],
    offset: usize,
    position: usize,
    proof: Expr,
) -> Expr {
    let remaining = result_props.len() - offset;
    if remaining == 1 {
        return proof;
    }
    let rest_type = &suffixes[offset + 1];
    if position == 0 {
        mk_or_inl(&result_props[offset], rest_type, &proof)
    } else {
        let inner =
            inject_into_or_chain_inner(result_props, suffixes, offset + 1, position - 1, proof);
        mk_or_inr(&result_props[offset], rest_type, &inner)
    }
}

/// Build `@Or.inl a b ha : Or a b`.
///
/// Or.inl : {a b : Prop} → a → Or a b (3 args)
pub(crate) fn mk_or_inl(a: &Expr, b: &Expr, ha: &Expr) -> Expr {
    Expr::app(
        Expr::app(
            Expr::app(Expr::const_(Name::from_string("Or.inl"), vec![]), a.clone()),
            b.clone(),
        ),
        ha.clone(),
    )
}

/// Build `@Or.inr a b hb : Or a b`.
///
/// Or.inr : {a b : Prop} → b → Or a b (3 args)
pub(crate) fn mk_or_inr(a: &Expr, b: &Expr, hb: &Expr) -> Expr {
    Expr::app(
        Expr::app(
            Expr::app(Expr::const_(Name::from_string("Or.inr"), vec![]), a.clone()),
            b.clone(),
        ),
        hb.clone(),
    )
}

/// Build `@Or.rec a b motive f_inl f_inr h`.
///
/// Or.rec (kernel recursor, no universe params for Prop elimination):
/// ```text
/// @Or.rec {a b : Prop} {motive : Or a b → Prop}
///         (f_inl : (h : a) → motive (Or.inl h))
///         (f_inr : (h : b) → motive (Or.inr h))
///         (t : Or a b) : motive t
/// ```
///
/// For constant motive (case analysis): pass `fun _ : Or a b => c` as motive.
pub(crate) fn mk_or_rec(
    a: &Expr,
    b: &Expr,
    motive: &Expr,
    f_inl: &Expr,
    f_inr: &Expr,
    h: &Expr,
) -> Expr {
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(Expr::const_(Name::from_string("Or.rec"), vec![]), a.clone()),
                        b.clone(),
                    ),
                    motive.clone(),
                ),
                f_inl.clone(),
            ),
            f_inr.clone(),
        ),
        h.clone(),
    )
}

/// Build a constant motive for Or.rec: `fun (_ : Or a b) => target`.
///
/// Used when case analysis produces the same target type in both branches.
pub(crate) fn mk_constant_or_motive(a: &Expr, b: &Expr, target: &Expr) -> Expr {
    let or_ab = Expr::app(
        Expr::app(Expr::const_(Name::from_string("Or"), vec![]), a.clone()),
        b.clone(),
    );
    // The motive body lives under the Or-rec binder, so outer loose bvars must
    // be lifted to avoid accidental capture.
    Expr::lam(BinderInfo::Default, or_ab, target.lift(1))
}

/// Build `@absurd a b ha hna : b`.
///
/// `absurd : {a : Prop} → {b : Prop} → a → ¬a → b`
///
/// Eliminates to `Sort 0` (Prop), so the universe parameter is `Level::zero()`.
pub(crate) fn mk_absurd(
    positive_prop: &Expr,
    target: &Expr,
    positive_proof: &Expr,
    negative_proof: &Expr,
) -> Expr {
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("absurd"), vec![Level::zero()]),
                    positive_prop.clone(),
                ),
                target.clone(),
            ),
            positive_proof.clone(),
        ),
        negative_proof.clone(),
    )
}

/// Build `@Classical.em p : Or p (Not p)`.
///
/// Classical excluded middle: for any proposition `p`, either `p` or `¬p` holds.
/// `Classical.em : ∀ (p : Prop), p ∨ ¬p` — no universe parameters.
pub(crate) fn mk_classical_em(p: &Expr) -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("Classical.em"), vec![]),
        p.clone(),
    )
}

/// Reorder a proof of `Or a b` into a proof of `Or b a`.
///
/// Builds `Or.rec` with a constant motive targeting the swapped disjunction.
pub(crate) fn mk_or_swap(a: &Expr, b: &Expr, h: &Expr) -> Expr {
    let target = Expr::app(
        Expr::app(Expr::const_(Name::from_string("Or"), vec![]), b.clone()),
        a.clone(),
    );
    let motive = mk_constant_or_motive(a, b, &target);
    let f_inl = Expr::lam(
        BinderInfo::Default,
        a.clone(),
        mk_or_inr(b, a, &Expr::bvar(0)),
    );
    let f_inr = Expr::lam(
        BinderInfo::Default,
        b.clone(),
        mk_or_inl(b, a, &Expr::bvar(0)),
    );
    mk_or_rec(a, b, &motive, &f_inl, &f_inr, h)
}

/// Build `@And.intro a b ha hb : And a b`.
///
/// `And.intro : {a b : Prop} → a → b → And a b` (4 args including implicits)
pub(crate) fn mk_and_intro(a: &Expr, b: &Expr, ha: &Expr, hb: &Expr) -> Expr {
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("And.intro"), vec![]),
                    a.clone(),
                ),
                b.clone(),
            ),
            ha.clone(),
        ),
        hb.clone(),
    )
}

/// Build `@True.intro : True`.
///
/// The unique constructor for the `True` proposition. No universe parameters.
pub(crate) fn mk_true_intro() -> Expr {
    Expr::const_(Name::from_string("True.intro"), vec![])
}

/// Build `@False.elim.{u} target h : target`.
///
/// `False.elim : {p : Sort u} → False → p`
/// For Prop elimination, `u = Level::zero()`.
pub(crate) fn mk_false_elim(target: &Expr, false_proof: &Expr) -> Expr {
    Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("False.elim"), vec![Level::zero()]),
            target.clone(),
        ),
        false_proof.clone(),
    )
}

/// Build `@propext a b (@Iff.intro a b mp mpr) : a = b`.
///
/// `propext : {a b : Prop} → (a ↔ b) → a = b` — the faithful Iff-shaped form the
/// kernel prelude registers (`init_propext`, kernel commit 3a09e7b7). The two
/// directional proofs `mp : a → b` and `mpr : b → a` are packaged into the
/// biconditional via `@Iff.intro a b mp mpr : a ↔ b`, then handed to `propext`.
/// (Previously this applied the de-`Iff`'d expanded form `propext a b mp mpr`,
/// which the current kernel rejects — the reconstructed proof terms failed to
/// type-check.)
pub(crate) fn mk_propext(a: &Expr, b: &Expr, mp: &Expr, mpr: &Expr) -> Expr {
    // @Iff.intro a b mp mpr : a ↔ b
    let iff = Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("Iff.intro"), vec![]),
                    a.clone(),
                ),
                b.clone(),
            ),
            mp.clone(),
        ),
        mpr.clone(),
    );
    // @propext a b (a ↔ b)
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("propext"), vec![]),
                a.clone(),
            ),
            b.clone(),
        ),
        iff,
    )
}

/// Build `@Iff.mp a b h_iff ha : b`.
///
/// Forward direction of biconditional: given `h_iff : a ↔ b` and `ha : a`,
/// produces a proof of `b`.
///
/// `Iff.mp : {a b : Prop} → (a ↔ b) → a → b`
pub(crate) fn mk_iff_mp(a: &Expr, b: &Expr, h_iff: &Expr, ha: &Expr) -> Expr {
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(Expr::const_(Name::from_string("Iff.mp"), vec![]), a.clone()),
                b.clone(),
            ),
            h_iff.clone(),
        ),
        ha.clone(),
    )
}

/// Build `@Iff.mpr a b h_iff hb : a`.
///
/// Backward direction of biconditional: given `h_iff : a ↔ b` and `hb : b`,
/// produces a proof of `a`.
///
/// `Iff.mpr : {a b : Prop} → (a ↔ b) → b → a`
pub(crate) fn mk_iff_mpr(a: &Expr, b: &Expr, h_iff: &Expr, hb: &Expr) -> Expr {
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("Iff.mpr"), vec![]),
                    a.clone(),
                ),
                b.clone(),
            ),
            h_iff.clone(),
        ),
        hb.clone(),
    )
}

/// Build the type of a right-associative And chain from a slice of propositions.
///
/// `[P₀]` → `P₀`
/// `[P₀, P₁]` → `And P₀ P₁`
/// `[P₀, P₁, P₂]` → `And P₀ (And P₁ P₂)`
pub(crate) fn and_chain_type(props: &[Expr]) -> Expr {
    assert!(!props.is_empty(), "and_chain_type: empty props");
    if props.len() == 1 {
        props[0].clone()
    } else {
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("And"), vec![]),
                props[0].clone(),
            ),
            and_chain_type(&props[1..]),
        )
    }
}

/// Extract the `position`-th conjunct from a right-associative And chain proof.
///
/// Given `h : And a₀ (And a₁ (... (And aₙ₋₂ aₙ₋₁)))`, returns a proof of `a_position`.
///
/// Navigation: apply `And.right` `position` times to reach the sub-chain starting
/// at `a_position`, then `And.left` to extract (unless `position == total - 1`,
/// which is the innermost element with no further And wrapper).
pub(crate) fn extract_and_conjunct(h: &Expr, position: usize, total: usize) -> Expr {
    assert!(total >= 1, "extract_and_conjunct: total must be >= 1");
    assert!(
        position < total,
        "extract_and_conjunct: position {} out of range (total {})",
        position,
        total
    );
    let mut current = h.clone();
    for _ in 0..position {
        current = mk_and_right(&current);
    }
    if total > 1 && position < total - 1 {
        current = mk_and_left(&current);
    }
    current
}

/// Build an `And.intro` chain from de Bruijn variable proofs.
///
/// Used at the base case of and_neg reconstruction, where `n` nested lambda
/// binders provide proofs of each conjunct as `bvar(n-1-i)` for conjunct `i`.
///
/// Builds `And.intro a₀ (And a₁ ...) bvar(n-1) (And.intro a₁ a₂ bvar(n-2) bvar(n-3) ...)`.
pub(crate) fn build_and_chain_from_bvars(conjuncts: &[Expr], offset: usize, total: usize) -> Expr {
    let remaining = conjuncts.len() - offset;
    let proof_of_current = Expr::bvar((total - 1 - offset) as u32);

    if remaining == 1 {
        return proof_of_current;
    }

    let rest_type = and_chain_type(&conjuncts[offset + 1..]);
    let rest_proof = build_and_chain_from_bvars(conjuncts, offset + 1, total);
    mk_and_intro(
        &conjuncts[offset],
        &rest_type,
        &proof_of_current,
        &rest_proof,
    )
}

/// Extract left component from conjunction: `h.1` where `h : And a b`.
///
/// Uses structure projection (`Expr::proj("And", 0, h)`) which is the kernel
/// representation of `And.left` / `And.casesOn` for field 0.
///
/// `And.left : {a b : Prop} → And a b → a`
pub(crate) fn mk_and_left(h: &Expr) -> Expr {
    Expr::proj(Name::from_string("And"), 0, h.clone())
}

/// Extract right component from conjunction: `h.2` where `h : And a b`.
///
/// Uses structure projection (`Expr::proj("And", 1, h)`) which is the kernel
/// representation of `And.right` / `And.casesOn` for field 1.
///
/// `And.right : {a b : Prop} → And a b → b`
pub(crate) fn mk_and_right(h: &Expr) -> Expr {
    Expr::proj(Name::from_string("And"), 1, h.clone())
}

#[cfg(test)]
mod tests {
    use super::{
        inject_into_or_chain, inject_into_or_chain_with_suffixes, precompute_or_chain_suffixes,
    };
    use clean_kernel::name::Name;
    use clean_kernel::Expr;

    #[test]
    fn test_inject_into_or_chain_with_suffixes_matches_standalone_helper() {
        let props: Vec<Expr> = ["P", "Q", "R"]
            .into_iter()
            .map(|name| Expr::const_(Name::from_string(name), vec![]))
            .collect();
        let suffixes = precompute_or_chain_suffixes(&props);

        for position in 0..props.len() {
            let proof = Expr::const_(Name::from_string("proof"), vec![]);
            assert_eq!(
                inject_into_or_chain(&props, position, proof.clone()),
                inject_into_or_chain_with_suffixes(&props, &suffixes, position, proof),
                "position {position} should build the same Or-chain proof with cached suffixes",
            );
        }
    }
}
