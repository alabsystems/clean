// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Built-in `List` simp lemmas (split from `lemmas_builtin.rs`).

use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Expr, Level};

use super::lemmas_builtin::push_if_present;
use super::types::{SimpConfig, SimpIndexMode, SimpLemma};
use crate::tactic::core::ProofState;

/// Collect built-in List simp lemmas: `List.append_nil`, the `List.length_*`
/// family, `List.reverse_reverse`, and `List.map_map`.
///
/// On `List.append_nil : xs ++ [] = xs` specifically: the reducing
/// direction `[] ++ xs = xs` closes by ι-reduction (rfl) without a lemma, but
/// the symbolic-tail direction is stuck on the recursion target and needs the
/// kernel-proved `List.append_nil` theorem (registered, axiom-free, by
/// `init_list_ops`).
///
/// The pattern is the BARE-op `@List.append.{u_simp} ?α ?xs (@List.nil.{u_simp}
/// ?α)`. simp's `reduce_op_projection_head` peels the `HAppend.hAppend`
/// typeclass projection off the goal `xs ++ []` to expose bare `List.append`
/// before unifying — the exact mechanism by which the bare-`Nat.add` Nat lemmas
/// match `HAdd`-headed goals. The `u_simp` level param is solved by the unifier
/// and re-applied to the reconstructed `@List.append_nil.{u_simp} α xs` proof
/// (the universe-polymorphic path already handled for `Eq.{u_simp}`/`ite`).
///
/// SOUNDNESS: the pattern's 2nd append arg is literally `@List.nil ?α` (sharing
/// the SAME `?α` as the list) and the RHS is the 1st arg `?xs`, so it only
/// fires on `xs ++ []` and rewrites to `xs`. It cannot match `xs ++ ys` (ys not
/// nil ⇒ unify fails) nor synthesize `[]` from `[] ++ xs`. The reconstructed
/// proof is the kernel-checked `List.append_nil`; `close_goal`/`add_decl`
/// re-verify, so any mis-assembly fails closed.
pub(crate) fn collect_list_lemmas(state: &ProofState, config: &SimpConfig) -> Vec<SimpLemma> {
    let mut lemmas = Vec::new();

    // List.append_nil: xs ++ [] = xs
    //
    // BVar(1) ↦ ?α (implicit, applied FIRST — matches `{α}`),
    // BVar(0) ↦ ?xs (explicit, applied LAST — matches `(xs)`).
    // The reverse-order proof reconstruction in `simp/expr.rs` applies
    // BVar(1) then BVar(0), assembling `@List.append_nil α xs`.
    push_if_present(state, config, &mut lemmas, "List.append_nil", || {
        SimpLemma {
            name: Name::from_string("List.append_nil"),
            lhs: make_list_append_nil_pattern(),
            rhs: Expr::bvar(0),
            // `List α : Type u_simp` — left as None; simp infers the carrier and
            // the kernel re-check governs soundness (mirrors Bool/Prop lemmas).
            eq_type: None,
            proof_expr: None,
            // B103: nil-operand identity — same WHNF-rotted-key disease as the
            // Nat literal-operand identities (`List.append ?xs nil` δ-unfolds
            // to its stuck `List.rec` body under the key path), so star-keyed.
            index_mode: SimpIndexMode::Unindexed,
            priority: 100,
        }
    });

    // List.length_nil: (@List.nil α).length = 0
    //
    // BVar(0) ↦ ?α (the only metavar). The proof reconstructs
    // `@List.length_nil.{u_simp} α`.
    push_if_present(state, config, &mut lemmas, "List.length_nil", || {
        SimpLemma {
            name: Name::from_string("List.length_nil"),
            lhs: make_list_length_nil_pattern(),
            rhs: Expr::const_(Name::from_string("Nat.zero"), vec![]),
            eq_type: Some(Expr::const_(Name::from_string("Nat"), vec![])),
            proof_expr: None,
            // B103: nil-operand identity — its pattern ι-collapses fully to
            // `Nat.zero` under the key path (a bogus-specific key), so
            // star-keyed like the Nat literal-operand identities.
            index_mode: SimpIndexMode::Unindexed,
            priority: 100,
        }
    });

    // List.length_cons: (@List.cons α x xs).length = Nat.succ xs.length
    //
    // BVar(2) ↦ ?α, BVar(1) ↦ ?x, BVar(0) ↦ ?xs (reverse-applied as α x xs).
    // The proof reconstructs `@List.length_cons.{u_simp} α x xs`.
    push_if_present(state, config, &mut lemmas, "List.length_cons", || {
        SimpLemma {
            name: Name::from_string("List.length_cons"),
            lhs: make_list_length_cons_pattern(),
            rhs: Expr::app(
                Expr::const_(Name::from_string("Nat.succ"), vec![]),
                make_list_length_app(Expr::bvar(2), Expr::bvar(0)),
            ),
            eq_type: Some(Expr::const_(Name::from_string("Nat"), vec![])),
            proof_expr: None,
            index_mode: SimpIndexMode::Normal,
            priority: 100,
        }
    });

    // List.length_append: (xs ++ ys).length = xs.length + ys.length
    //
    // BVar(2) ↦ ?α, BVar(1) ↦ ?xs, BVar(0) ↦ ?ys (reverse-applied as α xs ys).
    // The proof reconstructs `@List.length_append.{u_simp} α xs ys`.
    //
    // The goal's `++`/`+` are HAppend/HAdd-projection-headed; simp's
    // `reduce_op_projection_head` peels the typeclass projections off the goal
    // to expose bare `List.append`/`Nat.add` before unifying — the same path
    // the bare-`Nat.add` lemmas and `List.append_nil` already rely on. The
    // bare-`Nat.add` RHS is def-eq to the goal's `HAdd`-headed RHS, so after the
    // rewrite the goal becomes `a = a`, closed by the existing `eq_self` lemma.
    push_if_present(state, config, &mut lemmas, "List.length_append", || {
        SimpLemma {
            name: Name::from_string("List.length_append"),
            lhs: make_list_length_append_pattern(),
            rhs: Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("Nat.add"), vec![]),
                    make_list_length_app(Expr::bvar(2), Expr::bvar(1)),
                ),
                make_list_length_app(Expr::bvar(2), Expr::bvar(0)),
            ),
            eq_type: Some(Expr::const_(Name::from_string("Nat"), vec![])),
            proof_expr: None,
            index_mode: SimpIndexMode::Normal,
            priority: 100,
        }
    });

    // List.reverse_reverse: xs.reverse.reverse = xs
    //
    // BVar(1) ↦ ?α (implicit, applied FIRST), BVar(0) ↦ ?xs (explicit, applied
    // LAST). The proof reconstructs `@List.reverse_reverse.{u_simp} α xs`
    // (kernel-proved by `init_list_reverse_map_lemmas`, axiom-free). The
    // rewrite leaves `xs = xs`, closed by the existing `eq_self` lemma.
    //
    // SOUNDNESS: the pattern's inner argument is literally
    // `@List.reverse ?α ?xs` (same `?α` as the outer), so it fires only on a
    // double reverse and rewrites to the inner operand; the reconstructed
    // proof is the kernel-checked theorem and `close_goal`/`add_decl`
    // re-verify, so any mis-assembly fails closed.
    push_if_present(state, config, &mut lemmas, "List.reverse_reverse", || {
        SimpLemma {
            name: Name::from_string("List.reverse_reverse"),
            lhs: make_list_reverse_reverse_pattern(),
            rhs: Expr::bvar(0),
            eq_type: None,
            proof_expr: None,
            // `List.reverse` δ-unfolds to a stuck `reverseAux`/`List.rec` body
            // under the discrimination-tree key path (the B103 WHNF-rot
            // disease), so star-keyed like `List.append_nil`; still guarded by
            // the unifier + def-eq check + kernel re-verification.
            index_mode: SimpIndexMode::Unindexed,
            priority: 100,
        }
    });

    // List.map_map: (xs.map f).map g = xs.map (fun x => g (f x))
    //
    // BVar layout mirrors the declaration's binder order
    // (`{α β γ} (g) (f) (xs)`): ?α=BVar(5), ?β=BVar(4), ?γ=BVar(3),
    // ?g=BVar(2), ?f=BVar(1), ?xs=BVar(0). The RHS spells the fused function
    // as the raw lambda `fun x => g (f x)` — exactly what Clean's elaborator
    // desugars `g ∘ f` to — so after the rewrite the goal's two sides are
    // syntactically identical and `eq_self` closes it.
    //
    // Unlike the single-`u_simp` builtins, the pattern spells the
    // DECLARATION's own level params (`u`,`v`,`w`): `List.map_map` needs three
    // independent levels, and `resolve_lemma_level` resolves decl params under
    // their own names first (the environment-pattern convention), so the
    // unifier's per-name solutions flow straight into the reconstructed
    // `@List.map_map.{u,v,w}` proof head.
    push_if_present(state, config, &mut lemmas, "List.map_map", || SimpLemma {
        name: Name::from_string("List.map_map"),
        lhs: make_list_map_map_pattern(),
        rhs: make_list_map_map_rhs(),
        eq_type: None,
        proof_expr: None,
        // `List.map` δ-unfolds to a stuck `List.rec` body under the key path
        // (same B103 WHNF-rot class), so star-keyed.
        index_mode: SimpIndexMode::Unindexed,
        priority: 100,
    });

    lemmas
}

/// Build `@List.reverse.{u_simp} ?α (@List.reverse.{u_simp} ?α ?xs)` for
/// `List.reverse_reverse`.
///
/// `?α` = BVar(1) (shared by both `List.reverse` type args), `?xs` = BVar(0).
/// The `u_simp` level param is solved by the unifier and re-applied to the
/// reconstructed proof (same as `List.append_nil`).
fn make_list_reverse_reverse_pattern() -> Expr {
    let u_simp = Level::param(Name::from_string("u_simp"));
    let alpha = Expr::bvar(1);
    let xs = Expr::bvar(0);
    let rev_of = |l: Expr| {
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("List.reverse"), vec![u_simp.clone()]),
                alpha.clone(),
            ),
            l,
        )
    };
    rev_of(rev_of(xs))
}

/// Build `@List.map.{v,w} ?β ?γ ?g (@List.map.{u,v} ?α ?β ?f ?xs)` for
/// `List.map_map`.
///
/// `?α`=BVar(5), `?β`=BVar(4), `?γ`=BVar(3), `?g`=BVar(2), `?f`=BVar(1),
/// `?xs`=BVar(0). Levels spell the declaration's own params (`u`,`v`,`w`) —
/// see the registration comment.
fn make_list_map_map_pattern() -> Expr {
    let u = Level::param(Name::from_string("u"));
    let v = Level::param(Name::from_string("v"));
    let w = Level::param(Name::from_string("w"));
    let inner = Expr::apps(
        Expr::const_(Name::from_string("List.map"), vec![u, v.clone()]),
        [Expr::bvar(5), Expr::bvar(4), Expr::bvar(1), Expr::bvar(0)],
    );
    Expr::apps(
        Expr::const_(Name::from_string("List.map"), vec![v, w]),
        [Expr::bvar(4), Expr::bvar(3), Expr::bvar(2), inner],
    )
}

/// Build `@List.map.{u,w} ?α ?γ (fun (x : ?α) => ?g (?f x)) ?xs` — the RHS of
/// `List.map_map`.
///
/// Inside the lambda body the pattern indices shift by one for the lambda's
/// own binder (`substitute_bvars_with_metas` is depth-aware): `?g` = BVar(3),
/// `?f` = BVar(2), the bound `x` = BVar(0). The lambda's domain (outside the
/// binder) is `?α` = BVar(5).
fn make_list_map_map_rhs() -> Expr {
    let u = Level::param(Name::from_string("u"));
    let w = Level::param(Name::from_string("w"));
    let comp_lam = Expr::lam(
        BinderInfo::Default,
        Expr::bvar(5),
        Expr::app(Expr::bvar(3), Expr::app(Expr::bvar(2), Expr::bvar(0))),
    );
    Expr::apps(
        Expr::const_(Name::from_string("List.map"), vec![u, w]),
        [Expr::bvar(5), Expr::bvar(3), comp_lam, Expr::bvar(0)],
    )
}

/// Build `@List.length.{u_simp} α l` for the given `α` / `l` sub-patterns.
fn make_list_length_app(alpha: Expr, l: Expr) -> Expr {
    let u_simp = Level::param(Name::from_string("u_simp"));
    let list_length = Expr::const_(Name::from_string("List.length"), vec![u_simp]);
    Expr::app(Expr::app(list_length, alpha), l)
}

/// Build `@List.length.{u_simp} ?α (@List.nil.{u_simp} ?α)` (`?α` = BVar(0)).
fn make_list_length_nil_pattern() -> Expr {
    let u_simp = Level::param(Name::from_string("u_simp"));
    let alpha = Expr::bvar(0);
    let list_nil = Expr::const_(Name::from_string("List.nil"), vec![u_simp]);
    let nil = Expr::app(list_nil, alpha.clone());
    make_list_length_app(alpha, nil)
}

/// Build `@List.length.{u_simp} ?α (@List.cons.{u_simp} ?α ?x ?xs)`.
///
/// `?α` = BVar(2), `?x` = BVar(1), `?xs` = BVar(0).
fn make_list_length_cons_pattern() -> Expr {
    let u_simp = Level::param(Name::from_string("u_simp"));
    let alpha = Expr::bvar(2);
    let x = Expr::bvar(1);
    let xs = Expr::bvar(0);
    let list_cons = Expr::const_(Name::from_string("List.cons"), vec![u_simp]);
    let cons = Expr::app(Expr::app(Expr::app(list_cons, alpha.clone()), x), xs);
    make_list_length_app(alpha, cons)
}

/// Build `@List.length.{u_simp} ?α (@List.append.{u_simp} ?α ?xs ?ys)`.
///
/// `?α` = BVar(2), `?xs` = BVar(1), `?ys` = BVar(0).
fn make_list_length_append_pattern() -> Expr {
    let u_simp = Level::param(Name::from_string("u_simp"));
    let alpha = Expr::bvar(2);
    let xs = Expr::bvar(1);
    let ys = Expr::bvar(0);
    let list_append = Expr::const_(Name::from_string("List.append"), vec![u_simp]);
    let append = Expr::app(Expr::app(Expr::app(list_append, alpha.clone()), xs), ys);
    make_list_length_app(alpha, append)
}

/// Build the bare-op pattern `@List.append.{u_simp} ?α ?xs (@List.nil.{u_simp}
/// ?α)` for `List.append_nil`.
///
/// `?α` is `BVar(1)` (shared between the `List.append` type arg and the
/// `List.nil` type arg), `?xs` is `BVar(0)`. The consts carry a `u_simp` level
/// param so the unifier solves the universe and the proof-reconstruction path
/// re-applies it (same as `Eq.{u_simp}`/`ite.{u_simp}`).
fn make_list_append_nil_pattern() -> Expr {
    let u_simp = Level::param(Name::from_string("u_simp"));
    let alpha = Expr::bvar(1);
    let xs = Expr::bvar(0);
    let list_append = Expr::const_(Name::from_string("List.append"), vec![u_simp.clone()]);
    let list_nil = Expr::const_(Name::from_string("List.nil"), vec![u_simp]);
    // @List.nil.{u_simp} ?α
    let nil = Expr::app(list_nil, alpha.clone());
    // @List.append.{u_simp} ?α ?xs (@List.nil ?α)
    Expr::app(Expr::app(Expr::app(list_append, alpha), xs), nil)
}
