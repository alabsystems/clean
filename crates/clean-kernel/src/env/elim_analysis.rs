// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Elimination analysis for inductive types.
//!
//! Determines whether a Prop-valued inductive type can only eliminate into Prop
//! (small elimination) or into any universe (large elimination).
//!
//! Mirrors Lean 4 kernel `elim_only_at_universe_zero()` from `inductive.cpp:479`.
//! Uses TypeChecker for accurate field sort inference (matching Lean 4's
//! `tc().ensure_type(binding_domain(type))`), fixing incorrect `None` returns
//! for App expressions that caused Acc.rec to get wrong universe level count.

use crate::expr::{Expr, ExprKind};
use crate::inductive::{get_return_type, Constructor};
use crate::level::Level;
use crate::tc::TypeChecker;
use crate::Environment;

/// Check if recursor can only eliminate into Prop (Sort 0).
///
/// Mirrors Lean 4 kernel `elim_only_at_universe_zero()` from `inductive.cpp:479`.
/// When true, the recursor does NOT get an extra motive universe parameter;
/// the motive sort is fixed at `Sort 0` (Prop).
///
/// Rules (for a Prop-valued inductive):
/// - Mutual inductive predicates (num_types > 1) → always Prop-only (#3238)
///   Lean 4 `inductive.cpp:486-489`: `if (m_ind_types.size() > 1) return true;`
/// - Multiple constructors → Prop-only elimination (e.g., `Or`)
/// - Zero constructors → large elimination allowed (e.g., `False`)
/// - One constructor → check each non-param field:
///   (1) field's type is in Prop (Sort 0), OR
///   (2) field appears in the return type's index arguments.
///   If any field fails both, → Prop-only elimination (e.g., `Nonempty`).
///
/// Uses TypeChecker for field sort inference (matching Lean 4's approach).
/// Requires the inductive type and its constructors to be registered in `env`.
pub(crate) fn elim_only_at_universe_zero(
    env: &Environment,
    ind_type_expr: &Expr,
    constructors: &[Constructor],
    num_params: u32,
    num_types: usize,
) -> bool {
    // Lean gates the restriction on `is_not_zero` (inductive.cpp:246-248,
    // :481-484): large elimination is unconditional ONLY when the result
    // level is PROVABLY nonzero. A possibly-zero level (`Sort 0`, `Sort u`,
    // `Sort (imax 1 u)`, …) must run the restriction analysis — the previous
    // syntactic `is_zero` gate let `Sort u`-valued single-ctor types
    // large-eliminate, a proof-irrelevance violation at `u := 0`
    // (design 2026-07-02-parameterized-nested-inductives.md [R1]).
    // Clean's `Level::is_nonzero` implements Lean's `is_not_zero` semantics.
    let result_sort = get_return_type(ind_type_expr);
    let ExprKind::Sort(result_level) = &result_sort.kind else {
        return false; // not a sort head — malformed; rejected elsewhere
    };
    if result_level.is_nonzero() {
        return false; // provably ≥ 1 → large elimination allowed
    }

    // Lean 4 `inductive.cpp:486-489`: mutual inductive predicates (Prop-valued,
    // num_types > 1) can only eliminate into Prop. This prevents extracting
    // computational content from mutual proofs, preserving proof irrelevance.
    if num_types > 1 {
        return true; // Mutual Prop predicates → Prop-only (#3238)
    }

    if constructors.len() > 1 {
        return true; // Multiple constructors → Prop-only
    }
    if constructors.is_empty() {
        return false; // Empty type (e.g., False) → large elimination
    }

    // Exactly one constructor. Check non-param fields using TypeChecker.
    // Lean 4 uses tc().ensure_type(binding_domain(type)) for each non-param field,
    // checking if the sort-level is zero (field type lives in Prop).
    // TypeChecker.ctor_field_sort_levels does exactly this: walks Pi binders,
    // pushes local declarations, and calls infer_sort on each field's domain.
    let mut tc = TypeChecker::new(env);
    // Coq lane: field-sort inference must run under the SAME subtyping rule
    // the environment declares for declaration checking (`Prop ≤ Set ≤ Type`
    // when `Environment::set_cumulative(true)`, the Coq re-verification lane).
    // Without this, a Prop record whose fields apply a collapsed-universe
    // constant at a Prop argument (the Berardi `retract` class) fails
    // inference here and falls into the conservative Prop-only arm — while
    // the very same environment ACCEPTS the constructor in
    // `do_inductive_type_check`, and the importer's elim-shape mirror
    // (correctly, per the And-shaped subsingleton rule) predicts large
    // elimination. The result was a recursor with 0 level params against
    // references carrying 1 (`Level count mismatch retract.0.rec`).
    // No-op on the Lean/olean lane (`is_cumulative() == false`).
    tc.set_cumulative(env.is_cumulative());
    let ctor = &constructors[0];
    let field_sorts = match tc.ctor_field_sort_levels(&ctor.type_, num_params) {
        Ok(sorts) => sorts,
        Err(_) => {
            // Type checking failed — conservatively restrict to Prop elimination.
            // Sound: at worst too-restrictive (can't eliminate Eq into Type),
            // never too-liberal (would break proof irrelevance for Nonempty-like types).
            // In Lean 4, this error would abort the entire inductive declaration.
            return true;
        }
    };

    // ── Coq-lane PARAMETRIC SINGLETON ELIMINATION ──────────────────────────
    // (Coq's `Type`-valued single-constructor "singleton" rule, parametric
    // form; gated to the cumulative Coq re-verification lane.)
    //
    // For a SINGLE-constructor inductive whose result level `R` is NOT provably
    // nonzero (so the unconditional large-elim gate at :57 declined and the
    // subsingleton analysis is running), grant LARGE elimination when EVERY
    // constructor field's sort level is `≤ R` as a LEVEL EXPRESSION
    // (`Level::is_geq(R, field)` — e.g. `u ≤ max(u,v)` and `v ≤ max(u,v)` for
    // template-polymorphic `prod.{u,v} : Sort u → Sort v → Sort (max u v)`).
    //
    // SOUNDNESS (pointwise at every level instantiation `σ`):
    //   * If `σ(R) ≥ 1` — the inductive is a genuine `Type` at `σ`, so large
    //     elimination is unconditionally sound (it carries computational content
    //     by construction; there is no proof-irrelevance to protect).
    //   * If `σ(R) = 0` — then every field level `ℓ` with `is_geq(R, ℓ)` also
    //     satisfies `σ(ℓ) = 0`: `is_geq` returns true only when `R ≥ ℓ` holds
    //     SEMANTICALLY for all instantiations (it is a conservative
    //     approximation — see `Level::is_geq`), so `σ(R) ≥ σ(ℓ)`, and `σ(R)=0`
    //     forces `σ(ℓ)=0`. Hence the constructor's every field is a `Prop`, and
    //     a single-constructor all-`Prop`-field record is a SUBSINGLETON — Coq's
    //     singleton-elimination class, identical to `And`/`conj`. Any two
    //     inhabitants are componentwise proof-irrelevant, so eliminating into an
    //     arbitrary universe cannot leak a choice: the eliminator is
    //     proof-irrelevance-compatible.
    // Either way large elimination is sound at `σ`; because this holds for EVERY
    // `σ`, it is sound for the polymorphic declaration. This is exactly Coq's
    // rule for template-polymorphic `prod`/`sum`/`sigT`, pointwise-sound at every
    // instance.
    //
    // Coq-lane gated (`is_cumulative()`): a no-op on the Lean/olean lane, where
    // flipping a universe-polymorphic inductive's generated recursor level count
    // would diverge from `.olean` recursor expectations (the same gating pattern
    // as the elim-mirror cumulativity companion at :93). The [R1]
    // proof-irrelevance guard below is PRESERVED unchanged for every shape this
    // rule does not accept — multiple constructors (already returned above), a
    // field whose level is not `≤ R`, and indexed non-`Prop` fields — so
    // `Nonempty`/witness-extraction singletons keep eliminating only into `Prop`.
    if env.is_cumulative()
        && field_sorts
            .iter()
            .all(|field_level| Level::is_geq(result_level, field_level))
    {
        return false; // parametric singleton → large elimination
    }

    // Find non-Prop field positions (0-indexed from first non-param field)
    let non_prop_fields: Vec<u32> = field_sorts
        .iter()
        .enumerate()
        .filter(|(_, level)| !level.is_zero())
        .map(|(i, _)| i as u32)
        .collect();

    if non_prop_fields.is_empty() {
        return false; // All non-param fields in Prop → large elimination allowed
    }

    // Check condition 2: non-Prop fields must appear in return type indices.
    // Navigate past all Pi binders to the return type.
    let mut cur = &ctor.type_;
    while let ExprKind::Pi(_, _, body) = &cur.kind {
        cur = body;
    }

    // Collect return type arguments
    let mut return_args = Vec::new();
    let mut ret = cur;
    while let ExprKind::App(func, arg) = &ret.kind {
        return_args.push(arg.as_ref());
        ret = func;
    }
    return_args.reverse();
    let index_args: Vec<&Expr> = return_args.into_iter().skip(num_params as usize).collect();

    let total_fields = field_sorts.len() as u32;
    for field_pos in &non_prop_fields {
        let bvar_idx = total_fields - 1 - field_pos;
        // Lean 4 parity (inductive.cpp `elim_only_at_universe_zero`, the
        // `std::find(result_args, arg_to_check)` membership test): the
        // non-Prop field must appear as a result-type argument DIRECTLY (a
        // bare variable), not merely occur somewhere inside one. Example:
        // `Int.NonNeg.mk : (n : Nat) → Int.NonNeg (Int.ofNat n)` — `n`
        // occurs only under `Int.ofNat`, so Lean restricts `Int.NonNeg.rec`
        // to Prop elimination (level params `[]`); the previous
        // `has_loose_bvar` occurrence test wrongly granted large elimination
        // (kernel-parity sweep 2026-06-12, `Int.NonNeg` family cross-check).
        let found = index_args
            .iter()
            .any(|arg| matches!(&arg.kind, ExprKind::BVar(idx) if *idx == bvar_idx));
        if !found {
            return true; // Field is not a direct index arg → Prop-only elimination
        }
    }

    false // All non-Prop fields appear directly in indices → large elimination allowed
}

#[cfg(test)]
mod tests {
    use crate::env::Environment;
    use crate::expr::{BinderInfo, Expr};
    use crate::inductive::{Constructor, InductiveDecl, InductiveType};
    use crate::level::Level;
    use crate::tc::TypeChecker;
    use crate::Name;

    fn n(s: &str) -> Name {
        Name::from_string(s)
    }

    /// Coq-lane mirror of `Coq.Init.Logic.eq` at COLLAPSED universes: the
    /// importer renders Coq's floating `Type@{u}` parameter as a concrete
    /// `Sort 2`, so applying `eqc` at a `Prop`-sorted argument requires
    /// cumulative subtyping (`Prop ≤ Type`) — exactly the shape the real
    /// imported stdlib `eq` has inside `Coq.Logic.Berardi.retract`.
    ///
    ///   eqc : Π (A : Sort 2) (x : A) (y : A), Prop      (num_params = 2)
    ///   eqc.refl : Π (A : Sort 2) (x : A), eqc A x x
    fn coq_lane_eqc_decl() -> InductiveDecl {
        let sort2 = Expr::sort(Level::succ(Level::succ(Level::zero())));
        let eqc_ty = Expr::pi(
            BinderInfo::Default,
            sort2.clone(),
            Expr::pi(
                BinderInfo::Default,
                Expr::bvar(0),
                Expr::pi(BinderInfo::Default, Expr::bvar(1), Expr::prop()),
            ),
        );
        let refl_ty = Expr::pi(
            BinderInfo::Default,
            sort2,
            Expr::pi(
                BinderInfo::Default,
                Expr::bvar(0),
                Expr::apps(
                    Expr::const_(n("CoqLaneEqc"), vec![]),
                    [Expr::bvar(1), Expr::bvar(0), Expr::bvar(0)],
                ),
            ),
        );
        InductiveDecl {
            level_params: vec![],
            num_params: 2,
            types: vec![InductiveType {
                name: n("CoqLaneEqc"),
                type_: eqc_ty,
                constructors: vec![Constructor {
                    name: n("CoqLaneEqc.refl"),
                    type_: refl_ty,
                }],
            }],
        }
    }

    /// Faithful shape of `Coq.Logic.Berardi.retract` (stdlib dump,
    /// `Record retract (A B : Prop) : Prop := { i : A→B; j : B→A;
    /// inv : ∀ a, j (i a) = a }`) over the collapsed-universe `eqc` above:
    /// a SINGLE-constructor Prop record whose three fields are all
    /// Prop-sorted — the And-shaped subsingleton class Lean 4 grants LARGE
    /// elimination (a motive universe parameter on `.rec`).
    fn coq_lane_retract_decl() -> InductiveDecl {
        let retract = n("CoqLaneRetract");
        // retract : Π (A : Prop) (B : Prop), Prop
        let retract_ty = Expr::pi(
            BinderInfo::Default,
            Expr::prop(),
            Expr::pi(BinderInfo::Default, Expr::prop(), Expr::prop()),
        );
        // Build_retract : Π (A B : Prop) (i : A→B) (j : B→A)
        //                   (inv : Π (a : A), eqc A (j (i a)) a), retract A B
        let i_ty = Expr::pi(BinderInfo::Default, Expr::bvar(1), Expr::bvar(1));
        let j_ty = Expr::pi(BinderInfo::Default, Expr::bvar(1), Expr::bvar(3));
        let inv_body = Expr::apps(
            Expr::const_(n("CoqLaneEqc"), vec![]),
            [
                Expr::bvar(4),
                Expr::apps(Expr::bvar(1), [Expr::apps(Expr::bvar(2), [Expr::bvar(0)])]),
                Expr::bvar(0),
            ],
        );
        let inv_ty = Expr::pi(BinderInfo::Default, Expr::bvar(3), inv_body);
        let result = Expr::apps(
            Expr::const_(retract.clone(), vec![]),
            [Expr::bvar(4), Expr::bvar(3)],
        );
        let ctor_ty = Expr::pi(
            BinderInfo::Default,
            Expr::prop(),
            Expr::pi(
                BinderInfo::Default,
                Expr::prop(),
                Expr::pi(
                    BinderInfo::Default,
                    i_ty,
                    Expr::pi(
                        BinderInfo::Default,
                        j_ty,
                        Expr::pi(BinderInfo::Default, inv_ty, result),
                    ),
                ),
            ),
        );
        InductiveDecl {
            level_params: vec![],
            num_params: 2,
            types: vec![InductiveType {
                name: retract,
                type_: retract_ty,
                constructors: vec![Constructor {
                    name: n("CoqLaneRetract.mk"),
                    type_: ctor_ty,
                }],
            }],
        }
    }

    /// ELIM-SHAPE MIRROR parity (Coq lane): on a cumulative environment the
    /// Berardi `retract` Prop-record class must (a) replay through checked
    /// `add_inductive` — `do_inductive_type_check` runs under the env's
    /// declared subtyping mode — and (b) get a LARGE-eliminating recursor
    /// (exactly one motive level param), because its single constructor's
    /// fields are all Prop-sorted (Lean 4 subsingleton elimination, the same
    /// verdict `elim_only_at_universe_zero` reaches for `And`). Before the
    /// fix, (a) failed without the builder cumulativity companion, and with
    /// the companion alone (b) produced a 0-level-param recursor — the
    /// analysis TypeChecker erred on the cumulative `eqc A …` field and fell
    /// into the conservative Prop-only arm, diverging from the importer's
    /// elim-shape mirror (corpus symptom: `Level count mismatch
    /// retract.0.rec: declared 0 level params, got 1` on 14 baseline-KV
    /// stdlib decls).
    #[test]
    fn test_cumulative_prop_record_recursor_large_eliminates() {
        let mut env = Environment::try_with_prelude().expect("prelude environment");
        env.set_cumulative(true);
        env.add_inductive(coq_lane_eqc_decl())
            .expect("collapsed-universe eqc family must replay");
        env.add_inductive(coq_lane_retract_decl())
            .expect("retract Prop record must replay on the cumulative lane");
        let rec = env
            .get_recursor(&n("CoqLaneRetract.rec"))
            .expect("recursor generated");
        assert_eq!(
            rec.level_params.len(),
            1,
            "single-ctor all-Prop-field record large-eliminates (motive \
             universe param), matching the importer's elim-shape mirror; got \
             level_params = {:?}",
            rec.level_params
        );
    }

    /// Semantic pin: the large-eliminating recursor COMPUTES. Eliminate a
    /// concrete `retract True True` witness into `Nat` (motive at Sort 1 —
    /// only sound because the record is a subsingleton) and check iota
    /// reduction produces the minor premise's value.
    #[test]
    fn test_cumulative_prop_record_large_elim_computes() {
        let mut env = Environment::try_with_prelude().expect("prelude environment");
        env.set_cumulative(true);
        env.add_inductive(coq_lane_eqc_decl())
            .expect("eqc family must replay");
        env.add_inductive(coq_lane_retract_decl())
            .expect("retract family must replay");

        let tru = || Expr::const_(n("True"), vec![]);
        let nat = || Expr::const_(n("Nat"), vec![]);
        let id_true = || Expr::lam(BinderInfo::Default, tru(), Expr::bvar(0));
        // inv := λ (a : True). eqc.refl True a  (checks against
        // `eqc True (id (id a)) a` up to beta)
        let inv_val = Expr::lam(
            BinderInfo::Default,
            tru(),
            Expr::apps(
                Expr::const_(n("CoqLaneEqc.refl"), vec![]),
                [tru(), Expr::bvar(0)],
            ),
        );
        let witness = Expr::apps(
            Expr::const_(n("CoqLaneRetract.mk"), vec![]),
            [tru(), tru(), id_true(), id_true(), inv_val],
        );
        // motive := λ (_ : retract True True). Nat
        let motive = Expr::lam(
            BinderInfo::Default,
            Expr::apps(Expr::const_(n("CoqLaneRetract"), vec![]), [tru(), tru()]),
            nat(),
        );
        // minor := λ (i : True→True) (j : True→True)
        //            (inv : Π (a : True), eqc True (j (i a)) a). Nat.zero
        let arrow_true = || Expr::pi(BinderInfo::Default, tru(), tru());
        let minor_inv_ty = Expr::pi(
            BinderInfo::Default,
            tru(),
            Expr::apps(
                Expr::const_(n("CoqLaneEqc"), vec![]),
                [
                    tru(),
                    Expr::apps(Expr::bvar(1), [Expr::apps(Expr::bvar(2), [Expr::bvar(0)])]),
                    Expr::bvar(0),
                ],
            ),
        );
        let minor = Expr::lam(
            BinderInfo::Default,
            arrow_true(),
            Expr::lam(
                BinderInfo::Default,
                arrow_true(),
                Expr::lam(
                    BinderInfo::Default,
                    minor_inv_ty,
                    Expr::const_(n("Nat.zero"), vec![]),
                ),
            ),
        );
        // @CoqLaneRetract.rec.{1} True True motive minor witness : Nat
        let elim = Expr::apps(
            Expr::const_(n("CoqLaneRetract.rec"), vec![Level::succ(Level::zero())]),
            [tru(), tru(), motive, minor, witness],
        );

        let mut tc = TypeChecker::new(&env);
        tc.set_cumulative(true);
        tc.check_type(&elim, &nat())
            .expect("large elimination of the Prop record into Nat must typecheck");
        assert_eq!(
            tc.whnf(&elim),
            Expr::const_(n("Nat.zero"), vec![]),
            "iota reduction through the generated recursor must fire"
        );

        // NEGATIVE control (reference shape): the recursor declares exactly
        // ONE level param — a 0-level reference must be REJECTED, pinning
        // the level-arity contract the importer's Case lowering relies on.
        let elim_no_levels = Expr::apps(
            Expr::const_(n("CoqLaneRetract.rec"), vec![]),
            [
                tru(),
                tru(),
                Expr::lam(
                    BinderInfo::Default,
                    Expr::apps(Expr::const_(n("CoqLaneRetract"), vec![]), [tru(), tru()]),
                    nat(),
                ),
            ],
        );
        assert!(
            tc.infer_type(&elim_no_levels).is_err(),
            "a 0-level reference to the 1-level recursor must be rejected"
        );
    }

    /// NEGATIVE control (no witness extraction): a Prop singleton with a
    /// non-Prop field that is NOT a result index (`exn.mk : Π (w : Nat),
    /// exn`) must stay Prop-only-eliminating even on the cumulative lane —
    /// cumulativity changes which field-sort INFERENCES succeed, never the
    /// inferred levels the restriction tests.
    #[test]
    fn test_cumulative_witness_singleton_stays_prop_only() {
        let mut env = Environment::try_with_prelude().expect("prelude environment");
        env.set_cumulative(true);
        let exn = n("CoqLaneExn");
        let ctor_ty = Expr::pi(
            BinderInfo::Default,
            Expr::const_(n("Nat"), vec![]),
            Expr::const_(exn.clone(), vec![]),
        );
        env.add_inductive(InductiveDecl {
            level_params: vec![],
            num_params: 0,
            types: vec![InductiveType {
                name: exn.clone(),
                type_: Expr::prop(),
                constructors: vec![Constructor {
                    name: n("CoqLaneExn.mk"),
                    type_: ctor_ty,
                }],
            }],
        })
        .expect("witness singleton must replay");
        let rec = env
            .get_recursor(&n("CoqLaneExn.rec"))
            .expect("recursor generated");
        assert_eq!(
            rec.level_params.len(),
            0,
            "a non-Prop non-index field keeps the singleton Prop-only \
             (witness extraction must NOT be enabled by cumulativity)"
        );
    }

    /// NEGATIVE control (Lean lane byte-identical): WITHOUT the env
    /// cumulativity flag the collapsed-universe record cannot even be
    /// declared — `eqc` applied at a `Prop` argument fails the Lean-faithful
    /// non-cumulative check, exactly as before this change.
    #[test]
    fn test_non_cumulative_lane_still_rejects_collapsed_universe_record() {
        let mut env = Environment::try_with_prelude().expect("prelude environment");
        env.add_inductive(coq_lane_eqc_decl())
            .expect("eqc itself is universe-monomorphic and replays anywhere");
        assert!(
            env.add_inductive(coq_lane_retract_decl()).is_err(),
            "the Lean-faithful lane must keep rejecting Prop-at-Type \
             applications without cumulativity"
        );
    }
}
