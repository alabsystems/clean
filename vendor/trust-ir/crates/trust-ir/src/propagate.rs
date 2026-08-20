// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! **Forward propagation over the predicate lattice** — the inference half of
//! the typed value model.
//!
//! # The gap this closes
//!
//! [`crate::pred`] gives the model a way to STATE a fact and a decidable way to
//! CONSUME one. What it did not give was a way to *derive* one: every fact died
//! at the instruction that produced it, because a result's type is whatever the
//! producer declared and a producer that declares nothing declares
//! [`Pred::Top`]. A value computed from two refined operands therefore arrived
//! at its consumption site carrying no information at all — the exact shape the
//! model exists to make loud, manufactured by the model's own blind spot.
//!
//! # The soundness bar: NEVER MANUFACTURE A FACT
//!
//! Every rule here answers one question: *what is the strongest predicate this
//! result is GUARANTEED to satisfy whenever its operands satisfy theirs?* When
//! the answer is not decidable in microseconds, or the justification has a
//! hole — an overflow, a width change that could wrap, an operand whose fact is
//! unknown — the answer is [`Pred::Top`]. `Top` is not a failure mode here; it
//! is the correct answer to "I cannot justify better", and it costs a loud
//! error at the consumption site rather than a silent reinterpretation.
//!
//! Concretely, that means the rules below are deliberately *few*. A rule earns
//! its place only if its soundness argument fits in a sentence:
//!
//! | instruction | derived fact | why it is sound |
//! |---|---|---|
//! | [`Inst::Copy`] | the operand's fact | the result IS the operand |
//! | [`Inst::Select`] | join of the two arms | the result is one of them; a join is an upper bound of both |
//! | [`Inst::Const`] (integer/bool) | `Interval{v, v}` | the value is literally `v` |
//! | [`Inst::ICmp`]/[`Inst::FCmp`] (scalar) | `Interval{0, 1}` | a boolean carrier is 0 or 1 |
//! | [`Inst::BinOp`] `Add`/`Sub` | interval arithmetic | exact on ℤ, and **only** kept when the result provably cannot leave the result type's range |
//! | [`Inst::Cast`] `ZExt`/`SExt`/`Trunc` | the operand's interval | kept **only** when the cast provably preserves the mathematical value |
//!
//! Everything else is `Top`. There is no fixpoint, no widening and no
//! transitive closure over loops: the driver walks a function once in
//! reverse-postorder and a back edge contributes `Top`, so termination is not
//! an argument, it is a single pass.
//!
//! # Declared vs derived: INTERSECT, and a contradiction is a bug
//!
//! A producer's declared refinement and a derived fact are two claims about the
//! same value, so the value satisfies **both**: they INTERSECT. Propagation
//! therefore never overrides a declaration and never silently replaces it — a
//! consumption site is satisfied when *either* claim entails the requirement,
//! which is a sound reading of the conjunction.
//!
//! When the two are decidably DISJOINT, that is not a precision question: the
//! producer declared something the program cannot produce, which is a frontend
//! bug of exactly the class this model exists to catch. [`PredTable::contradicts`]
//! decides that case, and the validator raises a hard error on it.

use crate::inst::{BinOp, CastOp, Inst};
use crate::pred::{Pred, PredTable};
use crate::ty::Ty;
use crate::value::ValueId;

/// The inclusive range of mathematical integers a scalar carrier can hold.
///
/// `None` for every type whose range is not known context-free: pointer-width
/// integers (target-dependent) and `u128` (whose maximum does not fit `i128`).
/// A `None` here propagates to [`Pred::Top`] — the lattice never guesses a
/// width.
pub fn integer_value_range(ty: &Ty) -> Option<(i128, i128)> {
    match ty {
        Ty::Bool => Some((0, 1)),
        Ty::I8 => Some((i8::MIN as i128, i8::MAX as i128)),
        Ty::I16 => Some((i16::MIN as i128, i16::MAX as i128)),
        Ty::I32 => Some((i32::MIN as i128, i32::MAX as i128)),
        Ty::I64 => Some((i64::MIN as i128, i64::MAX as i128)),
        Ty::I128 => Some((i128::MIN, i128::MAX)),
        Ty::U8 => Some((0, u8::MAX as i128)),
        Ty::U16 => Some((0, u16::MAX as i128)),
        Ty::U32 => Some((0, u32::MAX as i128)),
        Ty::U64 => Some((0, u64::MAX as i128)),
        Ty::Char => Some((0, 0x10_FFFF)),
        // `usize`/`isize` are target-dependent and `u128`'s maximum does not
        // fit the lattice's `i128` arithmetic. Answer "unknown", never a guess.
        Ty::Usize | Ty::Isize | Ty::U128 => None,
        _ => None,
    }
}

/// Is `p` the "no information" element, in the only sense that matters here?
fn is_top(p: &Pred) -> bool {
    matches!(p, Pred::Top)
}

/// Clamp a derived interval into a canonical [`Pred`], or [`Pred::Top`].
fn interval_or_top(lo: i128, hi: i128) -> Pred {
    match Pred::interval(lo, hi) {
        Some(p) => p,
        None => Pred::Top,
    }
}

/// **The propagation rule set.**
///
/// Returns the strongest predicate `inst`'s SINGLE result is guaranteed to
/// satisfy, given that every operand satisfies the fact `operand_fact` reports
/// for it. Returns [`Pred::Top`] whenever nothing better is justified.
///
/// `operand_fact` must itself be sound — it reports what the caller is
/// entitled to ASSUME about a value (a declared refinement, or a previously
/// derived fact), and [`Pred::Top`] for anything unknown. A caller that has
/// not yet computed a value's fact (a back edge, an unvisited block) must
/// answer `Top`; answering anything else would break the guarantee.
///
/// Multi-result instructions (`Overflow`, `CmpXchg`, calls, dialect ops) are
/// deliberately not covered: a rule per extra result would have to reason
/// about which result is which, and none of them has a one-sentence soundness
/// argument. They are `Top`.
pub fn derive_result_fact(
    table: &PredTable<'_>,
    inst: &Inst,
    operand_fact: &dyn Fn(ValueId) -> Pred,
) -> Pred {
    derive_result_fact_with_representation(table, inst, None, operand_fact)
}

/// [`derive_result_fact`] with the instruction result's exact representation
/// type supplied by a module-aware caller.
///
/// `Ty::Refine` stores its base behind a `TyId`, so this crate-level rule file
/// cannot resolve the carrier from the wrapper alone. The validator passes
/// [`crate::Module::representation_ty`] here. Only representation questions
/// use this value; the caller retains the refined type and predicate as the
/// independently checked declared fact.
pub fn derive_result_fact_with_representation(
    table: &PredTable<'_>,
    inst: &Inst,
    result_representation: Option<&Ty>,
    operand_fact: &dyn Fn(ValueId) -> Pred,
) -> Pred {
    match inst {
        // The result IS the operand. Nothing to justify.
        Inst::Copy { operand, .. } => operand_fact(*operand),

        // The result is one of the two arms, and a join is an upper bound of
        // both — so it holds whichever arm was taken. This is the same
        // operation WP-1 already performs at control-flow edges; `Select` is
        // just the branchless spelling of that merge.
        Inst::Select {
            then_val, else_val, ..
        } => table.join_pred_nodes(&operand_fact(*then_val), &operand_fact(*else_val)),

        // A constant's value is literally the constant. Only integer/bool
        // scalars: those are the carriers the lattice can state a fact about,
        // and `Interval` is a claim about the mathematical value, so the
        // constant must actually fit the declared carrier.
        Inst::Const { ty, value } => match (
            integer_value_range(result_representation.unwrap_or(ty)),
            value,
        ) {
            (Some((tlo, thi)), crate::constant::Constant::Int(v)) if tlo <= *v && *v <= thi => {
                interval_or_top(*v, *v)
            }
            (Some(_), crate::constant::Constant::Bool(b)) => {
                let v = i128::from(*b);
                interval_or_top(v, v)
            }
            _ => Pred::Top,
        },

        // A comparison yields a boolean carrier, which is 0 or 1. This is
        // justified by the RESULT TYPE alone, so it needs no operand fact —
        // but it is only stated for the SCALAR result: a vector compare yields
        // a lane mask, and `Interval` is not a per-lane claim.
        Inst::ICmp { ty, .. } | Inst::FCmp { ty, .. } => {
            if ty.comparison_result_ty() == Ty::Bool {
                interval_or_top(0, 1)
            } else {
                Pred::Top
            }
        }

        // Interval arithmetic, kept ONLY when it provably cannot wrap.
        Inst::BinOp {
            op: op @ (BinOp::Add | BinOp::Sub),
            ty,
            lhs,
            rhs,
        } => derive_add_sub(
            table,
            *op,
            result_representation.unwrap_or(ty),
            &operand_fact(*lhs),
            &operand_fact(*rhs),
        ),

        // Width changes that provably preserve the mathematical value.
        Inst::Cast {
            op,
            src_ty,
            dst_ty,
            operand,
        } => derive_cast(table, *op, src_ty, dst_ty, &operand_fact(*operand)),

        _ => Pred::Top,
    }
}

/// `Add`/`Sub` over the operands' interval bounds.
///
/// Exact on the integers: `[a, b] + [c, d] = [a+c, b+d]` and
/// `[a, b] - [c, d] = [a-d, b-c]`. The machine, however, computes modulo the
/// result type's width — so the derived interval is kept ONLY when it is
/// entirely inside that type's range, where the modular result and the
/// mathematical one coincide. **Any possibility of overflow yields `Top`**,
/// including the case where the `i128` arithmetic used to check it would
/// itself overflow.
fn derive_add_sub(table: &PredTable<'_>, op: BinOp, ty: &Ty, lhs: &Pred, rhs: &Pred) -> Pred {
    let Some((tlo, thi)) = integer_value_range(ty) else {
        return Pred::Top;
    };
    let (Some((alo, ahi)), Some((blo, bhi))) =
        (table.interval_bound_of(lhs), table.interval_bound_of(rhs))
    else {
        return Pred::Top;
    };
    let (lo, hi) = match op {
        BinOp::Add => (alo.checked_add(blo), ahi.checked_add(bhi)),
        BinOp::Sub => (alo.checked_sub(bhi), ahi.checked_sub(blo)),
        _ => return Pred::Top,
    };
    let (Some(lo), Some(hi)) = (lo, hi) else {
        return Pred::Top;
    };
    // THE OVERFLOW GATE. Outside the carrier's range the machine wraps and the
    // interval is a lie, so the fact is dropped rather than narrowed.
    if lo < tlo || hi > thi {
        return Pred::Top;
    }
    interval_or_top(lo, hi)
}

/// `ZExt`/`SExt`/`Trunc` — kept only where the cast provably preserves the
/// mathematical value of the operand.
fn derive_cast(
    table: &PredTable<'_>,
    op: CastOp,
    src_ty: &Ty,
    dst_ty: &Ty,
    operand: &Pred,
) -> Pred {
    let Some((lo, hi)) = table.interval_bound_of(operand) else {
        return Pred::Top;
    };
    let Some((dlo, dhi)) = integer_value_range(dst_ty) else {
        return Pred::Top;
    };
    let survives = match op {
        // Zero-extension reads the source bit pattern as UNSIGNED. That equals
        // the mathematical value only when the value is non-negative; a
        // negative operand becomes a large positive one, so the interval does
        // not survive.
        CastOp::ZExt => lo >= 0,
        // Sign-extension preserves the signed value — but only from a SIGNED
        // carrier. Sign-extending an unsigned type reinterprets its high bit,
        // which is precisely the reinterpretation this model refuses to model
        // away.
        CastOp::SExt => src_ty.is_signed(),
        // Truncation is the identity on the value exactly when the value
        // already fits the destination; otherwise it wraps.
        CastOp::Trunc => dlo <= lo && hi <= dhi,
        // Every other cast either changes the value (float conversions),
        // reinterprets bits (`Bitcast`, `Transmute`), or crosses the
        // integer/pointer boundary where an integer fact says nothing.
        _ => false,
    };
    if !survives {
        return Pred::Top;
    }
    // Even a value-preserving cast must land inside the destination carrier;
    // if it cannot be shown to, the fact is dropped.
    if lo < dlo || hi > dhi {
        return Pred::Top;
    }
    interval_or_top(lo, hi)
}

/// The fact a caller is entitled to assume about a value that carries BOTH a
/// declared refinement and a derived one.
///
/// The two INTERSECT, but the lattice cannot spell an un-interned conjunction,
/// so this returns the stronger of the two where that is decidable and the
/// DECLARED one otherwise. Sound in both cases: each is individually a fact
/// about the value, and returning the weaker of two true facts only loses
/// precision.
///
/// Consumption checks must test BOTH claims separately rather than relying on
/// this — see `check_refinement_consumption` in `trust-ir-build`.
pub fn assumed_fact(table: &PredTable<'_>, declared: &Pred, derived: &Pred) -> Pred {
    if is_top(derived) {
        return declared.clone();
    }
    if is_top(declared) {
        return derived.clone();
    }
    if table.implies_pred(derived, declared) {
        return derived.clone();
    }
    declared.clone()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::constant::Constant;
    use crate::inst::ICmpOp;
    use crate::pred::Universe;
    use crate::value::{PredId, UnivId};

    /// A table + a fixed operand-fact map, for the rule tests below.
    struct Fixture {
        preds: Vec<Pred>,
        universes: Vec<Universe>,
        facts: Vec<Pred>,
    }

    impl Fixture {
        fn new(facts: Vec<Pred>) -> Self {
            Self {
                preds: Vec::new(),
                universes: Vec::new(),
                facts,
            }
        }
        fn with_tables(preds: Vec<Pred>, universes: Vec<Universe>, facts: Vec<Pred>) -> Self {
            Self {
                preds,
                universes,
                facts,
            }
        }
        fn table(&self) -> PredTable<'_> {
            PredTable::new(&self.preds, &self.universes)
        }
        fn derive(&self, inst: &Inst) -> Pred {
            let facts = &self.facts;
            derive_result_fact(&self.table(), inst, &|v: ValueId| {
                facts.get(v.as_usize()).cloned().unwrap_or(Pred::Top)
            })
        }
    }

    fn v(i: u32) -> ValueId {
        ValueId::new(i)
    }

    // ── Copy ────────────────────────────────────────────────────────────────

    #[test]
    fn copy_carries_the_operand_fact_and_falls_to_top_without_one() {
        let f = Fixture::new(vec![Pred::Interval { lo: 2, hi: 5 }]);
        assert_eq!(
            f.derive(&Inst::Copy {
                ty: Ty::I64,
                operand: v(0)
            }),
            Pred::Interval { lo: 2, hi: 5 },
            "(a) the fact is derived when justified"
        );
        // (b) an operand with no fact yields no fact — never an invented one.
        assert_eq!(
            f.derive(&Inst::Copy {
                ty: Ty::I64,
                operand: v(9)
            }),
            Pred::Top
        );
    }

    #[test]
    fn copy_preserves_a_convention_not_merely_a_number() {
        // The case that matters: `Copy` is how a frontend spells a rename, and
        // a rename must not lose the encoding convention.
        let f = Fixture::with_tables(
            vec![Pred::InUniverse(UnivId::new(0), crate::pred::Space::Member)],
            vec![Universe::IntRange { lo: 1, hi: 8 }],
            vec![Pred::InUniverse(UnivId::new(0), crate::pred::Space::Member)],
        );
        assert_eq!(
            f.derive(&Inst::Copy {
                ty: Ty::I64,
                operand: v(0)
            }),
            Pred::InUniverse(UnivId::new(0), crate::pred::Space::Member)
        );
    }

    // ── Select ──────────────────────────────────────────────────────────────

    #[test]
    fn select_joins_the_arms_and_a_missing_arm_fact_collapses_it() {
        let f = Fixture::new(vec![
            Pred::Interval { lo: 0, hi: 3 },
            Pred::Interval { lo: 7, hi: 9 },
        ]);
        let sel = |a, b| Inst::Select {
            ty: Ty::I64,
            cond: v(100),
            then_val: a,
            else_val: b,
        };
        // (a) justified: the hull holds whichever arm was taken.
        assert_eq!(f.derive(&sel(v(0), v(1))), Pred::Interval { lo: 0, hi: 9 });
        // (b) one arm carries nothing => the merge carries nothing. This is
        // the WP-28 mechanism, and it must decay rather than pick a side.
        assert_eq!(f.derive(&sel(v(0), v(50))), Pred::Top);
    }

    #[test]
    fn select_over_two_different_universes_decays_to_top() {
        // Two conventions with nothing in common must not merge into either.
        let univs = vec![
            Universe::IntRange { lo: 1, hi: 8 },
            Universe::IntRange { lo: 100, hi: 200 },
        ];
        let a = Pred::InUniverse(UnivId::new(0), crate::pred::Space::Member);
        let b = Pred::InUniverse(UnivId::new(1), crate::pred::Space::Member);
        let f = Fixture::with_tables(vec![a.clone(), b.clone()], univs, vec![a, b]);
        assert_eq!(
            f.derive(&Inst::Select {
                ty: Ty::I64,
                cond: v(100),
                then_val: v(0),
                else_val: v(1),
            }),
            Pred::Top
        );
    }

    // ── Const ───────────────────────────────────────────────────────────────

    #[test]
    fn an_integer_constant_pins_a_singleton_interval() {
        let f = Fixture::new(vec![]);
        assert_eq!(
            f.derive(&Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(7)
            }),
            Pred::Interval { lo: 7, hi: 7 }
        );
        // (b) a constant that does not fit its declared carrier is a producer
        // bug; derive nothing rather than a fact about a value that cannot be
        // represented.
        assert_eq!(
            f.derive(&Inst::Const {
                ty: Ty::I8,
                value: Constant::Int(300)
            }),
            Pred::Top
        );
        // (b') a non-scalar constant has no interval at all.
        assert_eq!(
            f.derive(&Inst::Const {
                ty: Ty::F64,
                value: Constant::Float(1.0)
            }),
            Pred::Top
        );
        // (b'') a target-dependent width is never guessed.
        assert_eq!(
            f.derive(&Inst::Const {
                ty: Ty::Usize,
                value: Constant::Int(7)
            }),
            Pred::Top
        );
    }

    // ── Comparisons ─────────────────────────────────────────────────────────

    #[test]
    fn a_scalar_comparison_yields_zero_or_one_and_a_vector_one_yields_top() {
        let f = Fixture::new(vec![]);
        assert_eq!(
            f.derive(&Inst::ICmp {
                op: ICmpOp::Slt,
                ty: Ty::I64,
                lhs: v(0),
                rhs: v(1)
            }),
            Pred::Interval { lo: 0, hi: 1 },
            "(a) a boolean carrier is 0 or 1, justified by the type alone"
        );
        // (b) a vector compare yields a lane MASK; `Interval` is not a
        // per-lane claim, so nothing is derived.
        assert_eq!(
            f.derive(&Inst::ICmp {
                op: ICmpOp::Slt,
                ty: Ty::Vector(Box::new(Ty::I32), 4),
                lhs: v(0),
                rhs: v(1)
            }),
            Pred::Top
        );
    }

    // ── Add / Sub ───────────────────────────────────────────────────────────

    fn add(ty: Ty, lhs: ValueId, rhs: ValueId) -> Inst {
        Inst::BinOp {
            op: BinOp::Add,
            ty,
            lhs,
            rhs,
        }
    }

    #[test]
    fn add_with_a_constant_shifts_the_interval_when_it_cannot_wrap() {
        let f = Fixture::new(vec![
            Pred::Interval { lo: 0, hi: 7 }, // v0: an index-shaped range
            Pred::Interval { lo: 1, hi: 1 }, // v1: the constant 1
        ]);
        // (a) DERIVED: the off-by-one correction that turns an index into a
        // member of `1..=8` is exactly this arithmetic.
        assert_eq!(
            f.derive(&add(Ty::I64, v(0), v(1))),
            Pred::Interval { lo: 1, hi: 8 }
        );
        // Commutative: the constant on the left works too.
        assert_eq!(
            f.derive(&add(Ty::I64, v(1), v(0))),
            Pred::Interval { lo: 1, hi: 8 }
        );
    }

    #[test]
    fn add_falls_to_top_on_overflow_and_on_an_unknown_operand() {
        // (b) OVERFLOW: `i8` tops out at 127, so `[100,127] + [1,1]` leaves the
        // carrier's range and the machine wraps. The fact must be dropped, not
        // narrowed to a wrapped interval.
        let f = Fixture::new(vec![
            Pred::Interval { lo: 100, hi: 127 },
            Pred::Interval { lo: 1, hi: 1 },
            Pred::Interval { lo: 0, hi: 7 },
        ]);
        assert_eq!(f.derive(&add(Ty::I8, v(0), v(1))), Pred::Top);
        // The same operands in a wider carrier DO derive — proving the refusal
        // above is the overflow gate and not a blanket refusal.
        assert_eq!(
            f.derive(&add(Ty::I16, v(0), v(1))),
            Pred::Interval { lo: 101, hi: 128 }
        );
        // (b') an operand with no fact yields nothing.
        assert_eq!(f.derive(&add(Ty::I64, v(2), v(77))), Pred::Top);
        // (b'') a target-dependent carrier width is never assumed.
        assert_eq!(f.derive(&add(Ty::Usize, v(2), v(1))), Pred::Top);
    }

    #[test]
    fn sub_is_exact_in_both_directions_and_gated_the_same_way() {
        let f = Fixture::new(vec![
            Pred::Interval { lo: 1, hi: 8 },
            Pred::Interval { lo: 1, hi: 1 },
            Pred::Interval { lo: -128, hi: -100 },
        ]);
        let sub = |ty, lhs, rhs| Inst::BinOp {
            op: BinOp::Sub,
            ty,
            lhs,
            rhs,
        };
        // (a) member of 1..=8 minus 1 is an ordinal in 0..=7.
        assert_eq!(
            f.derive(&sub(Ty::I64, v(0), v(1))),
            Pred::Interval { lo: 0, hi: 7 }
        );
        // Constant on the LEFT: [1,1] - [1,8] = [-7, 0].
        assert_eq!(
            f.derive(&sub(Ty::I64, v(1), v(0))),
            Pred::Interval { lo: -7, hi: 0 }
        );
        // (b) underflow at the bottom of `i8` drops the fact.
        assert_eq!(f.derive(&sub(Ty::I8, v(2), v(1))), Pred::Top);
    }

    #[test]
    fn multiplication_and_division_derive_nothing() {
        // The rule set is deliberately small: a rule earns its place only with
        // a one-sentence soundness argument. `Mul` does not have one here
        // (sign cases, overflow), so it is `Top` — the correct answer to "not
        // justified", not an oversight.
        let f = Fixture::new(vec![
            Pred::Interval { lo: 2, hi: 3 },
            Pred::Interval { lo: 4, hi: 5 },
        ]);
        for op in [BinOp::Mul, BinOp::SDiv, BinOp::And, BinOp::Shl] {
            assert_eq!(
                f.derive(&Inst::BinOp {
                    op,
                    ty: Ty::I64,
                    lhs: v(0),
                    rhs: v(1)
                }),
                Pred::Top,
                "{op:?} must not manufacture a fact"
            );
        }
    }

    // ── Casts ───────────────────────────────────────────────────────────────

    fn cast(op: CastOp, src: Ty, dst: Ty, operand: ValueId) -> Inst {
        Inst::Cast {
            op,
            src_ty: src,
            dst_ty: dst,
            operand,
        }
    }

    #[test]
    fn zext_survives_only_for_a_non_negative_interval() {
        let f = Fixture::new(vec![
            Pred::Interval { lo: 0, hi: 7 },
            Pred::Interval { lo: -1, hi: 7 },
        ]);
        // (a) justified: a non-negative value zero-extends to itself.
        assert_eq!(
            f.derive(&cast(CastOp::ZExt, Ty::I8, Ty::I64, v(0))),
            Pred::Interval { lo: 0, hi: 7 }
        );
        // (b) NOT justified: -1 zero-extends to 255 (or 2^63-1), which is
        // outside the claimed interval. Dropping the fact is the only sound
        // answer — narrowing it would be the miscompile.
        assert_eq!(
            f.derive(&cast(CastOp::ZExt, Ty::I8, Ty::I64, v(1))),
            Pred::Top
        );
    }

    #[test]
    fn sext_survives_only_from_a_signed_carrier() {
        let f = Fixture::new(vec![Pred::Interval { lo: -8, hi: 7 }]);
        // (a) justified: sign extension preserves a signed value.
        assert_eq!(
            f.derive(&cast(CastOp::SExt, Ty::I8, Ty::I64, v(0))),
            Pred::Interval { lo: -8, hi: 7 }
        );
        // (b) NOT justified from an unsigned carrier: the high bit is data,
        // not a sign, so extending it reinterprets the value.
        assert_eq!(
            f.derive(&cast(CastOp::SExt, Ty::U8, Ty::I64, v(0))),
            Pred::Top
        );
    }

    #[test]
    fn trunc_survives_only_when_the_interval_already_fits() {
        let f = Fixture::new(vec![
            Pred::Interval { lo: 0, hi: 7 },
            Pred::Interval { lo: 0, hi: 300 },
        ]);
        // (a) justified: [0,7] fits `i8`, so truncation is the identity.
        assert_eq!(
            f.derive(&cast(CastOp::Trunc, Ty::I64, Ty::I8, v(0))),
            Pred::Interval { lo: 0, hi: 7 }
        );
        // (b) NOT justified: 300 wraps to 44 in `i8`. The width change could
        // wrap, so the fact is dropped.
        assert_eq!(
            f.derive(&cast(CastOp::Trunc, Ty::I64, Ty::I8, v(1))),
            Pred::Top
        );
    }

    #[test]
    fn a_reinterpreting_cast_never_carries_an_integer_fact_across() {
        let f = Fixture::new(vec![Pred::Interval { lo: 0, hi: 7 }]);
        for op in [
            CastOp::Bitcast,
            CastOp::Transmute,
            CastOp::IntToPtr,
            CastOp::SIToFP,
            CastOp::FPToSI,
        ] {
            assert_eq!(
                f.derive(&cast(op, Ty::I64, Ty::I64, v(0))),
                Pred::Top,
                "{op:?} must not carry an integer fact across"
            );
        }
    }

    // ── The convention is never manufactured ────────────────────────────────

    #[test]
    fn arithmetic_never_promotes_a_number_into_a_convention() {
        // THE LOAD-BEARING NEGATIVE. Propagation derives NUMBERS. It must
        // never conclude that a value is a member of, or an index into, a
        // universe — that is a convention, it is not derivable from the
        // arithmetic, and inventing it is precisely the miscompile.
        let univs = vec![Universe::IntRange { lo: 1, hi: 8 }];
        let member = Pred::InUniverse(UnivId::new(0), crate::pred::Space::Member);
        let f = Fixture::with_tables(
            vec![member.clone(), Pred::Interval { lo: 1, hi: 1 }],
            univs,
            vec![member, Pred::Interval { lo: 1, hi: 1 }],
        );
        // member(1..=8) + 1 is numerically [2, 9] — and that is ALL it is.
        let derived = f.derive(&add(Ty::I64, v(0), v(1)));
        assert_eq!(derived, Pred::Interval { lo: 2, hi: 9 });
        assert!(
            derived.universe().is_none(),
            "a derived fact must never carry a universe the arithmetic did not \
             establish"
        );
    }

    // ── assumed_fact ────────────────────────────────────────────────────────

    #[test]
    fn assumed_fact_prefers_the_stronger_claim_and_never_invents_one() {
        let preds = vec![
            Pred::Interval { lo: 0, hi: 9 },
            Pred::Interval { lo: 2, hi: 5 },
        ];
        let t = PredTable::new(&preds, &[]);
        // The derived claim is stronger => take it.
        assert_eq!(
            assumed_fact(&t, &preds[0], &preds[1]),
            Pred::Interval { lo: 2, hi: 5 }
        );
        // The declared claim is stronger => keep it.
        assert_eq!(
            assumed_fact(&t, &preds[1], &preds[0]),
            Pred::Interval { lo: 2, hi: 5 }
        );
        // Nothing derived => the declaration stands untouched.
        assert_eq!(
            assumed_fact(&t, &preds[1], &Pred::Top),
            Pred::Interval { lo: 2, hi: 5 }
        );
        // Nothing declared => the derived fact stands.
        assert_eq!(
            assumed_fact(&t, &Pred::Top, &preds[1]),
            Pred::Interval { lo: 2, hi: 5 }
        );
    }

    #[test]
    fn contradiction_is_decided_only_when_the_bounds_are_disjoint() {
        let preds = vec![
            Pred::Interval { lo: 1, hi: 8 },
            Pred::Interval { lo: 100, hi: 107 },
            Pred::Interval { lo: 5, hi: 12 },
            Pred::NonZero,
        ];
        let t = PredTable::new(&preds, &[]);
        assert!(t.contradicts(&preds[0], &preds[1]), "disjoint");
        assert!(t.contradicts(&preds[1], &preds[0]), "symmetric");
        assert!(!t.contradicts(&preds[0], &preds[2]), "overlapping");
        assert!(
            !t.contradicts(&preds[0], &preds[3]),
            "undecided must answer false — a spurious hard error is not \
             acceptable here"
        );
        assert!(
            !t.contradicts(&preds[0], &Pred::Bottom),
            "`bottom` is an explicit dead-path marker, not a frontend bug"
        );
        // A `PredId`-free sanity check that the derived side is what a real
        // propagation would produce.
        let _ = PredId::new(0);
    }
}
