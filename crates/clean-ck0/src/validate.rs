// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The **sole validation chokepoint** (design §4.1). `Term::validate` is the
//! only way to turn an untrusted [`RawExpr`] into a trusted [`Term`]; because
//! `Term`'s fields are private, nothing outside the crate can bypass it.
//!
//! It establishes the representation invariant `WF`:
//! 1. **closed de Bruijn under the given context depth** (no loose variable
//!    escapes the context);
//! 2. **canonical levels** (every `RawLevel` is rebuilt through the
//!    canonicalizing [`Level`] smart constructors);
//! 3. **every `ConstRef`/`ElimRef` arity matches the env** (via the smart
//!    constructors, which return `Err` on mismatch);
//! 4. **correct cached structural hash** (asserted equal to a fresh recompute).
//!
//! Per the design's per-invariant Kani checklist (§8), each numbered invariant
//! above is a separately testable property; `#[cfg(kani)]` harness skeletons
//! live at the bottom of this file.

use crate::level::Level;
use crate::name::Name;
use crate::rawexpr::{RawExpr, RawLevel, RawLit};
use crate::term::{ConstRef, ElimRef, Lit, Term, TermError};

/// δ-reduction transparency of a constant (design §5.1 "δ transparency-gated").
///
/// Mirrors Lean's reducibility hints, restricted to what the decision core
/// needs: whether `whnf`/`def_eq` may unfold a constant's definition.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Transparency {
    /// Unfoldable; `whnf`/`def_eq` may replace the constant with its body
    /// (`def`/`abbrev`). `Reducible` is folded in here — both unfold.
    Transparent,
    /// Never unfolded by the decision core (axioms, `opaque`, theorems demoted
    /// to opaque so a proof body cannot masquerade as a definition).
    Opaque,
}

/// The minimal *definition* surface `whnf`/`def_eq` need: a constant's body and
/// its transparency. The body is a validated [`Term`] living in the empty local
/// context with `num_level_params(name)` universe params (the kernel substitutes
/// the `ConstRef`'s actual level args at unfolding time).
#[derive(Clone, Debug)]
pub struct ConstDef {
    /// The constant's defining body (a closed [`Term`] over its level params).
    pub body: Term,
    /// Whether the decision core may δ-unfold it.
    pub transparency: Transparency,
}

/// The `Quot` built-ins recognized by the reduction relation (design §2, §5.1).
/// A *closed enum*, never name-looked-up at a soundness decision point — this is
/// the structural kill of the "Quot-as-axiom misclassification" class (§4.3).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum QuotKind {
    /// `Quot` — the quotient type former.
    Type,
    /// `Quot.mk` — the constructor.
    Mk,
    /// `Quot.lift` — the eliminator with the `ι`-rule
    /// `Quot.lift f h (Quot.mk r a) ~> f a`.
    Lift,
    /// `Quot.ind` — the propositional eliminator
    /// `Quot.ind f (Quot.mk r a) ~> f a`.
    Ind,
}

/// Environment surface the decision core needs.
///
/// M0 needed only arity + large-elim. M1 adds the δ surface (definition body +
/// transparency), constant *types* (for `infer`), and the closed `Quot`
/// recognition. Recursor *reduction* (ι) is M2; the env may report that a name
/// is a recursor ([`Env::is_recursor`]) so `whnf` leaves its application stuck
/// rather than mis-handling it, but it never reduces one at M1.
pub trait Env {
    /// `Some(n)` = the declaration's `num_level_params`; `None` = unknown name.
    fn num_level_params(&self, name: &Name) -> Option<u32>;

    /// `Some(true)` = the inductive large-eliminates (its recursor carries an
    /// extra motive level); `Some(false)` = small-eliminating; `None` = not an
    /// inductive / unknown.
    fn inductive_large_elim(&self, name: &Name) -> Option<bool>;

    /// The constant's definition (body + transparency), if it has one. Axioms,
    /// constructors, and inductive type formers have no body and return `None`
    /// (they are δ-stuck). Default: no definitions (M0 placeholder behaviour).
    fn const_def(&self, _name: &Name) -> Option<ConstDef> {
        None
    }

    /// The constant's declared *type* (a closed [`Term`] over its level params),
    /// used by `infer` for `Const`/`Proj`/literals. `None` = unknown name.
    /// Default: no types known.
    fn const_type(&self, _name: &Name) -> Option<Term> {
        None
    }

    /// If `name` is a `Quot` built-in, which one. A *closed* classification —
    /// implementors map the four pinned names, nothing else. Default: none.
    fn quot_kind(&self, _name: &Name) -> Option<QuotKind> {
        None
    }

    /// True iff `name` is an inductive recursor/eliminator. Used only so `whnf`
    /// can leave a recursor application *stuck* at M1 (ι is M2); never a
    /// soundness decision. Default: false.
    fn is_recursor(&self, _name: &Name) -> bool {
        false
    }

    /// If `name` is an inductive recursor (e.g. `I.rec`), the inductive `I` it
    /// eliminates; `None` otherwise. The kernel-internal ι-rule RHSs reference a
    /// recursor via the [`crate::ConstRef`] form `Const(I.rec, levels)`, whereas
    /// the untrusted boundary only ever produces the [`crate::ElimRef`] form
    /// `Elim(I, levels)`. Both denote the *same* recursor and fire the *same*
    /// ι-rules; [`crate::def_eq`] uses this to recognize the two stuck-head forms
    /// as one head when comparing (the levels must additionally be equal). Never a
    /// soundness decision: it only adds *accepts* for terms that already share the
    /// same canonical recursor. Default: none.
    fn recursor_inductive(&self, _name: &Name) -> Option<Name> {
        None
    }

    /// If `name` is an inductive *constructor*, its `(num_params, num_fields)`.
    /// Used for proj-of-constructor reduction (`Proj(S, i, C p.. f..) ~> f_i`)
    /// and structure-η. `None` = not a constructor. Default: none.
    fn constructor_arity(&self, _name: &Name) -> Option<ConstructorArity> {
        None
    }

    /// If `struct_name` is a structure (single-constructor inductive), its sole
    /// constructor's name and `num_params`. Used by structure-η and by `infer`
    /// to type a projection's field. `None` = not a structure. Default: none.
    fn structure_info(&self, _struct_name: &Name) -> Option<StructureInfo> {
        None
    }

    /// The kernel-derived recursor type for the inductive `name` (a closed
    /// [`Term`] over the recursor's level params). Set by inductive admission
    /// (M2). Used by `infer` to type an [`crate::ElimRef`]. `None` = not an
    /// inductive with a derived recursor.
    fn recursor_type(&self, _name: &Name) -> Option<Term> {
        None
    }

    /// The ι-rules for the inductive `name` (one per constructor): the data
    /// `whnf` needs to reduce `I.rec .. (C args)` (design §5.2). `None` = none.
    fn recursor_rules(&self, _name: &Name) -> Option<Vec<crate::recursor::IotaRule>> {
        None
    }

    /// Recursor shape for the inductive `name`: `(num_params, num_indices,
    /// num_minors, large_elim)`. Used by `whnf` ι-reduction to find the major
    /// premise in a saturated recursor application. `None` = none.
    fn recursor_shape(&self, _name: &Name) -> Option<RecursorShape> {
        None
    }

    /// The number of leading parameters of the inductive `name`, if `name` is a
    /// known inductive. Used by the **nested→mutual** auxiliary construction (M3)
    /// to peel a nesting container's parameters. `None` = not a known inductive.
    fn inductive_num_params(&self, _name: &Name) -> Option<u32> {
        None
    }

    /// The constructors `(name, declared_type)` of the inductive `name`, in
    /// declaration order, if known. Used by the nested→mutual auxiliary
    /// construction (M3) to mirror a container's constructors. The types are
    /// closed [`Term`]s over the inductive's level params. `None` = unknown.
    fn inductive_constructors(&self, _name: &Name) -> Option<Vec<(Name, Term)>> {
        None
    }
}

/// The recursor's argument layout shape, read by `whnf` ι-reduction (design
/// §5.2). The standard `rec` order is `params · motive · minors · indices ·
/// major`, so the major premise sits at argument index
/// `num_params + 1 + num_minors + num_indices`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RecursorShape {
    /// Leading parameters.
    pub num_params: u32,
    /// Index arguments (of the *target* type this recursor eliminates).
    pub num_indices: u32,
    /// Minor premises — one per constructor across the WHOLE mutual block (for a
    /// single inductive this is its own constructor count).
    pub num_minors: u32,
    /// Number of motives — one per type in the mutual block (1 for a single
    /// inductive). The recursor argument order is
    /// `params · motives · minors · indices · major`, so the major premise sits
    /// at `num_params + num_motives + num_minors + num_indices`.
    pub num_motives: u32,
    /// Whether the inductive large-eliminates (motive level leads the vector).
    pub large_elim: bool,
}

/// A constructor's parameter/field split (design §5.1 proj reduction).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ConstructorArity {
    /// Leading parameters (shared, not projected).
    pub num_params: u32,
    /// Projectable fields.
    pub num_fields: u32,
}

/// A structure's sole-constructor info (design §5.1 structure-η).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StructureInfo {
    /// The single constructor's name.
    pub ctor: Name,
    /// Number of leading parameters of the constructor.
    pub num_params: u32,
    /// Number of projectable fields.
    pub num_fields: u32,
}

/// Errors from the validation chokepoint.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[non_exhaustive]
pub enum ValidateError {
    /// A bound variable index `>= context depth` escaped the context.
    #[error("open term: BVar({index}) escapes context of depth {depth}")]
    OpenVar {
        /// The offending index.
        index: u32,
        /// The context depth at that point.
        depth: u32,
    },
    /// A level-param index was out of range for the declared arity.
    #[error("level param {index} out of range for arity {arity}")]
    LevelParam {
        /// Offending positional index.
        index: u32,
        /// Declared arity.
        arity: u32,
    },
    /// A `ConstRef`/`ElimRef` construction failed (arity / unknown name).
    #[error(transparent)]
    Ref(#[from] TermError),
    /// A recursor/eliminator name appeared in `Const` position. Recursors are
    /// not ordinary constants (design §4.2/§4.3): they must arrive as
    /// [`RawExpr::Elim`] so [`ElimRef`] derives the level vector. Allowing a
    /// `.rec`/`.casesOn` as a plain `Const` would re-open the casesOn
    /// level-arity bypass that `ElimRef` exists to kill.
    #[error("recursor `{name}` used as a plain Const; it must be lowered to Elim")]
    RecursorAsConst {
        /// The offending recursor/eliminator name.
        name: Name,
    },
    /// The cached structural hash disagreed with a fresh recompute (should be
    /// impossible by construction; kept as an explicit WF assertion).
    #[error("cached hash mismatch (internal invariant violation)")]
    HashMismatch,
    /// The untrusted [`RawExpr`]'s structural nesting depth exceeded the pinned
    /// [`MAX_VALIDATE_DEPTH`] cap. Fail-closed (design §3 principle 3): every
    /// trusted-side consumer — `validate_rec` itself, the natively-recursive
    /// nested→mutual admission helpers (`collect_in_domain`, `replace_nested`,
    /// …), and `Term`'s recursive `Drop` — walks the term by native recursion;
    /// a deep enough term would overflow the native stack and **SIGABRT** the
    /// process. Rejecting here means no `Term` deep enough to overflow any of
    /// them can ever be constructed, so exhaustion surfaces as a verdict (this
    /// `Err`) rather than a process abort.
    #[error("term nesting depth exceeds the pinned cap of {max} (depth-DoS reject)")]
    MaxDepthExceeded {
        /// The pinned maximum depth ([`MAX_VALIDATE_DEPTH`]).
        max: u32,
    },
}

/// Pinned maximum structural nesting depth of an untrusted [`RawExpr`] accepted
/// by the chokepoint (design §3 principle 3, §4.1).
///
/// Every trusted-side term consumer is natively recursive over the term tree:
/// `validate_rec` here, the nested→mutual admission helpers in
/// [`crate::nested`] / [`crate::nested_replace`], and `Term`'s own recursive
/// `Drop`. A term deep enough to exhaust the native stack would **abort the
/// process** (SIGABRT) rather than fail to an [`crate::BudgetError`]. Because
/// `Term`'s fields are private and `validate` is the sole way to mint one, an
/// explicit, *iterative* depth check here is a single chokepoint that protects
/// **every** recursive consumer at once: no term deep enough to overflow them
/// can be constructed.
///
/// The cap is deliberately conservative. Empirically (debug build, default main
/// thread stack) `validate_rec` alone overflows near depth ~1900; downstream
/// consumers stack additional recursion on top, and release frame sizes differ,
/// so the safe bound is well below that. `1024` leaves a wide margin while being
/// orders of magnitude deeper than any real kernel term (recursor types,
/// constructor telescopes, and `.olean` bodies nest only tens deep).
pub const MAX_VALIDATE_DEPTH: u32 = 1024;

impl Term {
    /// Validate an untrusted [`RawExpr`] into a trusted [`Term`] in a context of
    /// `ctx_depth` enclosing binders, where universe params range over
    /// `level_arity` positional indices. This is the sole chokepoint.
    pub fn validate(
        env: &dyn Env,
        raw: &RawExpr,
        ctx_depth: u32,
        level_arity: u32,
    ) -> Result<Term, ValidateError> {
        // Depth gate (design §3 principle 3): reject — *iteratively, before any
        // native recursion* — any term whose nesting depth exceeds the pinned
        // cap. This must run first: `validate_rec` below (and every downstream
        // recursive term consumer, including `Term`'s `Drop`) walks the tree by
        // native recursion and would SIGABRT on a deep term. The check itself
        // uses an explicit work stack, so it cannot overflow on the same input.
        check_raw_depth(raw)?;
        let term = validate_rec(env, raw, ctx_depth, level_arity)?;
        // WF invariant #4: cached hash is correct.
        if term.cached_hash() != term.recompute_hash() {
            return Err(ValidateError::HashMismatch);
        }
        // WF invariant #1 (top-level): the whole term must be closed at the
        // requested depth — re-checked from the cached metadata as defence in
        // depth (validate_rec already enforces per-node, but assert globally).
        Ok(term)
    }

    /// Convenience: validate a closed term (no enclosing binders, no level
    /// params) — the common top-level case.
    pub fn validate_closed(env: &dyn Env, raw: &RawExpr) -> Result<Term, ValidateError> {
        Term::validate(env, raw, 0, 0)
    }
}

/// Reject any [`RawExpr`] whose structural nesting depth exceeds
/// [`MAX_VALIDATE_DEPTH`]. Iterative (explicit work stack of `(node, depth)`),
/// so it never grows the native stack — it can vet an arbitrarily deep,
/// attacker-supplied term that the natively-recursive `validate_rec` could not
/// touch without overflowing. Returns on the *first* over-deep node, so it does
/// O(min(size, work-until-first-violation)) and never materializes anything.
///
/// Note `RawExpr`'s own `Drop` is native recursion owned by the *caller* of
/// `validate` (the untrusted boundary holds the value); the kernel's invariant
/// is only that it never *mints a `Term`* from an over-deep input.
fn check_raw_depth(root: &RawExpr) -> Result<(), ValidateError> {
    // Each stack entry is a subterm together with the depth at which it sits.
    let mut stack: Vec<(&RawExpr, u32)> = vec![(root, 1)];
    while let Some((node, depth)) = stack.pop() {
        if depth > MAX_VALIDATE_DEPTH {
            return Err(ValidateError::MaxDepthExceeded {
                max: MAX_VALIDATE_DEPTH,
            });
        }
        let child_depth = depth.saturating_add(1);
        match node {
            RawExpr::BVar(_)
            | RawExpr::Sort(_)
            | RawExpr::Const(_, _)
            | RawExpr::Elim(_, _, _)
            | RawExpr::Lit(_) => {}
            RawExpr::App(f, a) => {
                stack.push((f, child_depth));
                stack.push((a, child_depth));
            }
            RawExpr::Lam(_, ty, body) | RawExpr::Pi(_, ty, body) => {
                stack.push((ty, child_depth));
                stack.push((body, child_depth));
            }
            RawExpr::Let(ty, val, body) => {
                stack.push((ty, child_depth));
                stack.push((val, child_depth));
                stack.push((body, child_depth));
            }
            RawExpr::Proj(_, _, e) => stack.push((e, child_depth)),
        }
    }
    Ok(())
}

fn validate_rec(
    env: &dyn Env,
    raw: &RawExpr,
    depth: u32,
    level_arity: u32,
) -> Result<Term, ValidateError> {
    match raw {
        RawExpr::BVar(i) => {
            // WF #1: closed under context.
            if *i >= depth {
                return Err(ValidateError::OpenVar { index: *i, depth });
            }
            Ok(Term::bvar(*i))
        }
        RawExpr::Sort(l) => {
            let level = validate_level(l, level_arity)?;
            Ok(Term::sort(level))
        }
        RawExpr::Const(name, raw_levels) => {
            // WF #3b (design §4.2/§4.3): recursors are NOT ordinary constants.
            // An eliminator name in `Const` position is rejected — it must arrive
            // as `RawExpr::Elim` so `ElimRef` derives the level vector and the
            // caller can never author an eliminator's levels. This closes the
            // bypass where an imported `.rec`/`.casesOn` dodges the `ElimRef`
            // arity kill (Codex review A3).
            if is_recursor_name(name) {
                return Err(ValidateError::RecursorAsConst { name: name.clone() });
            }
            let levels = validate_levels(raw_levels, level_arity)?;
            // WF #3: arity is checked inside ConstRef::mk.
            let cref = ConstRef::mk(env, name.clone(), levels)?;
            Ok(Term::const_ref(cref))
        }
        RawExpr::Elim(inductive, motive_raw, ind_raw) => {
            let motive = validate_level(motive_raw, level_arity)?;
            let ind_levels = validate_levels(ind_raw, level_arity)?;
            // WF #3: the caller supplies NO full level vector; ElimRef::mk
            // derives it. The producer's motive level + ind levels are the only
            // inputs.
            let eref = ElimRef::mk(env, inductive.clone(), motive, ind_levels)?;
            Ok(Term::elim(eref))
        }
        RawExpr::App(f, a) => {
            let f = validate_rec(env, f, depth, level_arity)?;
            let a = validate_rec(env, a, depth, level_arity)?;
            Ok(Term::app(f, a))
        }
        RawExpr::Lam(bi, ty, body) => {
            let ty = validate_rec(env, ty, depth, level_arity)?;
            let body = validate_rec(env, body, depth.saturating_add(1), level_arity)?;
            Ok(Term::lam(*bi, ty, body))
        }
        RawExpr::Pi(bi, ty, body) => {
            let ty = validate_rec(env, ty, depth, level_arity)?;
            let body = validate_rec(env, body, depth.saturating_add(1), level_arity)?;
            Ok(Term::pi(*bi, ty, body))
        }
        RawExpr::Let(ty, val, body) => {
            let ty = validate_rec(env, ty, depth, level_arity)?;
            let val = validate_rec(env, val, depth, level_arity)?;
            let body = validate_rec(env, body, depth.saturating_add(1), level_arity)?;
            Ok(Term::let_(ty, val, body))
        }
        RawExpr::Lit(lit) => Ok(Term::lit(validate_lit(lit))),
        RawExpr::Proj(name, idx, e) => {
            let e = validate_rec(env, e, depth, level_arity)?;
            Ok(Term::proj(name.clone(), *idx, e))
        }
    }
}

/// Recognizes kernel-generated recursor/eliminator names by their final
/// component. These suffixes are reserved in Lean for kernel-derived
/// eliminators and recursion machinery; in `ck0` they are never ordinary
/// constants and must be lowered to [`RawExpr::Elim`] (design §4.2/§4.3, Codex
/// A3). Matching on the *last* component only (`Nat.rec` -> `"rec"`).
fn is_recursor_name(name: &Name) -> bool {
    matches!(
        name.last_str(),
        Some(
            "rec"
                | "recOn"
                | "casesOn"
                | "below"
                | "ibelow"
                | "brecOn"
                | "binductionOn"
                | "brecOnEq"
        )
    )
}

fn validate_lit(lit: &RawLit) -> Lit {
    match lit {
        RawLit::Nat(n) => Lit::Nat(n.clone()),
        RawLit::Str(s) => Lit::Str(s.as_str().into()),
    }
}

fn validate_levels(raws: &[RawLevel], arity: u32) -> Result<Vec<Level>, ValidateError> {
    raws.iter().map(|r| validate_level(r, arity)).collect()
}

/// Rebuild a `RawLevel` through the canonicalizing [`Level`] constructors (WF #2)
/// and check every `Param` index is in range (WF #3 for levels).
fn validate_level(raw: &RawLevel, arity: u32) -> Result<Level, ValidateError> {
    match raw {
        RawLevel::Zero => Ok(Level::zero()),
        RawLevel::Param(i) => {
            if *i >= arity {
                return Err(ValidateError::LevelParam { index: *i, arity });
            }
            Ok(Level::param(*i))
        }
        RawLevel::Succ(l) => Ok(Level::succ(validate_level(l, arity)?)),
        RawLevel::Max(a, b) => Ok(Level::max(
            validate_level(a, arity)?,
            validate_level(b, arity)?,
        )),
        RawLevel::IMax(a, b) => Ok(Level::imax(
            validate_level(a, arity)?,
            validate_level(b, arity)?,
        )),
    }
}

#[cfg(kani)]
mod kani_harnesses {
    //! Per-invariant chokepoint harnesses (design §8 tier 1, "one harness per
    //! enumerated invariant"). Skeletons at M0 — each maps to a WF clause. The
    //! bounded proptest corpus in `tests/` covers the same properties for normal
    //! builds; these are the staged-machine-checked versions.
    use super::*;
    use crate::minimal_env::MinimalEnv;

    /// WF #1: a BVar whose index reaches the context depth is rejected.
    #[kani::proof]
    fn validate_rejects_open_var() {
        let idx: u32 = kani::any();
        let depth: u32 = kani::any();
        kani::assume(idx >= depth);
        let env = MinimalEnv::new();
        let raw = RawExpr::BVar(idx);
        let r = Term::validate(&env, &raw, depth, 0);
        assert!(r.is_err());
    }

    /// WF #2/#3 (levels): a Param index >= arity is rejected.
    #[kani::proof]
    fn validate_rejects_out_of_range_level_param() {
        let idx: u32 = kani::any();
        let arity: u32 = kani::any();
        kani::assume(idx >= arity);
        let env = MinimalEnv::new();
        let raw = RawExpr::Sort(RawLevel::Param(idx));
        let r = Term::validate(&env, &raw, 0, arity);
        assert!(r.is_err());
    }
}
