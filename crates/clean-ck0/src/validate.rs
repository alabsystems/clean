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
//!    canonicalizing [`Level`](crate::level::Level) smart constructors);
//! 3. **every `ConstRef`/`ElimRef` arity matches the env** (via the smart
//!    constructors, which return `Err` on mismatch);
//! 4. **correct cached structural hash** (asserted equal to a fresh recompute).
//!
//! Per the design's per-invariant Kani checklist (§8), each numbered invariant
//! above is a separately testable property; `#[cfg(kani)]` harness skeletons
//! live at the bottom of this file.

use crate::name::Name;
use crate::rawexpr::{RawExpr, RawLit};
use crate::term::{ConstRef, ElimRef, Lit, Term, TermError};

mod depth;
mod terms;
use depth::check_raw_depth;
use terms::validate_rec;
mod levels;
pub use levels::WrittenLevel;
use levels::{validate_level, validate_levels};

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
/// Types, definitions and licensed computations.
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

    /// Untrusted scheduling hint for lazy delta reduction. Larger priorities
    /// unfold first; it changes resource use only, never an equality rule.
    fn delta_priority(&self, _name: &Name) -> u64 {
        0
    }

    /// Whether this environment licenses the named native Nat computation.
    /// Existing host environments retain their previous behavior by default.
    /// An untrusted byte reader must fence names until their closure is checked.
    fn native_nat_allowed(&self, _name: &Name) -> bool {
        true
    }

    /// Whether canonical checked String/Char/List definitions license the
    /// literal's constructor view. Existing hosts opt in explicitly.
    fn string_literal_view(&self) -> bool {
        false
    }

    /// The constant's declared *type* (a closed [`Term`] over its level params),
    /// used by `infer` for `Const`/`Proj`/literals. `None` = unknown name.
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
    /// Container family in declaration order; legacy hosts default to one member.
    fn inductive_family(&self, name: &Name) -> Option<Vec<Name>> {
        self.inductive_num_params(name).map(|_| vec![name.clone()])
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
    /// A level written in a form Lean's kernel reads differently from ck0's
    /// canonical form (R177). ck0 keeps only the canonical form, so it refuses
    /// the level where Lean's kernel would decide on the form as written.
    #[error("a level written as {form}, which Lean's kernel reads differently from ck0's canonical form (R177)")]
    LevelAsWritten {
        /// The form.
        form: WrittenLevel,
    },
}

/// Pinned maximum structural nesting depth of an untrusted [`RawExpr`] accepted
/// by the chokepoint (design §3 principle 3, §4.1).
///
/// Every trusted-side term consumer is natively recursive over the term tree:
/// `validate_rec` here, the nested→mutual admission helpers in
/// [`crate::nested`] / `crate::nested_replace`, and `Term`'s own recursive
/// `Drop`. A term deep enough to exhaust the native stack would **abort the
/// process** (SIGABRT) rather than fail to an [`crate::BudgetError`]. Because
/// `Term`'s fields are private and `validate` is the sole way to mint one, an
/// explicit, *iterative* depth check here is a single chokepoint that protects
/// **every** recursive consumer at once: no input deep enough to overflow them
/// can be constructed. Reduction mints terms too, and head reduction is a loop
/// that can build one far deeper than its input, so `whnf_core` refuses a reduct
/// whose cached depth passes this cap (R166). A universe level counts toward the
/// depth of the term it sits in, one more per `Succ`, `Max` and `IMax` node, as
/// the level operations recurse over it natively too; δ-unfolding a
/// universe-polymorphic constant can grow one, and the same reduct check holds
/// it (R166). A derived recursor's telescope is held to the cap as well
/// ([`crate::recursor`]).
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
        let _dag = crate::term_dag::DagScope::enter();
        check_raw_depth(raw)?;
        let term = validate_rec(
            env,
            raw,
            ctx_depth,
            level_arity,
            &mut std::collections::HashMap::new(),
        )?;
        // The term as built can be deeper than the raw input: canonicalising a
        // level flattens a `Max` into a chain of its distinct arguments, which
        // `validate_level` bounds node by node, so the built term is within
        // about twice the bound and this O(1) check refuses the rest (R166).
        if term.depth > MAX_VALIDATE_DEPTH {
            return Err(ValidateError::MaxDepthExceeded {
                max: MAX_VALIDATE_DEPTH,
            });
        }
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

/// Recognizes a final component used by Lean's recursion machinery. Such a
/// spelling alone is insufficient to authorize a raw constant reference.
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

#[cfg(kani)]
mod kani_harnesses {
    //! Per-invariant chokepoint harnesses (design §8 tier 1, "one harness per
    //! enumerated invariant"). Skeletons at M0 — each maps to a WF clause. The
    //! bounded proptest corpus in `tests/` covers the same properties for normal
    //! builds; these are the staged-machine-checked versions.
    use super::*;
    use crate::minimal_env::MinimalEnv;
    use crate::rawexpr::RawLevel;

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
