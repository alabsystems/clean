// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The **trusted, private** [`Term`] (design §4.1) plus the two reference types
//! [`ConstRef`] and [`ElimRef`] whose smart constructors establish the level
//! invariants that killed Incident #1.
//!
//! All fields are private. The only ways to obtain a `Term` are
//! [`crate::Term::validate`] (the chokepoint, in [`crate::validate`]) and the
//! internal builders here, which the chokepoint calls. Nothing outside this
//! crate can fabricate an ill-formed term, a wrong-arity `ConstRef`, or a
//! caller-authored eliminator level vector:
//!
//! * **`ConstRef`** is built only via [`ConstRef::mk`], which reads the
//!   declaration's `num_level_params` from the env and returns `Err` unless the
//!   supplied level vector matches. There is no `Term` variant holding a free
//!   `Vec<Level>` for a constant — the levels live inside the validated `ConstRef`.
//! * **`ElimRef`** is built only via [`ElimRef::mk`]; the caller supplies *only*
//!   the motive level and the inductive's own level substitution. The full level
//!   argument vector is **derived** by the kernel from the inductive's stored
//!   recursor signature. **No `Term` variant holds a free `Vec<Level>` for an
//!   eliminator.** (M0 stores the derived vector and the recipe; the full
//!   recursor *typing* is M2.)
//!
//! Every `Term` carries a cached structural hash; the chokepoint guarantees the
//! cache is correct, so `Term` equality can fast-reject on the hash.

use crate::bignat::BigNat;
use crate::level::{Level, LevelTooDeep};
use crate::name::Name;
use crate::rawexpr::BinderInfo;
use std::sync::Arc;

/// Errors specific to building the trusted reference types.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum TermError {
    /// `ConstRef::mk`: the supplied level vector length differs from the
    /// declaration's `num_level_params`. (This is the structural kill of
    /// Incident #1's emission site — the `.{0}` term cannot be constructed.)
    #[error("const '{name}': supplied {got} level args, declaration has {expected}")]
    LevelArity {
        /// The constant.
        name: Name,
        /// Levels the caller supplied.
        got: usize,
        /// Levels the declaration requires.
        expected: usize,
    },
    /// `ElimRef::mk`: the inductive is unknown to the env.
    #[error("eliminator: unknown inductive '{name}'")]
    UnknownInductive {
        /// The inductive name.
        name: Name,
    },
    /// `ElimRef::mk`: the supplied `ind_levels` vector length differs from the
    /// inductive's `num_level_params`. This is the eliminator-side dual of
    /// [`TermError::LevelArity`] and the structural kill of Incident #1's
    /// *level-count* class: the derived recursor level vector's length is
    /// definitionally `num_level_params(I) + (1 iff large-eliminating)`, so a
    /// caller-chosen `ind_levels` count is a `Rejected`, never an accepted term
    /// (design §4.2/§4.3 Incident #1).
    #[error(
        "eliminator '{inductive}': supplied {got} inductive level args, \
         inductive has {expected} level params"
    )]
    ElimLevelArity {
        /// The inductive.
        inductive: Name,
        /// Level args the caller supplied for the inductive's own params.
        got: usize,
        /// Level params the inductive declares.
        expected: usize,
    },
}

/// A literal carried by a [`Term`].
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Lit {
    /// arbitrary-precision natural literal
    Nat(BigNat),
    /// string literal
    Str(Box<str>),
}

/// A validated constant reference: the level vector is *guaranteed* to match the
/// declaration's arity (established by [`ConstRef::mk`]).
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ConstRef {
    name: Name,
    levels: Arc<[Level]>,
}

impl ConstRef {
    /// Build a constant reference, checking the level vector against the
    /// declaration's `num_level_params`. `pub(crate)` is not used here because
    /// the *guarantee* is the smart constructor; the type's fields stay private
    /// so the guarantee cannot be bypassed.
    pub fn mk(
        env: &dyn crate::validate::Env,
        name: Name,
        levels: Vec<Level>,
    ) -> Result<Self, TermError> {
        let expected = env
            .num_level_params(&name)
            .ok_or_else(|| TermError::LevelArity {
                name: name.clone(),
                got: levels.len(),
                expected: 0,
            })?;
        let expected_usize = usize::try_from(expected).unwrap_or(usize::MAX);
        if levels.len() != expected_usize {
            return Err(TermError::LevelArity {
                name,
                got: levels.len(),
                expected: expected_usize,
            });
        }
        Ok(ConstRef {
            name,
            levels: levels.into(),
        })
    }

    /// A level-argument-free constant reference minted by the **trusted native
    /// reducers** (design §3.2): the `Nat`/`Bool` constructors the native rules
    /// produce (`Bool.true`, `Nat.zero`, ...) are nullary and universe-monomorphic,
    /// so no env arity check is meaningful. Crate-internal; never reachable from
    /// the untrusted boundary (which only constructs `ConstRef` via [`ConstRef::mk`]).
    pub(crate) fn native(name: Name) -> Self {
        ConstRef {
            name,
            levels: Vec::new().into(),
        }
    }

    /// Build a `ConstRef` with a kernel-chosen level vector, **without** the
    /// construction-time env arity check. Crate-internal: used only by the
    /// **recursor derivation** (design §5.2), which constructs
    /// `I`/constructor/`I.rec` references at the exact arities it is itself
    /// deriving — there is no untrusted producer in this path.
    ///
    /// The arity guarantee is re-established by **checking, not construction**:
    /// the generated recursor type is re-validated by a full kernel `infer`
    /// (`recursor::kernel_check_recursor`), and [`crate::infer::infer`]'s `Const`
    /// arm independently re-checks every `Const`'s level count against the env's
    /// `num_level_params`, rejecting a mismatch with
    /// [`crate::infer::InferError::LevelArity`] (#17 — without that check,
    /// `instantiate_levels` would silently leave over-indexed `Param`s
    /// unsubstituted). Never reachable from the untrusted boundary.
    pub(crate) fn mk_unchecked_levels(name: Name, levels: Vec<Level>) -> Self {
        ConstRef {
            name,
            levels: levels.into(),
        }
    }

    /// [`ConstRef::mk_unchecked_levels`] over an already-shared level vector, so
    /// many references to one constant (the nested auxiliary's self-references)
    /// share a single allocation. Same invariant: the caller supplies exactly
    /// the declaration's level params.
    pub(crate) fn mk_unchecked_shared_levels(name: Name, levels: Arc<[Level]>) -> Self {
        ConstRef { name, levels }
    }

    /// The referenced constant's name.
    #[must_use]
    pub fn name(&self) -> &Name {
        &self.name
    }

    /// The (arity-checked) level arguments.
    #[must_use]
    pub fn levels(&self) -> &[Level] {
        &self.levels
    }

    /// Rebuild with each level arg `subst`-instantiated. Arity is preserved
    /// (substitution maps a level to a level), so the invariant established by
    /// [`ConstRef::mk`] is maintained without re-consulting the env. Crate-
    /// internal: used by δ-unfold / const-type instantiation.
    pub(crate) fn instantiate_levels(&self, subst: &[Level]) -> Result<ConstRef, LevelTooDeep> {
        Ok(ConstRef {
            name: self.name.clone(),
            levels: self
                .levels
                .iter()
                .map(|l| l.try_instantiate_params(subst))
                .collect::<Result<_, _>>()?,
        })
    }
}

/// A validated eliminator reference. The caller supplies only the motive level
/// and the inductive's own level substitution; the full level vector is derived
/// by the kernel and stored here. The caller **cannot** author a level vector
/// for an eliminator.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ElimRef {
    inductive: Name,
    /// the kernel-derived full level vector (motive level + inductive levels,
    /// in the order the recursor signature dictates). Private; no constructor
    /// lets a caller write this directly.
    derived_levels: Arc<[Level]>,
}

impl ElimRef {
    /// Build an eliminator reference. `motive_level` is the universe the motive
    /// eliminates into; `ind_levels` is the substitution for the inductive's own
    /// level params. The derived level vector is
    /// `[motive_level, ind_levels...]` when the inductive large-eliminates, else
    /// `[ind_levels...]` — derived from the env's recorded recursor signature
    /// (design §4.2). M2 fills in the full recursor *type*; M0 establishes the
    /// level-derivation invariant.
    ///
    /// `ind_levels` is a substitution for the inductive's *own* level params, so
    /// its length must equal `env.num_level_params(&inductive)`. Enforcing this
    /// here is what makes the derived vector's length provably
    /// `num_level_params(I) + (1 iff large_elim)` rather than caller-chosen — the
    /// level-count kill of Incident #1 (design §4.3, WF #3 in
    /// [`crate::validate`]). A mismatch is [`TermError::ElimLevelArity`], i.e. a
    /// `Rejected`, never an accepted `Term`.
    pub fn mk(
        env: &dyn crate::validate::Env,
        inductive: Name,
        motive_level: Level,
        ind_levels: Vec<Level>,
    ) -> Result<Self, TermError> {
        let large_elim =
            env.inductive_large_elim(&inductive)
                .ok_or_else(|| TermError::UnknownInductive {
                    name: inductive.clone(),
                })?;
        // WF #3 (eliminator level arity): the inductive must declare a level-param
        // count, and `ind_levels` must match it. An inductive that large-/small-
        // eliminates is still a declaration with `num_level_params`; if the env
        // knows it as an inductive it must know its arity. A `None` here means the
        // env's inductive registry is internally inconsistent with its declaration
        // table, which we reject rather than bless a caller-chosen vector.
        let expected =
            env.num_level_params(&inductive)
                .ok_or_else(|| TermError::UnknownInductive {
                    name: inductive.clone(),
                })?;
        let expected_usize = usize::try_from(expected).unwrap_or(usize::MAX);
        if ind_levels.len() != expected_usize {
            return Err(TermError::ElimLevelArity {
                inductive,
                got: ind_levels.len(),
                expected: expected_usize,
            });
        }
        // The derived vector length is now provably `expected_usize + large_elim`.
        // It is built in `ind_levels`' own allocation (the motive level, if any,
        // goes in front), not in a fresh `Vec::with_capacity` sized from the
        // env-reported arity: that count is a `usize` the allocation lane cannot
        // bound, while the caller's vector is memory already held.
        let mut derived = ind_levels;
        if large_elim {
            derived.insert(0, motive_level);
        }
        Ok(ElimRef {
            inductive,
            derived_levels: derived.into(),
        })
    }

    /// The inductive being eliminated.
    #[must_use]
    pub fn inductive(&self) -> &Name {
        &self.inductive
    }

    /// The kernel-derived full level vector.
    #[must_use]
    pub fn levels(&self) -> &[Level] {
        &self.derived_levels
    }

    /// Rebuild with each derived level `subst`-instantiated. Length is preserved.
    /// Crate-internal: used by level instantiation of a `Term` containing an
    /// `Elim`.
    pub(crate) fn instantiate_levels(&self, subst: &[Level]) -> Result<ElimRef, LevelTooDeep> {
        Ok(ElimRef {
            inductive: self.inductive.clone(),
            derived_levels: self
                .derived_levels
                .iter()
                .map(|l| l.try_instantiate_params(subst))
                .collect::<Result<_, _>>()?,
        })
    }
}

/// The internal, trusted term node. Constructed only via the builders in this
/// module (called by the validation chokepoint). Fields are `pub(crate)` — i.e.
/// **private to everything outside the crate**, which is the soundness-relevant
/// boundary (design §4.1) — so the crate's own `term_ops` module can implement
/// de Bruijn / equality / hashing against them without re-exposing them.
#[derive(Clone, Debug)]
pub struct Term {
    pub(crate) kind: Arc<TermKind>,
    /// cached structural hash; the chokepoint guarantees it equals
    /// [`TermKind`]'s structural hash so equality can fast-reject on it.
    pub(crate) hash: u64,
    /// One past the largest loose (free) de Bruijn index of the subtree (`0`
    /// when it is closed), computed from the children's in O(1) per node (R162:
    /// it was a whole-subtree walk per node built, quadratic in a term's size).
    /// Cached so `validate` checks closedness in O(1), and so `lift`/`instantiate`
    /// skip a subtree with no index at or above their cutoff.
    pub(crate) loose: u32,
    /// Height of the subtree (a leaf is 1, plus its levels' depth), computed
    /// from the children's and the levels' in O(1) per child. `validate` admits
    /// no input higher than [`crate::MAX_VALIDATE_DEPTH`], and `whnf_core`
    /// refuses a reduct higher than it (R166), so every term the checker reduces
    /// stays within the depth its natively recursive consumers (`Drop`,
    /// `PartialEq`, `instantiate`, `lift`, `infer`, and the level operations
    /// they call) are sized for.
    pub(crate) depth: u32,
}

/// The shape of a [`Term`]. Note: no `Const` variant with a free level vector
/// (that is [`ConstRef`]); no eliminator variant with a free level vector
/// (that is [`ElimRef`]).
#[derive(Clone, Debug)]
pub enum TermKind {
    /// de Bruijn bound variable.
    BVar(u32),
    /// `Sort l`.
    Sort(Level),
    /// arity-checked constant reference.
    Const(ConstRef),
    /// derived-level eliminator reference applied to nothing yet (application
    /// happens via [`TermKind::App`]).
    Elim(ElimRef),
    /// application `f a`.
    App(Term, Term),
    /// lambda `λ (x : ty). body`.
    Lam(BinderInfo, Term, Term),
    /// pi `(x : ty) → body`.
    Pi(BinderInfo, Term, Term),
    /// `let _ : ty := val; body`.
    Let(Term, Term, Term),
    /// literal.
    Lit(Lit),
    /// projection `e.i` of structure `name`.
    Proj(Name, u32, Term),
}

impl Term {
    // --- builders (crate-internal; the chokepoint calls these) ---

    pub(crate) fn mk(kind: TermKind) -> Term {
        #[cfg(test)]
        NODES_BUILT.with(|n| n.set(n.get().saturating_add(1)));
        let hash = crate::term_ops::structural_hash(&kind);
        let loose = crate::term_ops::compute_loose_range(&kind);
        let depth = crate::term_ops::compute_depth(&kind);
        Term {
            kind: crate::term_dag::intern(kind, hash),
            hash,
            loose,
            depth,
        }
    }

    pub(crate) fn bvar(i: u32) -> Term {
        Term::mk(TermKind::BVar(i))
    }
    pub(crate) fn sort(l: Level) -> Term {
        Term::mk(TermKind::Sort(l))
    }
    pub(crate) fn const_ref(c: ConstRef) -> Term {
        Term::mk(TermKind::Const(c))
    }
    /// A level-free constant minted by the native reducers (e.g. `Bool.true`).
    pub(crate) fn native_const(name: Name) -> Term {
        Term::const_ref(ConstRef::native(name))
    }
    pub(crate) fn elim(e: ElimRef) -> Term {
        Term::mk(TermKind::Elim(e))
    }
    pub(crate) fn app(f: Term, a: Term) -> Term {
        Term::mk(TermKind::App(f, a))
    }
    pub(crate) fn lam(bi: BinderInfo, ty: Term, body: Term) -> Term {
        Term::mk(TermKind::Lam(bi, ty, body))
    }
    pub(crate) fn pi(bi: BinderInfo, ty: Term, body: Term) -> Term {
        Term::mk(TermKind::Pi(bi, ty, body))
    }
    pub(crate) fn let_(ty: Term, val: Term, body: Term) -> Term {
        Term::mk(TermKind::Let(ty, val, body))
    }
    pub(crate) fn lit(l: Lit) -> Term {
        Term::mk(TermKind::Lit(l))
    }
    pub(crate) fn proj(name: Name, idx: u32, e: Term) -> Term {
        Term::mk(TermKind::Proj(name, idx, e))
    }

    // --- accessors ---

    /// The node shape.
    #[must_use]
    pub fn kind(&self) -> &TermKind {
        #[cfg(test)]
        KIND_READS.with(|n| n.set(n.get().saturating_add(1)));
        &self.kind
    }

    /// The cached structural hash (guaranteed correct by the chokepoint).
    #[must_use]
    pub fn cached_hash(&self) -> u64 {
        self.hash
    }

    /// True iff this subtree has a loose (free) bound variable.
    #[must_use]
    pub fn has_loose_bvars(&self) -> bool {
        self.loose > 0
    }

    /// Decompose an application spine `f a1 a2 ... an` into `(f, [a1..an])`.
    /// `f` is the (non-`App`) head; the args are returned in *application order*.
    /// A non-application returns `(self, [])`.
    #[must_use]
    pub fn unfold_apps(&self) -> (Term, Vec<Term>) {
        let mut args = Vec::new();
        let mut cur = self.clone();
        while let TermKind::App(f, a) = &*cur.kind.clone() {
            #[cfg(test)]
            walk_step();
            args.push(a.clone());
            cur = f.clone();
        }
        args.reverse();
        (cur, args)
    }

    /// Build an application spine: `apply(f, [a1, a2]) = App(App(f, a1), a2)`.
    #[must_use]
    pub fn apply(head: Term, args: &[Term]) -> Term {
        args.iter().fold(head, |f, a| Term::app(f, a.clone()))
    }

    /// Recompute the structural hash from scratch — used by `validate` to verify
    /// the cache is correct (it always is, because `mk` computes it, but the
    /// check is part of the WF invariant the chokepoint establishes).
    #[must_use]
    pub fn recompute_hash(&self) -> u64 {
        crate::term_ops::structural_hash(&self.kind)
    }
}

#[cfg(test)]
thread_local! {
    /// The nodes [`Term::mk`] has built on this thread, for the tests that
    /// bound what a rewrite builds (R176). A test reads it before and after.
    pub(crate) static NODES_BUILT: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
    /// The steps walks over terms have taken on this thread, for the tests
    /// that bound what the nested rewrites look at (R176): one per call of
    /// `Term`'s equality, argument `unfold_apps` takes off, call of the
    /// parameter lowering, and step of the nested rewrites' own walks.
    pub(crate) static WALK_STEPS: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
    /// The node shapes read through [`Term::kind`] on this thread, for the
    /// tests that bound what a walk reads (R176). A test reads it before and
    /// after.
    pub(crate) static KIND_READS: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
}

/// Count one step of a walk over a term on this thread (R176).
#[cfg(test)]
pub(crate) fn walk_step() {
    WALK_STEPS.with(|n| n.set(n.get().saturating_add(1)));
}

/// What `f` returns, and the walk steps it took on this thread (R176).
#[cfg(test)]
pub(crate) fn walk_steps<R>(f: impl FnOnce() -> R) -> (R, u64) {
    let before = WALK_STEPS.with(std::cell::Cell::get);
    let out = f();
    (
        out,
        WALK_STEPS.with(std::cell::Cell::get).saturating_sub(before),
    )
}

#[cfg(test)]
mod tests;

#[cfg(test)]
mod dag_tests;
