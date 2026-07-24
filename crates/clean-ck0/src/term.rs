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
use crate::level::Level;
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
    pub(crate) fn instantiate_levels(&self, subst: &[Level]) -> ConstRef {
        ConstRef {
            name: self.name.clone(),
            levels: self
                .levels
                .iter()
                .map(|l| l.instantiate_params(subst))
                .collect(),
        }
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
        let mut derived: Vec<Level> =
            Vec::with_capacity(expected_usize.saturating_add(usize::from(large_elim)));
        if large_elim {
            derived.push(motive_level);
        }
        derived.extend(ind_levels);
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
    pub(crate) fn instantiate_levels(&self, subst: &[Level]) -> ElimRef {
        ElimRef {
            inductive: self.inductive.clone(),
            derived_levels: self
                .derived_levels
                .iter()
                .map(|l| l.instantiate_params(subst))
                .collect(),
        }
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
    /// `true` iff the subtree contains a loose (free) de Bruijn variable.
    /// Cached so `validate` can check closedness in O(1) per node.
    pub(crate) has_loose: bool,
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
        let hash = crate::term_ops::structural_hash(&kind);
        let has_loose = crate::term_ops::compute_has_loose(&kind);
        Term {
            kind: Arc::new(kind),
            hash,
            has_loose,
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
        self.has_loose
    }

    /// Decompose an application spine `f a1 a2 ... an` into `(f, [a1..an])`.
    /// `f` is the (non-`App`) head; the args are returned in *application order*.
    /// A non-application returns `(self, [])`.
    #[must_use]
    pub fn unfold_apps(&self) -> (Term, Vec<Term>) {
        let mut args = Vec::new();
        let mut cur = self.clone();
        while let TermKind::App(f, a) = &*cur.kind.clone() {
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
mod tests {
    use super::*;
    use crate::minimal_env::MinimalEnv;
    use crate::validate::Env;

    #[test]
    fn test_structural_equality_with_matching_hash() {
        // Two independently built identical terms are == (and share a hash).
        let a = Term::app(Term::bvar(0), Term::sort(Level::zero()));
        let b = Term::app(Term::bvar(0), Term::sort(Level::zero()));
        assert_eq!(a, b);
        assert_eq!(a.cached_hash(), b.cached_hash());
    }

    #[test]
    fn test_different_terms_differ() {
        let a = Term::bvar(0);
        let b = Term::bvar(1);
        assert_ne!(a, b);
    }

    #[test]
    fn test_cached_hash_equals_recompute() {
        let t = Term::lam(
            BinderInfo::Default,
            Term::sort(Level::zero()),
            Term::app(Term::bvar(0), Term::bvar(0)),
        );
        assert_eq!(t.cached_hash(), t.recompute_hash());
    }

    #[test]
    fn test_has_loose_tracks_binders() {
        // lambda over BVar(0) is closed; BVar(0) alone is loose.
        let closed = Term::lam(
            BinderInfo::Default,
            Term::sort(Level::zero()),
            Term::bvar(0),
        );
        assert!(!closed.has_loose_bvars());
        let loose = Term::bvar(0);
        assert!(loose.has_loose_bvars());
    }

    #[test]
    fn test_constref_levels_match_env_arity() {
        let env: MinimalEnv = MinimalEnv::new().with_const(Name::from_dotted("Id"), 1);
        assert_eq!(env.num_level_params(&Name::from_dotted("Id")), Some(1));
        let c = ConstRef::mk(&env, Name::from_dotted("Id"), vec![Level::param(0)]).expect("ok");
        assert_eq!(c.levels().len(), 1);
    }
}
