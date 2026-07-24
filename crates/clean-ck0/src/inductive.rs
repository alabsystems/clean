// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Inductive **admission** (design §2, §5.2, milestone M2): the single total
//! [`add_inductive`] entry point that admits a *single, non-mutual,
//! non-nested* inductive and derives its recursor.
//!
//! `add_inductive` runs, in order (design §5.2):
//!
//! 1. **structural-identity conflict check** — re-adding a structurally-identical
//!    inductive is idempotent-OK; the same name with any different type/ctor is
//!    [`AdmitError::Conflict`]. There is **no** `_unchecked` variant.
//! 2. **strict positivity** — iterative (explicit work stack, stack-safe past
//!    20k nesting depth), fail-closed; rejects negative / non-strictly-positive
//!    occurrences (e.g. `Bad : (Bad -> Bad) -> Bad`).
//! 3. **universe constraint** — every constructor field's sort `<=` the
//!    inductive's sort ([`Level::is_geq`] on canonical levels), fail-closed.
//! 4. **subsingleton / large-elim determination** — the soundness-critical §2
//!    gate, transcribed from Lean's `elim_only_at_universe_zero`.
//! 5. **`build_recursor`** — derives the recursor type, level signature, and
//!    ι-rules; every generated recursor type and minor premise is **kernel-
//!    checked** (design §5.2 "not validated as debug-only metadata").
//!
//! **Mutual + nested inductives are M3 (out of scope here)** and are rejected
//! with [`AdmitError::Unsupported`] — never a fake/weak recursor.

use crate::budget::Budget;
use crate::infer::InferError;
use crate::level::Level;
use crate::name::Name;
use crate::positivity::{check_positivity_ctor, term_mentions};
use crate::rawexpr::BinderInfo;
use crate::recursor::{build_recursor, RecursorData};
use crate::staging_env::StagingEnv;
use crate::term::{Term, TermKind};
use crate::validate::Env;

/// A constructor of an inductive being admitted. The `type_` is a closed
/// [`Term`] over the inductive's level params, validated *before* admission (its
/// telescope is `(params...) (fields...) -> I params indices`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Constructor {
    /// The fully-qualified constructor name (e.g. `Nat.succ`).
    pub name: Name,
    /// The constructor's declared type.
    pub type_: Term,
}

/// A single (non-mutual) inductive declaration submitted for admission.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct InductiveDecl {
    /// The inductive's name (e.g. `Nat`).
    pub name: Name,
    /// Number of universe level params.
    pub num_level_params: u32,
    /// Number of leading parameters (shared across constructors, not eliminated).
    pub num_params: u32,
    /// The inductive's type: `(params...) (indices...) -> Sort u`.
    pub type_: Term,
    /// The constructors, in declaration order.
    pub constructors: Vec<Constructor>,
}

/// Errors from inductive admission. Every variant is a *reject*; there is no
/// fail-open (design §4.3).
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[non_exhaustive]
pub enum AdmitError {
    /// An inductive with this name already exists but is not structurally
    /// identical (different type or constructors). Re-adding an identical one is
    /// idempotent-OK; any difference is a hard conflict (design §5.2 #1).
    #[error(
        "inductive '{name}': conflicting redeclaration (name exists with a different type/ctors)"
    )]
    Conflict {
        /// The conflicting inductive name.
        name: Name,
    },
    /// A constructor argument is not strictly positive in the inductive being
    /// defined (negative / non-strictly-positive occurrence). Fail-closed
    /// (design §5.2 #2).
    #[error(
        "inductive '{ind}': non-strictly-positive occurrence of '{ind}' in constructor '{ctor}'"
    )]
    NonPositive {
        /// The inductive being defined.
        ind: Name,
        /// The offending constructor.
        ctor: Name,
    },
    /// A constructor field's sort exceeds the inductive's sort (universe
    /// constraint violation). Fail-closed (design §5.2 #3).
    #[error("inductive '{ind}': constructor '{ctor}' field sort exceeds the inductive's sort")]
    UniverseTooLarge {
        /// The inductive being defined.
        ind: Name,
        /// The offending constructor.
        ctor: Name,
    },
    /// The declared `num_params` is structurally inconsistent with the
    /// inductive's own type and/or its constructors' shapes: either it exceeds
    /// the inductive type's Pi arity, or some constructor does not have
    /// `num_params` leading binders, or a constructor's result type is not `I`
    /// applied to exactly those leading binders as bare, in-order de Bruijn
    /// variables (the "parameters are uniform" check Lean's kernel enforces).
    ///
    /// This is checked **before** the subsingleton / large-elim gate so that an
    /// over-declared `num_params` cannot hide a non-`Prop` data field from the
    /// bare-index analysis (design §2, §12): the malformed-params shape is made
    /// *unrepresentable at the gate*, not merely caught downstream by the
    /// recursor kernel-check. Fail-closed.
    #[error("inductive '{ind}': malformed num_params ({detail})")]
    MalformedParams {
        /// The inductive being defined.
        ind: Name,
        /// What is structurally inconsistent.
        detail: String,
    },
    /// A generated recursor type, minor premise, or the inductive/ctor types
    /// failed kernel checking, or a structural precondition (telescope shape)
    /// was violated. Fail-closed.
    #[error("inductive '{ind}': recursor derivation failed: {detail}")]
    Derivation {
        /// The inductive being defined.
        ind: Name,
        /// What failed.
        detail: String,
    },
    /// Mutual or nested inductives are unsupported at M2 (they are M3). Rejected
    /// with a clear error rather than a fake/weak recursor (design: M2 scope).
    #[error("inductive '{name}': {what} is unsupported at M2 (mutual/nested are M3)")]
    Unsupported {
        /// The inductive name.
        name: Name,
        /// Which unsupported feature was detected.
        what: String,
    },
    /// A soundness check could not complete within the pinned budget. Exhaustion
    /// collapses to *reject* (design §5.1: rejection checks never fail open).
    #[error("inductive '{ind}': out of budget during admission")]
    OutOfBudget {
        /// The inductive being defined.
        ind: Name,
    },
}

/// The mutable environment surface inductive admission writes into. The decision
/// core (`whnf`/`infer`/`def_eq`) only ever *reads* the env; admission is the one
/// place that extends it, and it does so through this trait so the storage layer
/// (the `MinimalEnv` in `validate`, or a richer host env) stays decoupled from
/// the derivation logic.
///
/// There is intentionally **no** `_unchecked` admission path on this trait
/// (design §4.3): the only way to register an inductive + recursor is
/// [`add_inductive`], which always derives and kernel-checks.
pub trait MutableEnv: Env {
    /// True iff an inductive with this name is already registered (used by the
    /// structural-identity conflict check).
    fn has_inductive(&self, name: &Name) -> bool;

    /// The stored decl + recursor for an already-admitted inductive, for the
    /// idempotency / conflict comparison.
    fn admitted(&self, name: &Name) -> Option<AdmittedInductive>;

    /// Commit a fully-derived, kernel-checked inductive (its decl, its derived
    /// recursors, its constructors and ι-rules) into the env atomically. Called
    /// only by [`add_inductive`] after every check has passed.
    fn commit_inductive(&mut self, admitted: AdmittedInductive);

    /// The stored [`InductiveDecl`] for an already-admitted type, whether it was
    /// admitted singly or as part of a mutual block. Used by the mutual
    /// admission's structural-identity conflict check. Default: derive from the
    /// single-inductive [`MutableEnv::admitted`] record.
    fn admitted_mutual_decl(&self, name: &Name) -> Option<InductiveDecl> {
        self.admitted(name).map(|a| a.decl)
    }
}

/// The full record of an admitted inductive: everything the env stores so the
/// decision core can read it back (types, large-elim flag, derived recursors,
/// ι-rules). Compared structurally for the idempotency / conflict check.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AdmittedInductive {
    /// The original declaration.
    pub decl: InductiveDecl,
    /// Whether the inductive large-eliminates (design §2 subsingleton gate).
    pub large_elim: bool,
    /// The kernel-derived recursor (`I.rec`).
    pub recursor: RecursorData,
}

/// Admit a single non-mutual, non-nested inductive into `env`, deriving and
/// kernel-checking its recursor. **One total function** (design §5.2). Returns
/// `Ok(())` on success (including idempotent re-admission of a structurally
/// identical inductive); every failure is a `Rejected` [`AdmitError`].
pub fn add_inductive(env: &mut dyn MutableEnv, decl: InductiveDecl) -> Result<(), AdmitError> {
    // M2 scope guard: reject anything that smells mutual/nested up front so we
    // never derive a fake recursor for an out-of-scope shape.
    reject_out_of_scope(&decl)?;

    // (1) structural-identity conflict check (idempotency).
    if env.has_inductive(&decl.name) {
        match env.admitted(&decl.name) {
            Some(prev) if prev.decl == decl => return Ok(()), // idempotent re-add
            _ => {
                return Err(AdmitError::Conflict {
                    name: decl.name.clone(),
                })
            }
        }
    }

    // (1b) structural num_params validation (fail-closed). Done BEFORE the
    // subsingleton gate and the universe constraint so an over-declared
    // num_params cannot drop a genuine non-Prop data field out of the
    // bare-index analysis (design §2, §12). This closes the gate-level
    // false-ACCEPT at the gate itself rather than relying on the separately
    // implemented recursor kernel-check to reject the resulting recursor.
    crate::inductive_params::validate_num_params(&decl)?;

    // (2) strict positivity (iterative, stack-safe, fail-closed).
    for ctor in &decl.constructors {
        check_positivity_ctor(&*env, &decl.name, &ctor.type_).map_err(|()| {
            AdmitError::NonPositive {
                ind: decl.name.clone(),
                ctor: ctor.name.clone(),
            }
        })?;
    }

    // The staging env knows the inductive type former + its constructors (which
    // are not yet committed), so every check that needs to resolve `I` or `I`'s
    // constructors (field-sort inference, the large-elim gate, the recursor
    // kernel-check) can do so before the recursor exists.
    let staging = StagingEnv::new(env, &decl);

    // (3) universe constraint (is_geq on canonical levels, fail-closed).
    let ind_sort = inductive_result_level(&decl).ok_or_else(|| AdmitError::Derivation {
        ind: decl.name.clone(),
        detail: "inductive result type is not a Sort".to_string(),
    })?;
    check_universe_constraint(&staging, &decl, &ind_sort)?;

    // (4) subsingleton / large-elim determination (THE soundness gate, §2).
    let large_elim = crate::elim_analysis::large_eliminates(&staging, &decl, &ind_sort);

    // (5) build + kernel-check the recursor (type, level sig, ι-rules) against
    // the same staging env (the kernel-check needs `I` and the constructors).
    let recursor = build_recursor(&staging, &decl, large_elim)?;
    drop(staging);

    env.commit_inductive(AdmittedInductive {
        decl,
        large_elim,
        recursor,
    });
    Ok(())
}

/// Reject mutual / nested inductives (M3). A submission is detected as
/// out-of-scope if a constructor field's *domain* mentions the inductive under a
/// type former other than the inductive applied directly (a nested occurrence
/// such as `List I`), since M2 derives no auxiliary mutual construction for it.
fn reject_out_of_scope(decl: &InductiveDecl) -> Result<(), AdmitError> {
    for ctor in &decl.constructors {
        let (fields, _ret) = split_ctor_telescope(&ctor.type_, decl.num_params);
        for field_ty in &fields {
            if field_mentions_nested(&decl.name, field_ty) {
                return Err(AdmitError::Unsupported {
                    name: decl.name.clone(),
                    what: format!(
                        "nested occurrence of '{}' in constructor '{}'",
                        decl.name, ctor.name
                    ),
                });
            }
        }
    }
    Ok(())
}

/// A field whose *return-type head* (after stripping its own Pi binders) is the
/// inductive applied directly is an OK recursive field. A field that mentions the
/// inductive only as a strict *argument* of some other head (e.g. `List I`,
/// `Pair I I`) is a nested occurrence: unsupported at M2.
fn field_mentions_nested(ind: &Name, field_ty: &Term) -> bool {
    // Strip the field's own leading Pi binders to reach its return type.
    let mut cur = field_ty.clone();
    while let TermKind::Pi(_, _, body) = cur.kind() {
        cur = body.clone();
    }
    let (head, args) = cur.unfold_apps();
    let head_is_ind = matches!(head.kind(), TermKind::Const(c) if c.name() == ind);
    if head_is_ind {
        // Recursive field: I applied to params/indices. The args themselves must
        // not mention I (that would be a nested occurrence inside an index).
        return args.iter().any(|a| term_mentions(a, ind));
    }
    // Head is not I: a nested occurrence iff I appears anywhere inside.
    term_mentions(&cur, ind)
}

// ---------------------------------------------------------------------------
// Universe constraint.
// ---------------------------------------------------------------------------

/// The inductive's result-sort level: strip its Pi telescope to the `Sort u`.
pub(crate) fn inductive_result_level(decl: &InductiveDecl) -> Option<Level> {
    let mut cur = decl.type_.clone();
    while let TermKind::Pi(_, _, body) = cur.kind() {
        cur = body.clone();
    }
    match cur.kind() {
        TermKind::Sort(l) => Some(l.clone()),
        _ => None,
    }
}

/// Every constructor field's sort must be `<=` the inductive's sort
/// (`ind_sort >= field_sort`), with the standard Prop exception: a `Prop`
/// inductive (`ind_sort = 0`) admits fields of any sort (Lean impredicativity).
/// Fail-closed: budget exhaustion or a non-sort field type is a reject.
/// Block-aware universe constraint: each type's constructor fields are checked
/// against *that type's* sort. (The field-sort inference resolves block types
/// through the staging env, so cross-type field references type cleanly.) For a
/// single-element block this is exactly [`check_universe_constraint`].
pub(crate) fn check_universe_constraint_block(
    env: &dyn Env,
    decl: &InductiveDecl,
    ind_sort: &Level,
) -> Result<(), AdmitError> {
    check_universe_constraint(env, decl, ind_sort)
}

fn check_universe_constraint(
    env: &dyn Env,
    decl: &InductiveDecl,
    ind_sort: &Level,
) -> Result<(), AdmitError> {
    // Prop is impredicative: a Prop-valued inductive may quantify over fields in
    // any universe (Lean kernel: the level-le check is skipped when the inductive
    // is in Prop).
    if ind_sort.is_zero() {
        return Ok(());
    }
    let mut budget = Budget::default_budget();
    for ctor in &decl.constructors {
        let (field_tys, _ret) = split_ctor_telescope(&ctor.type_, decl.num_params);
        // Field domains are typed under a context of [params..., earlier fields].
        // We type each field's sort in the running context.
        let mut ctx: Vec<Term> = Vec::new();
        // Push parameter binder types (the leading Pi domains of the ctor type).
        let param_binders = pi_domains(&ctor.type_, decl.num_params);
        for d in &param_binders {
            ctx.push(d.clone());
        }
        for field_ty in &field_tys {
            let sort =
                infer_sort_in_ctx(env, &ctx, field_ty, &mut budget).map_err(|e| match e {
                    InferError::OutOfBudget => AdmitError::OutOfBudget {
                        ind: decl.name.clone(),
                    },
                    _ => AdmitError::UniverseTooLarge {
                        ind: decl.name.clone(),
                        ctor: ctor.name.clone(),
                    },
                })?;
            if !Level::is_geq(ind_sort, &sort) {
                return Err(AdmitError::UniverseTooLarge {
                    ind: decl.name.clone(),
                    ctor: ctor.name.clone(),
                });
            }
            ctx.push(field_ty.clone());
        }
    }
    Ok(())
}

/// Infer the sort of `ty` under a local context — thin wrapper over `infer`'s
/// context-aware path (added in M2).
fn infer_sort_in_ctx(
    env: &dyn Env,
    ctx: &[Term],
    ty: &Term,
    budget: &mut Budget,
) -> Result<Level, InferError> {
    crate::infer::infer_sort_in_context(env, ctx, ty, budget)
}

// ---------------------------------------------------------------------------
// Telescope helpers shared with the recursor builder.
// ---------------------------------------------------------------------------

/// Split a constructor type `(p_0..p_{np-1}) (f_0..f_{m-1}) -> Ret` into its
/// field domain types `[f_0, .., f_{m-1}]` (after skipping `num_params` leading
/// params) and the return type `Ret`.
/// Decide whether a single-constructor inductive is a genuine **η-structure**:
/// one for which `mk (proj_0 t) … (proj_{n-1} t) ≡ t` for every `t : I` — the
/// exact soundness side-condition that licenses structure-η (in `def_eq` and in
/// the recursor ι-rule). Lean enables structure-η only for such types.
///
/// The gate (ALL must hold; fail-closed — any doubt returns `false`):
/// 1. **exactly one constructor** (caller already filters, re-checked here);
/// 2. **no indices** (`num_indices == 0`): an indexed family (e.g. `Eq`) is NOT
///    a structure — its constructor's result type pins indices that projections
///    cannot recover, so `mk (proj t) ≢ t`;
/// 3. **non-recursive**: no constructor field mentions any name in `family`
///    (the inductive itself, or any block member for a mutual). A recursive
///    field is not projectable in the η sense and would also risk a non-
///    terminating expansion.
///
/// Returns `true` only when structure-η is definitionally valid for `I`.
pub(crate) fn is_eta_structure(
    ctor_ty: &Term,
    num_params: u32,
    num_indices: u32,
    num_ctors: usize,
    family: &[Name],
) -> bool {
    if num_ctors != 1 {
        return false;
    }
    if num_indices != 0 {
        return false;
    }
    // Non-recursive: no field's type may mention any family member. We strip the
    // params from the constructor telescope and inspect each field domain (and
    // its own nested binders, which `term_mentions` traverses in full).
    let (fields, _ret) = split_ctor_telescope(ctor_ty, num_params);
    for field_ty in &fields {
        if family.iter().any(|n| term_mentions(field_ty, n)) {
            return false;
        }
    }
    true
}

pub(crate) fn split_ctor_telescope(ctor_ty: &Term, num_params: u32) -> (Vec<Term>, Term) {
    let mut fields = Vec::new();
    let mut cur = ctor_ty.clone();
    let mut seen: u32 = 0;
    let np = num_params;
    while let TermKind::Pi(_, dom, codom) = cur.kind() {
        if seen >= np {
            fields.push(dom.clone());
        }
        seen = seen.saturating_add(1);
        cur = codom.clone();
    }
    (fields, cur)
}

/// Collect the first `count` Pi domain types of `ty` (with their binder info).
pub(crate) fn pi_domains_with_info(ty: &Term, count: u32) -> Vec<(BinderInfo, Term)> {
    let mut out = Vec::new();
    let mut cur = ty.clone();
    let mut got: u32 = 0;
    while got < count {
        match cur.kind() {
            TermKind::Pi(bi, dom, codom) => {
                out.push((*bi, dom.clone()));
                cur = codom.clone();
                got = got.saturating_add(1);
            }
            _ => break,
        }
    }
    out
}

/// Collect the first `count` Pi domain types of `ty`.
fn pi_domains(ty: &Term, count: u32) -> Vec<Term> {
    pi_domains_with_info(ty, count)
        .into_iter()
        .map(|(_, t)| t)
        .collect()
}

/// Count the leading Pi binders of `t`.
pub(crate) fn count_pi(t: &Term) -> u32 {
    let mut cur = t.clone();
    let mut n: u32 = 0;
    while let TermKind::Pi(_, _, codom) = cur.kind() {
        n = n.saturating_add(1);
        cur = codom.clone();
    }
    n
}

/// The return type of `t` after stripping all leading Pi binders.
pub(crate) fn return_type(t: &Term) -> Term {
    let mut cur = t.clone();
    while let TermKind::Pi(_, _, codom) = cur.kind() {
        cur = codom.clone();
    }
    cur
}
