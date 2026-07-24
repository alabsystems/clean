// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Kernel-derived **recursor** generation (design §5.2, milestone M2) for a
//! *single, non-mutual, non-nested* inductive — the **top-tier TCB** surface.
//!
//! [`build_recursor`] derives, for an inductive `I`:
//!
//! * the recursor **type** `I.rec` (Lean order
//!   `params -> motive -> minors -> indices -> major -> conclusion`),
//! * the **level signature** (`num_level_params(I) + (1 iff large_elim)`, the
//!   motive universe param leading when large-eliminating), and
//! * the **iota-rules** (one per constructor: how `I.rec .. (C args)` reduces to
//!   `minor_k ..`).
//!
//! `recOn` / `casesOn` are derived from `rec`.
//!
//! Every generated recursor type and minor premise is **kernel-checked** at
//! admission (design §5.2): a wrong motive universe / minor type / index
//! substitution / ι-RHS is a false-*accept*, so the derivation re-runs the
//! kernel's own `infer`/`check` on what it built and rejects on any failure.
//!
//! ## de Bruijn discipline (num_motives = 1, M2)
//!
//! In the rec type body, counting binders from innermost (major = `BVar(0)`):
//! ```text
//!   major   : BVar(0)
//!   indices : BVar(1) .. BVar(num_indices)
//!   minors  : BVar(num_indices+1) .. BVar(num_indices+num_minors)
//!   motive  : BVar(num_indices+num_minors+1)
//!   params  : BVar(num_indices+num_minors+2) ..
//! ```

use crate::budget::Budget;
use crate::inductive::{count_pi, return_type, split_ctor_telescope, AdmitError, InductiveDecl};
use crate::level::Level;
use crate::name::Name;
use crate::recursor_build::build_recursor_type;
use crate::recursor_rules::build_rule_rhs;
use crate::term::{ConstRef, Term, TermKind};
use crate::validate::Env;

/// A single ι-reduction rule for a constructor: when `I.rec` is applied to a
/// major premise that is a saturated application of `constructor`, it reduces by
/// substituting into `rhs`.
///
/// `rhs` is a closed [`Term`] (a λ over `params · motive · minors · fields`) such
/// that, applied positionally to those arguments, it yields the minor premise
/// invoked on the constructor's fields and their recursive IH calls (design §5.2
/// ι-rule). `num_fields` is the constructor's field count; `recursive` flags
/// which of those fields are recursive (carry an IH).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IotaRule {
    /// The constructor this rule fires on.
    pub constructor: Name,
    /// The constructor's field count (after params).
    pub num_fields: u32,
    /// Per-field recursive flag (length == `num_fields`).
    pub recursive: Vec<bool>,
    /// The rule right-hand side, a λ over `params · motive · minors · fields`.
    pub rhs: Term,
    /// The recursor's universe-level param count
    /// (`num_level_params(I) + (1 iff large_elim)`). The `rhs` is built over these
    /// generic level params (`Param(0)…`); the ι-reducer (`whnf::try_iota`)
    /// instantiates them with the firing head's concrete levels before applying,
    /// so a recursive minor's embedded IH sub-recursor lands at the concrete
    /// levels rather than the generic params. Used as an arity check there.
    pub rec_num_levels: usize,
}

/// The kernel-derived recursor record stored in the env.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RecursorData {
    /// `I.rec`.
    pub name: Name,
    /// The inductive `I`.
    pub inductive: Name,
    /// The recursor's universe-level param count = `num_level_params(I) + (1 iff
    /// large_elim)`. The motive universe is the **leading** param when present.
    pub num_level_params: u32,
    /// Whether the inductive large-eliminates (motive into `Sort u`, `u > 0`).
    pub large_elim: bool,
    /// `num_params`.
    pub num_params: u32,
    /// `num_indices` (of the target type this recursor eliminates).
    pub num_indices: u32,
    /// Number of motives: 1 for a single inductive, `N` for an `N`-type mutual
    /// block. The recursor's argument order is
    /// `params · motives · minors · indices · major`.
    pub num_motives: u32,
    /// Total number of minor premises across the whole block (= `rules.len()`
    /// for a single inductive; the block-wide constructor count for a mutual
    /// recursor, which fires only on its own type's constructors but binds every
    /// block minor).
    pub num_minors_total: u32,
    /// The kernel-checked recursor type.
    pub type_: Term,
    /// The ι-rules — for the constructors this recursor fires on (its own type's
    /// constructors). The RHS still expects all block motives + minors.
    pub rules: Vec<IotaRule>,
}

/// Derive + kernel-check the recursor for a single non-mutual inductive.
pub(crate) fn build_recursor(
    env: &dyn Env,
    decl: &InductiveDecl,
    large_elim: bool,
) -> Result<RecursorData, AdmitError> {
    let derr = |detail: String| AdmitError::Derivation {
        ind: decl.name.clone(),
        detail,
    };

    let num_params = decl.num_params;
    let type_arity = count_pi(&decl.type_);
    let num_indices = type_arity.saturating_sub(num_params);
    let num_minors = u32::try_from(decl.constructors.len())
        .map_err(|_| derr("too many constructors".to_string()))?;

    // Level signature: motive universe param is index 0 when large-eliminating,
    // and the inductive's own params follow (shifted by 1). When Prop-only, the
    // motive targets Sort 0 and there is no extra level param.
    let (rec_num_levels, motive_univ, ind_level_subst) = if large_elim {
        let motive_lvl = Level::param(0);
        // The inductive's own params, as seen inside the recursor's telescope,
        // are shifted up by one (the motive level occupies index 0).
        let ind_subst: Vec<Level> = (0..decl.num_level_params)
            .map(|i| Level::param(i.saturating_add(1)))
            .collect();
        (
            decl.num_level_params.saturating_add(1),
            motive_lvl,
            ind_subst,
        )
    } else {
        let ind_subst: Vec<Level> = (0..decl.num_level_params).map(Level::param).collect();
        (decl.num_level_params, Level::zero(), ind_subst)
    };

    // Per-constructor field analysis. Field types and return-index expressions
    // are pulled from the constructor's declared type, which is written over the
    // inductive's own universe params; **level-shift** them by `ind_level_subst`
    // so they live in the recursor's level telescope (identity when small-elim).
    let mut ctor_infos: Vec<CtorInfo> = Vec::with_capacity(decl.constructors.len());
    for ctor in &decl.constructors {
        let (field_tys, ret) = split_ctor_telescope(&ctor.type_, num_params);
        let recursive: Vec<bool> = field_tys
            .iter()
            .map(|f| is_recursive_field(&decl.name, f))
            .collect();
        let field_tys: Vec<Term> = field_tys
            .into_iter()
            .map(|t| t.instantiate_levels(&ind_level_subst))
            .collect();
        let (_h, ret_args) = ret.unfold_apps();
        let np = usize::try_from(num_params).unwrap_or(usize::MAX);
        let return_indices: Vec<Term> = ret_args
            .into_iter()
            .skip(np)
            .map(|t| t.instantiate_levels(&ind_level_subst))
            .collect();
        ctor_infos.push(CtorInfo {
            name: ctor.name.clone(),
            num_fields: u32::try_from(field_tys.len())
                .map_err(|_| derr("too many fields".to_string()))?,
            field_tys,
            recursive,
            return_indices,
        });
    }

    let rec_name = Name::from_dotted(&format!("{}.rec", decl.name));

    // Build the recursor type.
    let rec_ty = build_recursor_type(
        decl,
        &rec_name,
        num_indices,
        &motive_univ,
        &ind_level_subst,
        &ctor_infos,
    )
    .map_err(&derr)?;

    // Build ι-rules.
    let mut rules = Vec::with_capacity(ctor_infos.len());
    for (idx, ci) in ctor_infos.iter().enumerate() {
        let rhs = build_rule_rhs(
            decl,
            &rec_name,
            rec_num_levels,
            num_indices,
            num_minors,
            idx,
            ci,
            &ind_level_subst,
        )
        .map_err(&derr)?;
        rules.push(IotaRule {
            constructor: ci.name.clone(),
            num_fields: ci.num_fields,
            recursive: ci.recursive.clone(),
            rhs,
            rec_num_levels: usize::try_from(rec_num_levels).unwrap_or(usize::MAX),
        });
    }

    let recursor = RecursorData {
        name: rec_name,
        inductive: decl.name.clone(),
        num_level_params: rec_num_levels,
        large_elim,
        num_params,
        num_indices,
        num_motives: 1,
        num_minors_total: num_minors,
        type_: rec_ty,
        rules,
    };

    // Kernel-check the generated recursor type (design §5.2: not debug-only).
    kernel_check_recursor(env, decl, &recursor)?;

    Ok(recursor)
}

/// Per-constructor info gathered once.
pub(crate) struct CtorInfo {
    pub(crate) name: Name,
    pub(crate) num_fields: u32,
    pub(crate) field_tys: Vec<Term>,
    pub(crate) recursive: Vec<bool>,
    pub(crate) return_indices: Vec<Term>,
}

/// A field is recursive iff its return-type head (after stripping its own Pi
/// binders) is the inductive applied directly. Nested occurrences were already
/// rejected by `add_inductive`'s scope guard.
fn is_recursive_field(ind: &Name, field_ty: &Term) -> bool {
    let ret = return_type(field_ty);
    let (head, _args) = ret.unfold_apps();
    matches!(head.kind(), TermKind::Const(c) if c.name() == ind)
}

/// `I @ levels p_0 .. p_{np-1} i_0 .. i_{ni-1}` where each `p`/`i` is the BVar
/// given by the offset closures. Used to build major-premise / motive-domain
/// applications at the right binder depths.
pub(crate) fn ind_app(
    ind: &Name,
    levels: &[Level],
    num_params: u32,
    num_indices: u32,
    param_bvar: impl Fn(u32) -> u32,
    index_bvar: impl Fn(u32) -> u32,
) -> Result<Term, String> {
    let cref = ConstRef::mk_unchecked_levels(ind.clone(), levels.to_vec());
    let mut app = Term::const_ref(cref);
    for p in 0..num_params {
        app = Term::app(app, Term::bvar(param_bvar(p)));
    }
    for i in 0..num_indices {
        app = Term::app(app, Term::bvar(index_bvar(i)));
    }
    Ok(app)
}

// ---------------------------------------------------------------------------
// Kernel-check of the generated recursor.
// ---------------------------------------------------------------------------

/// Kernel-check the generated recursor type (design §5.2): the whole `I.rec`
/// type must `infer_sort` cleanly (i.e. be a well-formed type) under the
/// recursor's level params. This re-runs the kernel's own typing on what the
/// derivation built, so a wrong motive universe / minor type / index
/// substitution surfaces as a *reject*, not a silent false-accept.
fn kernel_check_recursor(
    env: &dyn Env,
    decl: &InductiveDecl,
    rec: &RecursorData,
) -> Result<(), AdmitError> {
    let derr = |detail: String| AdmitError::Derivation {
        ind: decl.name.clone(),
        detail,
    };
    let mut budget = Budget::default_budget();
    // The recursor type is closed over `rec.num_level_params` universe params.
    // infer_sort over the empty local context with that level arity.
    crate::infer::infer_sort_in_context(env, &[], &rec.type_, &mut budget)
        .map_err(|e| derr(format!("generated recursor type failed kernel check: {e}")))?;
    Ok(())
}
