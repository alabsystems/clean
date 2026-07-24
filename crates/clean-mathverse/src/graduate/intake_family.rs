// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! v3 carried inductive families — the intake-side `add_inductive` re-check.
//!
//! A "value-less carrier" (`Rat.Raw`, `NNVerify.IntervalBounds`,
//! `AddCommGroup`, …) is an inductive-family member registered with
//! `ConstantInfo { value: None }`; its real kernel certificate lives in the
//! environment side tables (`get_inductive` / `get_constructor` /
//! `get_recursor`) and is re-earned here by replaying the reconstructed
//! [`InductiveDecl`] through the kernel's full checked
//! [`Environment::add_inductive`] path (positivity, nested positivity,
//! universe constraints, recursor generation) in the gate's fresh recheck
//! environment. See `designs/2026-06-11-graduation-v3-valueless-carriers.md`
//! option (a).
//!
//! Fail-closed properties:
//! - **v3.0 fence:** single-type, non-nested, non-mutual families only
//!   (`all_names.len() == 1 && !is_nested`); everything else rejects with
//!   `carried-inductive-unsupported`.
//! - **Member cross-check (surface a6):** every value-less family member the
//!   source environment knows must match (level params + type, up to
//!   kernel-meaningless `BinderInfo` annotations — see
//!   [`exprs_equal_ignoring_binder_info`]) the constant `add_inductive`
//!   regenerated — the same discipline the cake gate's replay applies to
//!   shard bytes, so the two reconstructions cannot silently diverge.
//! - **Union closure (surface a4):** the family's honest axiom-closure
//!   contribution is the union over ALL member types (inductive type + every
//!   constructor type); a poisoned constructor rejects the whole family even
//!   if no accepted theorem ever references that constructor.
//! - **Failure cascades:** a failed family is cached (`failed_families`) and
//!   every later dependent fails with the same audited reason.

use std::collections::HashSet;

use clean_kernel::{Environment, Expr, Name};

use super::intake::{collect_constant_refs, resolve_dependency, GateState};
use super::record::{
    expr_canonical_digest, AxiomClosure, CarriedInductive, CarriedInductiveConstructor,
    KernelFacts, KernelVerdict,
};

/// State of one carried inductive family (the family analog of
/// `CarriedDefState`).
pub(super) struct CarriedFamilyState {
    /// Record entry; `members_in_shard` stays empty until shard write time
    /// (only then is the referenced-recursor set known).
    pub(super) entry: CarriedInductive,
    /// Family-root (inductive type) name.
    pub(super) root: String,
    /// Constructor names, declaration order.
    pub(super) ctor_names: Vec<String>,
    /// Generated recursor-kind members present in the recheck environment
    /// (`rec` / `casesOn` / `recOn`) — shard-write candidates when the
    /// accepted content references them.
    pub(super) recursor_names: Vec<String>,
    /// Every constant name this family's `add_inductive` added to the
    /// recheck environment (maps member references back to the family).
    pub(super) member_names: Vec<String>,
    /// Sorted external (non-member) constant refs of the family — the union
    /// of the inductive type's and every constructor type's references.
    pub(super) refs: Vec<String>,
}

/// Structural expression equality that tolerates exactly one divergence:
/// the `BinderInfo` annotation (default / implicit / strict-implicit /
/// instance) on `Lam`/`Pi` binders.
///
/// Why this tolerance is needed: the `.olean` direct importer does not
/// faithfully preserve binder annotations — Lean-implicit binders arrive as
/// `BinderInfo::Default` on every imported constant (verified by direct
/// dump: `id`, `PProd.mk`, `PProd.rec` from `Init.Prelude` all carry
/// `Default` where Lean has `{...}`), while the kernel's `add_inductive`
/// regenerates recursor types with its own annotations. The two
/// reconstructions of a Lean-core recursor type are therefore byte-identical
/// EXCEPT for binder info.
///
/// Why it is sound: binder info is elaborator metadata with zero kernel
/// meaning — `TypeChecker::is_def_eq_binding` discards it (`Lam(_, ty,
/// body)`) and no type-checking path consults it. The regenerated member is
/// the trusted object (it just came out of the checked `add_inductive`
/// replay, and it — not the source constant — is what dependents are
/// re-typechecked against); this comparison only establishes that the
/// source environment's metadata denotes the same kernel object.
///
/// Everything else must match exactly: de Bruijn structure, constants,
/// literals, universe levels, projections, let-binder names, `nonDep`
/// hints, and the QTT multiplicity carried alongside the binder info
/// (stricter than strictly necessary — fail closed).
pub(super) fn exprs_equal_ignoring_binder_info(
    a: &clean_kernel::Expr,
    b: &clean_kernel::Expr,
) -> bool {
    use clean_kernel::expr::ExprKind;
    let mut stack: Vec<(&clean_kernel::Expr, &clean_kernel::Expr)> = vec![(a, b)];
    while let Some((a, b)) = stack.pop() {
        match (a.kind(), b.kind()) {
            (ExprKind::App(f1, a1), ExprKind::App(f2, a2)) => {
                stack.push((f1, f2));
                stack.push((a1, a2));
            }
            // `BinderData::info` is deliberately not compared; the QTT
            // multiplicity still is.
            (ExprKind::Lam(d1, t1, b1), ExprKind::Lam(d2, t2, b2))
            | (ExprKind::Pi(d1, t1, b1), ExprKind::Pi(d2, t2, b2)) => {
                if d1.mult != d2.mult {
                    return false;
                }
                stack.push((t1, t2));
                stack.push((b1, b2));
            }
            (ExprKind::Let(n1, t1, v1, b1, nd1), ExprKind::Let(n2, t2, v2, b2, nd2)) => {
                if n1 != n2 || nd1 != nd2 {
                    return false;
                }
                stack.push((t1, t2));
                stack.push((v1, v2));
                stack.push((b1, b2));
            }
            (ExprKind::Proj(n1, i1, e1), ExprKind::Proj(n2, i2, e2)) => {
                if n1 != n2 || i1 != i2 {
                    return false;
                }
                stack.push((e1, e2));
            }
            // Every other variant (BVar, FVar, Sort, Const, Lit, mode
            // extensions, ...) carries no binder info: exact equality.
            (ka, kb) => {
                if ka != kb {
                    return false;
                }
            }
        }
    }
    true
}

/// Lean-kernel-parity annotation erasure for a carried family's Pi
/// telescopes (the inductive type's and every constructor's).
///
/// Lean's kernel routes every binder domain its inductive machinery touches
/// through `Expr.consumeTypeAnnotations` (`optParam` / `autoParam` /
/// `outParam` / `semiOutParam` unwrap to their underlying type), so the
/// objects it GENERATES are annotation-free even when the stored
/// constructor type carries the elaborator gadget. The gadgets are
/// definitionally transparent (`autoParam P tac` delta-unfolds to `P`) —
/// kernel-meaningless metadata of the same grade as `BinderInfo`.
///
/// Why the gate must erase them on carry: mathlib typeclass constructors
/// embed tactic-default payloads (`AddMonoid.nsmul_succ._autoParam :
/// Lean.Syntax := <syntax tree>`) inside `autoParam` annotations. Replaying
/// an annotated constructor would force the recheck environment to carry
/// `autoParam`, the payload definition, and the entire (nested, out-of-fence)
/// `Lean.Syntax` family — none of which participates in the family's kernel
/// certificate. Erasing the annotation at carry time keeps the replayed
/// object the kernel-semantic one, exactly as Lean's own recursor generation
/// does. Only the HEAD of each binder domain is consumed (mirroring
/// `mk_local_decl_for`); the body of the telescope is walked recursively.
pub(super) fn consume_telescope_annotations(ty: &Expr) -> Expr {
    use clean_kernel::expr::ExprKind;
    match ty.kind() {
        ExprKind::Pi(bd, dom, body) => Expr::pi(
            *bd,
            clean_kernel::inductive::consume_type_annotations(dom).clone(),
            consume_telescope_annotations(body),
        ),
        _ => ty.clone(),
    }
}

/// Map a constant to the root of the inductive family it belongs to, using
/// the source environment's checked side tables. `None` for non-members
/// (including value-bearing generated definitions like `noConfusion`).
pub(super) fn inductive_family_root(source: &Environment, name: &Name) -> Option<Name> {
    if source.get_inductive(name).is_some() {
        return Some(name.clone());
    }
    if let Some(ctor) = source.get_constructor(name) {
        return Some(ctor.inductive_name.clone());
    }
    if let Some(rec) = source.get_recursor(name) {
        return Some(rec.inductive_name.clone());
    }
    None
}

/// Carry the inductive family rooted at `root` into the recheck environment
/// through the kernel's full checked `add_inductive` path.
///
/// Resolves the family's own dependencies first (depth-first, same walk as
/// carried definitions), replays the reconstructed `InductiveDecl`,
/// cross-checks regenerated members against the source environment, computes
/// the union closure over all member types, and registers the family in the
/// gate state. Errors are reject reasons; every failure is cached so later
/// dependents fail fast with the same audit trail.
pub(super) fn carry_inductive_family(
    source: &Environment,
    state: &mut GateState,
    root: &Name,
    in_progress: &mut Vec<String>,
) -> Result<(), String> {
    let root_str = root.to_string();
    if let Some(reason) = state.failed_families.get(&root_str) {
        return Err(reason.clone());
    }
    if state.carried_idx.contains_key(&root_str) {
        return Ok(());
    }
    if in_progress.iter().any(|n| n == &root_str) {
        return Err(format!(
            "dependency-cycle: inductive family `{root_str}` participates in a reference \
             cycle ({})",
            in_progress.join(" -> ")
        ));
    }

    // v3.0 fence: single-type, non-nested, non-mutual families only.
    let Some(ind_val) = source.get_inductive(root) else {
        let reason = format!(
            "carried-inductive-failed: `{root_str}` is registered as an inductive-family \
             member but its family root has no InductiveVal in the source environment"
        );
        state.failed_families.insert(root_str, reason.clone());
        return Err(reason);
    };
    if ind_val.all_names.len() != 1 || ind_val.is_nested {
        let shape = if ind_val.all_names.len() != 1 {
            "mutual"
        } else {
            "nested"
        };
        // Audit precision: record HOW the gate reached this family (the
        // depth-first resolution chain), so out-of-fence rejections are
        // diagnosable from the reason alone.
        let via = if in_progress.is_empty() {
            String::new()
        } else {
            format!(" [resolved via {}]", in_progress.join(" -> "))
        };
        let reason = format!(
            "carried-inductive-unsupported: mutual/nested — family `{root_str}` is {shape} \
             ({} types in block, is_nested={}); graduation v3.0 carries only single-type \
             non-nested families{via}",
            ind_val.all_names.len(),
            ind_val.is_nested
        );
        state.failed_families.insert(root_str, reason.clone());
        return Err(reason);
    }
    let Some(mut decl) = source.inductive_decl_of(root) else {
        let reason = format!(
            "carried-inductive-failed: inductive family `{root_str}` could not be \
             reassembled from the source environment's side tables"
        );
        state.failed_families.insert(root_str, reason.clone());
        return Err(reason);
    };
    // Lean-kernel-parity annotation erasure (see
    // `consume_telescope_annotations`): the replayed family is the
    // kernel-semantic object; elaborator gadgets (`optParam`/`autoParam`/...)
    // are erased from every telescope so their payloads (e.g. mathlib's
    // `*._autoParam : Lean.Syntax` tactic defaults) never enter the carry
    // closure.
    for ty in &mut decl.types {
        ty.type_ = consume_telescope_annotations(&ty.type_);
        for ctor in &mut ty.constructors {
            ctor.type_ = consume_telescope_annotations(&ctor.type_);
        }
    }

    // Resolve the family's own dependencies first (refs of the inductive
    // type and of every constructor type), excluding the members themselves.
    let ctor_names: Vec<String> = decl.types[0]
        .constructors
        .iter()
        .map(|c| c.name.to_string())
        .collect();
    let mut member_set: HashSet<String> = ctor_names.iter().cloned().collect();
    member_set.insert(root_str.clone());
    let mut refs: HashSet<String> = collect_constant_refs(&decl.types[0].type_);
    for ctor in &decl.types[0].constructors {
        refs.extend(collect_constant_refs(&ctor.type_));
    }
    let mut refs: Vec<String> = refs.difference(&member_set).cloned().collect();
    refs.sort();
    in_progress.push(root_str.clone());
    let resolved: Result<(), String> = refs
        .iter()
        .try_for_each(|dep| resolve_dependency(source, state, dep, in_progress));
    in_progress.pop();
    if let Err(reason) = resolved {
        state.failed_families.insert(root_str, reason.clone());
        return Err(reason);
    }

    // Snapshot family-prefixed names so the post-replay scan can attribute
    // exactly the constants THIS add_inductive added.
    let member_prefix = format!("{root_str}.");
    let is_family_name = |name: &str| {
        name == root_str || name.starts_with(&member_prefix) || member_set.contains(name)
    };
    let before: HashSet<String> = state
        .recheck
        .constants()
        .map(|c| c.name.to_string())
        .filter(|name| is_family_name(name))
        .collect();

    // The checked kernel replay: positivity, nested positivity, universe
    // constraints, recursor generation — the only path to family_checked.
    // Run it in a SCRATCH clone first: a family that fails any later check
    // (member cross-check, union closure) must leave the real recheck
    // environment untouched, or a later dependent would resolve the orphaned
    // members instead of hitting the cached failure.
    let mut scratch = state.recheck.clone();
    if let Err(e) = state.base.add_family(&mut scratch, decl.clone()) {
        let reason = format!(
            "carried-inductive-failed: inductive family `{root_str}` did not pass its \
             kernel add_inductive re-check ({e})"
        );
        state.failed_families.insert(root_str, reason.clone());
        return Err(reason);
    }
    let member_names: Vec<String> = {
        let mut added: Vec<String> = scratch
            .constants()
            .map(|c| c.name.to_string())
            .filter(|name| is_family_name(name) && !before.contains(name))
            .collect();
        added.sort();
        added
    };

    // Member cross-check (surface a6): every value-less family member the
    // source environment carries must match the regenerated constant.
    let mut check_names: Vec<String> = vec![root_str.clone()];
    check_names.extend(ctor_names.iter().cloned());
    let recursor_names: Vec<String> = ["rec", "casesOn", "recOn"]
        .iter()
        .map(|suffix| format!("{root_str}.{suffix}"))
        .filter(|name| member_names.contains(name))
        .collect();
    check_names.extend(recursor_names.iter().cloned());
    for member in &check_names {
        let member_name = Name::from_string(member);
        let Some(source_info) = source.get_const(&member_name) else {
            continue;
        };
        if source_info.value.is_some() {
            // Value-bearing source constants (e.g. an importer's casesOn
            // definition) are not what this family carries; dependents that
            // reference them are checked against the regenerated constant.
            continue;
        }
        let regenerated = scratch.get_const(&member_name);
        // Binder info (implicit/strict-implicit annotations) is elaborator
        // metadata the kernel ignores, and the `.olean` direct importer does
        // not preserve it (imported binders arrive as Default); everything
        // kernel-meaningful — de Bruijn structure, constants, universe
        // levels, level params, QTT multiplicity — must match exactly. See
        // `exprs_equal_ignoring_binder_info`.
        //
        // The source side is compared through the same annotation erasure the
        // carried decl went through (`consume_telescope_annotations`):
        // constructor types may carry `optParam`/`autoParam` gadgets that the
        // replayed family deliberately drops (Lean's own kernel generates
        // annotation-free recursors from annotated constructors). For
        // generated members (root, rec/casesOn/recOn) the erasure is the
        // identity.
        let source_type = consume_telescope_annotations(&source_info.type_);
        let matches = regenerated.is_some_and(|info| {
            info.level_params == source_info.level_params
                && exprs_equal_ignoring_binder_info(&info.type_, &source_type)
        });
        if !matches {
            // Audit precision: show both spellings so a mismatch is
            // diagnosable from the rejection reason alone.
            let detail = match regenerated {
                Some(info) => format!(
                    "source levels {:?} type `{}` vs regenerated levels {:?} type `{}`",
                    source_info.level_params, source_info.type_, info.level_params, info.type_
                ),
                None => "member missing from the regenerated family".to_string(),
            };
            let reason = format!(
                "carried-inductive-failed: regenerated member `{member}` of family \
                 `{root_str}` does not match the source environment's checked metadata \
                 (level params + type must be identical up to binder info): {detail}"
            );
            state.failed_families.insert(root_str, reason.clone());
            return Err(reason);
        }
    }

    // Union closure over ALL member types (surface a4): foundational-only or
    // the whole family fails, even for constructors no theorem references.
    let mut domain_axioms: HashSet<String> = HashSet::new();
    for member in std::iter::once(&root_str).chain(ctor_names.iter()) {
        let deps = scratch
            .axiom_deps(&Name::from_string(member))
            .unwrap_or_default();
        domain_axioms.extend(deps.iter().map(Name::to_string));
    }
    if !domain_axioms.is_empty() {
        let mut axioms: Vec<String> = domain_axioms.into_iter().collect();
        axioms.sort();
        let reason = format!(
            "carried-inductive-failed: inductive family `{root_str}` has a non-foundational \
             union closure over its member types [{}] — a constructor-type axiom rejects \
             the whole family",
            axioms.join(", ")
        );
        state.failed_families.insert(root_str, reason.clone());
        return Err(reason);
    }

    let entry = build_family_record_entry(source, &scratch, root, &decl, &ctor_names).inspect_err(
        |reason| {
            state
                .failed_families
                .insert(root_str.clone(), reason.clone());
        },
    )?;

    // Every check passed: commit the family into the REAL recheck
    // environment via the same checked path (deterministic — it just
    // succeeded against an identical environment in `scratch`).
    if let Err(e) = state.base.add_family(&mut state.recheck, decl) {
        let reason = format!(
            "carried-inductive-failed: inductive family `{root_str}` failed its commit \
             replay into the recheck environment ({e})"
        );
        state.failed_families.insert(root_str, reason.clone());
        return Err(reason);
    }

    state.register_family(CarriedFamilyState {
        entry,
        root: root_str,
        ctor_names,
        recursor_names,
        member_names,
        refs,
    });
    Ok(())
}

/// Assemble the family's `carried_inductives` record entry (audit identity:
/// hashes, closure, structure fields, kernel facts). `checked` is the
/// environment the family's `add_inductive` replay just succeeded in.
fn build_family_record_entry(
    source: &Environment,
    checked: &Environment,
    root: &Name,
    decl: &clean_kernel::inductive::InductiveDecl,
    ctor_names: &[String],
) -> Result<CarriedInductive, String> {
    let root_str = root.to_string();
    let statement_hash = expr_canonical_digest(&decl.types[0].type_)
        .map_err(|e| format!("carried-inductive-failed: hash-failed for `{root_str}`: {e}"))?;
    let mut constructors = Vec::with_capacity(decl.types[0].constructors.len());
    for ctor in &decl.types[0].constructors {
        constructors.push(CarriedInductiveConstructor {
            name: ctor.name.to_string(),
            statement_hash: expr_canonical_digest(&ctor.type_).map_err(|e| {
                format!(
                    "carried-inductive-failed: hash-failed for constructor `{}`: {e}",
                    ctor.name
                )
            })?,
        });
    }
    // `num_params` as actually re-checked: fixed-index promotion may raise it
    // above the source decl's value, and the shard metadata must carry the
    // value the replay needs.
    let num_params = checked
        .get_inductive(root)
        .map_or(decl.num_params, |val| val.num_params);
    let structure_fields = source
        .get_structure_field_names(root)
        .map(|fields| fields.iter().map(Name::to_string).collect())
        .unwrap_or_default();
    debug_assert_eq!(ctor_names.len(), constructors.len());

    Ok(CarriedInductive {
        name: root_str,
        level_params: decl.level_params.iter().map(Name::to_string).collect(),
        num_params,
        statement_hash,
        constructors,
        members_in_shard: Vec::new(),
        kernel: KernelFacts {
            verdict: KernelVerdict::KernelVerified,
            value_typechecked: false,
            family_checked: true,
            checker: format!("clean-kernel {}", env!("CARGO_PKG_VERSION")),
        },
        axiom_closure: AxiomClosure {
            foundational_only: true,
            domain_axioms: Vec::new(),
            axiom_profile_bits: 0,
        },
        structure_fields,
        required_by: Vec::new(),
    })
}
