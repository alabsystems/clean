// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Which simp-list names that resolve to nothing in Clean's environment Lean
//! 4.8.0 would still accept (G48, ledger (118)).
//!
//! A name that names nothing is an unknown identifier in Lean, and since G48
//! in Clean too, with two exceptions where the absence is Clean's
//! incompleteness rather than the user's error:
//!
//! * a declaration Lean GENERATES on demand from an existing constant and
//!   Clean does not mint ([`lean_generates_from`]), and
//! * a name of Lean 4.8.0's `Init` that Clean's builtin prelude lacks, read
//!   the way Lean's `resolveGlobalName` reads it ([`init_name_reachable`]).
//!
//! Each exception is exactly as wide as what pinned Lean 4.8.0 realizes,
//! measured with `#check` (review r4t, 2026-10-09):
//!
//! * `C.injEq` / `C.inj` exist only for a constructor `C` of a non-`Prop`
//!   inductive with a field that is neither a proof nor determined by the
//!   result type's indices (`T.a.injEq` for a field-less `T.a`, `P.mk.injEq`
//!   for `structure P where h : True`, `I.mk.injEq` for `I.mk (n) : I n` and
//!   `Or.inl.injEq` are all unknown; `J.mk (n m) : J n` and `Vec.cons` have
//!   one).
//! * `D.eq_def` and `D.eq_1` exist for every definition `D`, and only for a
//!   definition (`Nat.add_zero.eq_def` is unknown: a theorem).
//! * `D.eq_<n>` for `n ≥ 2` exists only when `D` is RECURSIVE: a
//!   non-recursive definition by pattern matching gets the single
//!   `D.eq_1 : D x = match x with …` (`f.eq_2` is unknown for `def f | 0 => 1
//!   | n+1 => n`), while `fib` gets one equation per alternative. Clean's
//!   bound on the alternatives is the number of leaves of the compiled case
//!   tree ([`case_leaves`]): every non-redundant alternative reaches at least
//!   one leaf, so the bound never refuses an equation Lean has, and
//!   `f.eq_7` is refused.
//! * A protected `Init` name is never reached from an ATOMIC identifier
//!   through a namespace (`open Nat in … simp [pow_succ]`: "unknown
//!   identifier 'pow_succ'").

use clean_kernel::env::ConstantKind;
use clean_kernel::name::NameInner;
use clean_kernel::{Environment, Expr, ExprKind, Name, RecursorArgOrder};
use clean_parser::SurfaceName;

use crate::tactic::ProofState;

/// Whether `name`, which names nothing in this environment, is still a name
/// Lean 4.8.0 would accept (see the module documentation).
pub(super) fn names_unminted_lean_name(ps: &ProofState, name: &SurfaceName) -> bool {
    generated_from_existing(ps, name) || init_name_reachable(ps, name)
}

fn generated_from_existing(ps: &ProofState, name: &SurfaceName) -> bool {
    let base = name.parent();
    if base.is_anonymous() {
        return false;
    }
    let Ok(parent) = crate::tactic::core::resolve_global_name(ps, &base) else {
        return false;
    };
    lean_generates_from(ps.env(), &parent, &name.last_component().to_string())
}

/// Whether Lean 4.8.0 realizes `<parent>.<suffix>` on demand.
pub(super) fn lean_generates_from(env: &Environment, parent: &Name, suffix: &str) -> bool {
    match suffix {
        "injEq" | "inj" => has_injectivity_theorem(env, parent),
        "eq_def" => is_plain_definition(env, parent),
        _ => match suffix.strip_prefix("eq_").and_then(parse_index) {
            Some(1) => is_plain_definition(env, parent),
            Some(n) if n >= 2 => {
                is_plain_definition(env, parent)
                    && env
                        .get_const(parent)
                        .and_then(|c| c.value.as_ref())
                        .is_some_and(|value| {
                            if let Some(alternatives) =
                                course_of_values_alternatives(env, parent, value)
                            {
                                return n <= alternatives;
                            }
                            is_recursive_value(env, value) && n <= case_leaves(env, value)
                        })
            }
            _ => false,
        },
    }
}

/// The alternatives of a definition Clean compiled through its
/// course-of-values transform (`crates/clean-elab/src/infer/course_of_values.rs`):
/// `def f : Nat → R | 0 => … | 1 => … | n+2 => …` becomes the wrapper `fun n =>
/// Prod.fst (f.cov n)` over a recursive auxiliary `f.cov`, so the value itself
/// holds no recursor and no case tree. The transform fires only on exactly
/// those three arms, Lean's `f.eq_1` … `f.eq_3` (pinned Lean 4.8.0 realizes
/// `fib.eq_3` and refuses `fib.eq_4`). `None` for any other value.
fn course_of_values_alternatives(env: &Environment, parent: &Name, value: &Expr) -> Option<usize> {
    let mut body = value;
    while let ExprKind::Lam(_, _, b) = body.kind() {
        body = b.as_ref();
    }
    let ExprKind::Const(head, _) = body.get_app_fn().kind() else {
        return None;
    };
    let args = body.get_app_args();
    if head.to_string() != "Prod.fst" {
        return None;
    }
    let aux = parent.clone().str("cov");
    let inner = args.last()?;
    let ExprKind::Const(inner_head, _) = inner.get_app_fn().kind() else {
        return None;
    };
    let aux_value = env.get_const(&aux)?.value.as_ref()?;
    (*inner_head == aux && is_recursive_value(env, aux_value)).then_some(3)
}

/// `<digits>` with no leading zero (`eq_01` is not an equation name).
fn parse_index(digits: &str) -> Option<usize> {
    if digits.is_empty() || !digits.bytes().all(|b| b.is_ascii_digit()) || digits.starts_with('0') {
        return None;
    }
    digits.parse().ok()
}

/// A definition with a value that is not an inductive's own machinery.
fn is_plain_definition(env: &Environment, name: &Name) -> bool {
    env.get_const(name)
        .is_some_and(|c| matches!(c.kind, ConstantKind::Definition) && c.value.is_some())
        && env.get_constructor(name).is_none()
        && env.get_recursor(name).is_none()
        && env.get_inductive(name).is_none()
}

/// Lean's `mkInjectiveTheorems`: a constructor of a non-`Prop` inductive with
/// at least one field that is not a proof and does not occur in the indices
/// of the constructor's result type (those are shared between the two sides).
fn has_injectivity_theorem(env: &Environment, ctor_name: &Name) -> bool {
    let Some(ctor) = env.get_constructor(ctor_name) else {
        return false;
    };
    let Some(ind) = env.get_inductive(&ctor.inductive_name) else {
        return false;
    };
    if ends_in_prop(&ind.type_) {
        return false;
    }
    let params = ctor.num_params as usize;
    let fields = ctor.num_fields as usize;
    let mut ty = &ctor.type_;
    let mut domains = Vec::with_capacity(fields);
    for i in 0..params + fields {
        let ExprKind::Pi(_, dom, body) = ty.kind() else {
            return false;
        };
        if i >= params {
            domains.push(dom.as_ref());
        }
        ty = body.as_ref();
    }
    let result_args = ty.get_app_args();
    let indices: Vec<&Expr> = result_args.iter().skip(params).copied().collect();
    domains.iter().enumerate().any(|(i, dom)| {
        // Field `i` is bound `fields - 1 - i` binders above the result type.
        let bvar = u32::try_from(fields - 1 - i).unwrap_or(u32::MAX);
        !indices.iter().any(|ix| ix.has_loose_bvar(bvar)) && !is_structurally_prop(env, dom)
    })
}

/// The type ends, after its Pi binders, in `Prop`.
fn ends_in_prop(ty: &Expr) -> bool {
    let mut cur = ty;
    loop {
        match cur.kind() {
            ExprKind::Pi(_, _, body) => cur = body.as_ref(),
            ExprKind::Sort(level) => return level.is_zero(),
            _ => return false,
        }
    }
}

/// The field type's head constant is declared to land in `Prop` (`True`,
/// `Eq`, `n < m`, …). Unknown heads count as data, which can only make Clean
/// accept a name Lean lacks for a constructor whose fields are all proofs of
/// a variable proposition — never refuse one Lean has.
fn is_structurally_prop(env: &Environment, ty: &Expr) -> bool {
    match ty.get_app_fn().kind() {
        ExprKind::Const(head, _) => env.get_const(head).is_some_and(|c| ends_in_prop(&c.type_)),
        _ => false,
    }
}

fn last_component(name: &Name) -> Option<&str> {
    match name.inner() {
        NameInner::Str(_, last) => Some(last.as_ref()),
        _ => None,
    }
}

/// The value recurses: Clean's structural lowering emits a `T.rec` (a
/// non-recursive match lowers to `T.casesOn`), its well-founded lowering a
/// `WellFounded.fix`, and an imported Lean definition a `T.brecOn`.
fn is_recursive_value(env: &Environment, value: &Expr) -> bool {
    crate::tactic::unfold::collect_consts(value)
        .iter()
        .any(|c| match last_component(c) {
            Some("rec") => env.get_recursor(c).is_some(),
            Some("brecOn" | "binductionOn") => true,
            _ => {
                let s = c.to_string();
                s == "WellFounded.fix" || s == "WellFounded.fixF"
            }
        })
}

/// Upper bound on the match alternatives of a definition: the leaves of the
/// case tree its value compiles to. `T.rec` / `T.casesOn` sum over their
/// minor premises, a Lean matcher (`f.match_<k>`) is opened with its
/// arguments, `T.brecOn` / `WellFounded.fix` count their functional argument,
/// and anything else is one leaf. Exhausting the step budget answers the
/// maximum, which keeps the pre-G48 skip for a definition too large to
/// measure rather than refusing a name Lean may have.
fn case_leaves(env: &Environment, value: &Expr) -> usize {
    let mut fuel = 20_000usize;
    leaves(env, value, &mut fuel)
}

fn leaves(env: &Environment, e: &Expr, fuel: &mut usize) -> usize {
    if *fuel == 0 {
        return usize::MAX;
    }
    *fuel -= 1;
    let mut body = e;
    while let ExprKind::Lam(_, _, b) | ExprKind::Let(_, _, _, b, _) | ExprKind::MData(_, b) =
        body.kind()
    {
        body = b.as_ref();
    }
    let ExprKind::Const(head, _) = body.get_app_fn().kind() else {
        return 1;
    };
    let args = body.get_app_args();
    if let Some(minors) = minor_range(env, head) {
        return args
            .iter()
            .skip(minors.start)
            .take(minors.len())
            .fold(0usize, |acc, m| acc.saturating_add(leaves(env, m, fuel)))
            .max(1);
    }
    let last = last_component(head).unwrap_or("");
    if last.starts_with("match_") {
        if let Some(value) = env.get_const(head).and_then(|c| c.value.as_ref()) {
            let mut opened = value.clone();
            for arg in args.iter() {
                let ExprKind::Lam(_, _, b) = opened.kind() else {
                    break;
                };
                opened = b.instantiate(arg);
            }
            return leaves(env, &opened, fuel);
        }
    }
    let is_fix = matches!(last, "brecOn" | "binductionOn")
        || matches!(
            head.to_string().as_str(),
            "WellFounded.fix" | "WellFounded.fixF"
        );
    if is_fix {
        return args.iter().map(|a| leaves(env, a, fuel)).max().unwrap_or(1);
    }
    1
}

/// The argument positions of the minor premises of a `T.rec` / `T.casesOn`
/// head, in the layouts `recursion_site::split_layout` reads.
fn minor_range(env: &Environment, head: &Name) -> Option<std::ops::Range<usize>> {
    let NameInner::Str(prefix, last) = head.inner() else {
        return None;
    };
    match (last.as_ref(), env.get_recursor(head)) {
        ("casesOn" | "rec", Some(rec)) => {
            let passive = (rec.num_params + rec.num_motives) as usize;
            let minors = rec.rules.len();
            let start = if matches!(rec.arg_order, RecursorArgOrder::MajorAfterMotive) {
                passive + rec.num_indices as usize + 1
            } else {
                passive
            };
            Some(start..start + minors)
        }
        ("casesOn", None) => {
            let ind = env.get_inductive(prefix)?;
            let start = ind.num_params as usize + 1 + ind.num_indices as usize + 1;
            Some(start..start + ind.constructor_names.len())
        }
        _ => None,
    }
}

/// Whether an `Init` name Clean lacks is what `name` resolves to in Lean:
/// as written, under each enclosing namespace, or under each `open`
/// namespace — the last two only when the name is not `protected` or the
/// identifier is not atomic (`resolveQualifiedName`).
fn init_name_reachable(ps: &ProofState, name: &SurfaceName) -> bool {
    use crate::lean_core_names::{is_lean_init_name, is_lean_init_name_from_atomic_in_namespace};
    if is_lean_init_name(&name.qualify_under(&SurfaceName::default()).into_name()) {
        return true;
    }
    let atomic = name.parent().is_anonymous();
    let reachable = |full: Name| {
        if atomic {
            is_lean_init_name_from_atomic_in_namespace(&full)
        } else {
            is_lean_init_name(&full)
        }
    };
    let Some(ns_state) = ps.namespace_state() else {
        return false;
    };
    let mut prefix = ns_state.current_namespace().clone();
    while !prefix.is_anon() {
        if reachable(
            SurfaceName::from_name(prefix.clone())
                .append(name)
                .into_name(),
        ) {
            return true;
        }
        prefix = SurfaceName::from_name(prefix).parent().into_name();
    }
    ns_state.open_namespaces().iter().any(|open| {
        reachable(
            SurfaceName::from_name(open.clone())
                .append(name)
                .into_name(),
        )
    })
}
