// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Lean's rcases rules for constructor arguments and cleared components
//! (`Lean/Elab/Tactic/RCases.lean`):
//!
//! * [`process_constructor`] — which pattern each constructor field gets.
//!   Without `@`, patterns go to the EXPLICIT fields only; `@⟨…⟩` binds every
//!   field, implicit ones included.
//! * The clear pattern `-`. `rcasesCore` does not clear a `-` component on
//!   the spot: it records it, and `RCases.finish` clears all of them, with
//!   their dependents, once the whole pattern has run ("clearing too early
//!   can cause `cases` to fail"). Here a `-` component is renamed to a
//!   compiler-authored marker that travels with the hypothesis through every
//!   later `cases`/`subst`, and [`finish_rcases_clears`] clears the marked
//!   hypotheses of every goal at the end of the tactic.

use clean_kernel::name::NameInner;
use clean_kernel::{BinderInfo, Environment, ExprKind, FVarId, Name};
use clean_parser::SurfaceName;

use super::super::ProofState;
use super::rintro::RIntroPattern;

/// The numeric frame of compiler-authored tactic binder names (no identifier
/// token spells a numeric component, so user code cannot reach them).
const TACTIC_FRAME: u64 = 0x5441_4354;
const CLEAR_MARK: &str = "rcases_clear";

/// Which constructor arguments a tuple pattern addresses
/// (`RCasesPatt.asTuple`'s flag).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum CtorArgs {
    /// `⟨…⟩`: the explicit arguments; an implicit one is left unnamed.
    ExplicitOnly,
    /// `@⟨…⟩`: every argument.
    All,
}

/// Lean's `RCasesPatt.asTuple`: the arguments a pattern addresses and its
/// components when it is matched against one constructor.
pub(super) fn as_tuple(pattern: &RIntroPattern) -> (CtorArgs, Vec<RIntroPattern>) {
    match pattern {
        RIntroPattern::Tuple(sub) | RIntroPattern::Anonymous(sub) => {
            (CtorArgs::ExplicitOnly, sub.clone())
        }
        RIntroPattern::Explicit(inner) => (CtorArgs::All, as_tuple(inner).1),
        other => (CtorArgs::ExplicitOnly, vec![other.clone()]),
    }
}

/// Lean's `processConstructor`: one pattern per constructor field.
///
/// `explicit_fields[i]` says whether field `i` is an explicit binder of the
/// constructor. Without `@`, an implicit field gets `_` and consumes no
/// pattern. Every field but the last takes the next pattern (`_` once they
/// run out); the last takes what remains — nothing (`_`), one pattern, or the
/// rest as a tuple (`⟨a, b, c⟩` on `∃ x y, p` reads `⟨a, ⟨b, c⟩⟩`), which
/// keeps the `@` it came with.
pub(super) fn process_constructor(
    explicit_fields: &[bool],
    args: CtorArgs,
    patterns: &[RIntroPattern],
) -> Vec<RIntroPattern> {
    let mut rest = patterns;
    let last = explicit_fields.len().saturating_sub(1);
    explicit_fields
        .iter()
        .enumerate()
        .map(|(index, &explicit)| {
            if args == CtorArgs::ExplicitOnly && !explicit {
                return RIntroPattern::Wildcard;
            }
            if index < last {
                let head = rest.first().cloned().unwrap_or(RIntroPattern::Wildcard);
                rest = rest.get(1..).unwrap_or_default();
                return head;
            }
            match rest {
                [] => RIntroPattern::Wildcard,
                [single] => single.clone(),
                many => {
                    let tuple = RIntroPattern::Tuple(many.to_vec());
                    match args {
                        CtorArgs::All => RIntroPattern::Explicit(Box::new(tuple)),
                        CtorArgs::ExplicitOnly => tuple,
                    }
                }
            }
        })
        .collect()
}

/// Whether each of the `num_fields` fields of constructor number `ctor_index`
/// of the inductive `inductive` is an explicit binder. When the constructor
/// cannot be read, or the goal does not hold exactly its fields (an indexed
/// family's `cases` can add or remove hypotheses), every field counts as
/// explicit — what a plain positional match does.
pub(super) fn field_explicitness(
    env: &Environment,
    inductive: Option<&Name>,
    ctor_index: usize,
    num_fields: usize,
) -> Vec<bool> {
    read_field_explicitness(env, inductive, ctor_index, num_fields)
        .unwrap_or_else(|| vec![true; num_fields])
}

fn read_field_explicitness(
    env: &Environment,
    inductive: Option<&Name>,
    ctor_index: usize,
    num_fields: usize,
) -> Option<Vec<bool>> {
    let ind = env.get_inductive(inductive?)?;
    let ctor = env.get_constructor(ind.constructor_names.get(ctor_index)?)?;
    if usize::try_from(ctor.num_fields).ok()? != num_fields {
        return None;
    }
    let mut ty = &ctor.type_;
    for _ in 0..ctor.num_params {
        let ExprKind::Pi(_, _, body) = ty.kind() else {
            return None;
        };
        ty = body;
    }
    let mut explicit = Vec::with_capacity(num_fields);
    for _ in 0..num_fields {
        let ExprKind::Pi(binder, _, body) = ty.kind() else {
            return None;
        };
        explicit.push(matches!(binder.info, BinderInfo::Default));
        ty = body;
    }
    Some(explicit)
}

/// The name a `-` component carries until [`finish_rcases_clears`] clears
/// it. `fvar` keeps the markers of one context apart.
pub(super) fn clear_marker(fvar: FVarId) -> SurfaceName {
    SurfaceName::from_name(
        Name::anon()
            .num(TACTIC_FRAME)
            .str(CLEAR_MARK)
            .num(fvar.as_u64()),
    )
}

/// Whether `name` is a [`clear_marker`] (possibly with the numeric suffix
/// `intro` appends to an already-taken name).
fn is_clear_marker(name: &SurfaceName) -> bool {
    let mut components = Vec::new();
    let mut cursor = name.name();
    while let NameInner::Str(parent, _) | NameInner::Num(parent, _) = cursor.inner() {
        components.push(cursor.inner());
        cursor = parent;
    }
    matches!(
        components.as_slice(),
        [.., NameInner::Str(_, mark), NameInner::Num(_, TACTIC_FRAME)] if &**mark == CLEAR_MARK
    )
}

/// The inaccessible name a marked hypothesis keeps when it cannot be cleared.
fn kept_name(fvar: FVarId) -> SurfaceName {
    SurfaceName::from_name(
        Name::anon()
            .num(TACTIC_FRAME)
            .str("rcases")
            .num(fvar.as_u64()),
    )
}

/// `RCases.finish` / `tryClearMany'`: in every goal, clear each hypothesis a
/// `-` pattern marked together with every hypothesis that depends on it, the
/// latest first. As Lean's `tryClear`, a hypothesis that the target or a
/// remaining hypothesis still mentions stays — under an inaccessible name, so
/// no later rcases reads it as marked.
///
/// SOUNDNESS: this only hides hypotheses from a goal's context (what the
/// `clear` tactic does); nothing that remains mentions a removed one, and the
/// assembled proof term is kernel-rechecked as before.
pub(crate) fn finish_rcases_clears(state: &mut ProofState) {
    for index in 0..state.goals.len() {
        let Some(goal) = state.goals.get(index) else {
            continue;
        };
        if !goal
            .local_ctx
            .iter()
            .any(|decl| is_clear_marker(&decl.name))
        {
            continue;
        }
        let instantiate = |expr: &clean_kernel::Expr| state.metas.instantiate(expr);
        let mentions_any = |decl: &super::super::LocalDecl, erase: &[FVarId]| {
            let ty = instantiate(&decl.ty);
            let value = decl.value.as_ref().map(instantiate);
            erase.iter().any(|fvar| {
                crate::tactic::builtins_replace::mentions_fvar(&ty, *fvar)
                    || value
                        .as_ref()
                        .is_some_and(|v| crate::tactic::builtins_replace::mentions_fvar(v, *fvar))
            })
        };
        // `toErase`: the marked hypotheses, then their dependents in context
        // order (a dependent of a dependent is found because it comes later).
        let mut erase: Vec<FVarId> = goal
            .local_ctx
            .iter()
            .filter(|decl| is_clear_marker(&decl.name))
            .map(|decl| decl.fvar)
            .collect();
        for decl in &goal.local_ctx {
            if !erase.contains(&decl.fvar) && mentions_any(decl, &erase) {
                erase.push(decl.fvar);
            }
        }
        let target = instantiate(&goal.target);
        let mut ctx = goal.local_ctx.clone();
        // `tryClearMany` folds from the right: the latest first.
        for fvar in erase.iter().rev() {
            let Some(position) = ctx.iter().position(|decl| decl.fvar == *fvar) else {
                continue;
            };
            let still_needed = crate::tactic::builtins_replace::mentions_fvar(&target, *fvar)
                || ctx
                    .iter()
                    .any(|decl| decl.fvar != *fvar && mentions_any(decl, &[*fvar]));
            if !still_needed {
                ctx.remove(position);
            }
        }
        for decl in &mut ctx {
            if is_clear_marker(&decl.name) {
                decl.name = kept_name(decl.fvar);
            }
        }
        if let Some(goal) = state.goals.get_mut(index) {
            goal.local_ctx = ctx;
        }
    }
    state.invalidate_tc_cache();
}

#[cfg(test)]
mod tests {
    use super::*;

    fn name(text: &str) -> RIntroPattern {
        RIntroPattern::Name(SurfaceName::component(text, false))
    }

    fn names(pats: &[RIntroPattern]) -> Vec<String> {
        pats.iter().map(|p| format!("{p:?}")).collect()
    }

    #[test]
    fn test_process_constructor_skips_implicit_fields_without_at() {
        // `mk {n} (x) (y)`: `⟨a, b⟩` binds x and y; `@⟨a, b, c⟩` binds all.
        let fields = [false, true, true];
        let got = process_constructor(&fields, CtorArgs::ExplicitOnly, &[name("a"), name("b")]);
        assert_eq!(
            names(&got),
            names(&[RIntroPattern::Wildcard, name("a"), name("b")])
        );
        let got = process_constructor(&fields, CtorArgs::All, &[name("a"), name("b"), name("c")]);
        assert_eq!(names(&got), names(&[name("a"), name("b"), name("c")]));
    }

    #[test]
    fn test_process_constructor_groups_the_tail_into_the_last_field() {
        let got = process_constructor(
            &[true, true],
            CtorArgs::ExplicitOnly,
            &[name("a"), name("b"), name("c")],
        );
        assert_eq!(
            names(&got),
            names(&[name("a"), RIntroPattern::Tuple(vec![name("b"), name("c")])])
        );
        // Under `@` the grouped tail stays explicit.
        let got = process_constructor(
            &[true, true],
            CtorArgs::All,
            &[name("a"), name("b"), name("c")],
        );
        assert_eq!(
            names(&got),
            names(&[
                name("a"),
                RIntroPattern::Explicit(Box::new(RIntroPattern::Tuple(vec![name("b"), name("c")])))
            ])
        );
        // Too few patterns: the rest are `_`; one field takes a single
        // pattern as itself, not as a one-element tuple.
        let got = process_constructor(&[true, true], CtorArgs::ExplicitOnly, &[name("a")]);
        assert_eq!(names(&got), names(&[name("a"), RIntroPattern::Wildcard]));
        let got = process_constructor(&[true], CtorArgs::ExplicitOnly, &[name("a")]);
        assert_eq!(names(&got), names(&[name("a")]));
    }

    #[test]
    fn test_rintro_pattern_parse_clear_and_explicit() {
        assert!(matches!(
            RIntroPattern::parse("-"),
            Ok(RIntroPattern::Clear)
        ));
        let tuple = RIntroPattern::parse("⟨hlo, -⟩").expect("`⟨hlo, -⟩` parses");
        assert!(
            matches!(&tuple, RIntroPattern::Tuple(p)
                if matches!(p.as_slice(), [RIntroPattern::Name(_), RIntroPattern::Clear])),
            "got {tuple:?}"
        );
        let explicit = RIntroPattern::parse("@⟨a, b⟩").expect("`@⟨a, b⟩` parses");
        assert!(
            matches!(&explicit, RIntroPattern::Explicit(inner)
                if matches!(inner.as_ref(), RIntroPattern::Tuple(p) if p.len() == 2)),
            "got {explicit:?}"
        );
        // `@` binds tighter than `|`.
        let alt = RIntroPattern::parse("@(a | b) | c").expect("`@(a | b) | c` parses");
        assert!(
            matches!(&alt, RIntroPattern::Or(arms)
                if matches!(arms.as_slice(), [RIntroPattern::Explicit(inner), RIntroPattern::Name(_)]
                    if matches!(inner.as_ref(), RIntroPattern::Or(p) if p.len() == 2))),
            "got {alt:?}"
        );
        assert!(RIntroPattern::parse("@").is_err(), "`@` needs a pattern");
    }

    #[test]
    fn test_rintro_pattern_parse_keeps_parenthesized_alternatives_grouped() {
        let alt = RIntroPattern::parse("(hp | hq) | hr").expect("parses");
        assert!(
            matches!(&alt, RIntroPattern::Or(arms)
                if matches!(arms.as_slice(), [RIntroPattern::Or(inner), RIntroPattern::Name(_)]
                    if inner.len() == 2)),
            "got {alt:?}"
        );
        let typed = RIntroPattern::parse("hr | (h : #0)").expect("parses");
        assert!(
            matches!(&typed, RIntroPattern::Or(arms)
                if matches!(arms.as_slice(), [RIntroPattern::Name(_), RIntroPattern::Typed(_, 0)])),
            "got {typed:?}"
        );
    }

    #[test]
    fn test_clear_marker_is_recognized_with_an_intro_suffix() {
        let marker = clear_marker(FVarId::new(7));
        assert!(is_clear_marker(&marker));
        let suffixed = SurfaceName::from_name(marker.name().clone().num(1));
        assert!(is_clear_marker(&suffixed));
        assert!(!is_clear_marker(&kept_name(FVarId::new(7))));
        assert!(!is_clear_marker(&SurfaceName::component(
            "rcases_clear",
            false
        )));
    }
}
