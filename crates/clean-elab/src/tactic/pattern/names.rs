//! Typed hypothesis labels and checked source-name adapters.

use super::super::{TacticError, TacticResult};
use clean_kernel::{name::NameInner, Name};
use clean_parser::SurfaceName;

pub(crate) fn local_name_matches(actual: &SurfaceName, requested: &SurfaceName) -> bool {
    !requested.is_relative_constructor()
        && !requested.is_anonymous()
        && !requested.is_unescaped_component("_")
        && !actual.is_unescaped_component("_")
        && actual.name() == requested.name()
        && template_marks_admit(actual, requested)
}

/// Whether the hypothesis named `actual` is the one the name `requested` a
/// tactic was given denotes: the same name, read with the hygiene marks of a
/// notation or macro template (see [`template_marks_admit`]). Unlike
/// [`local_name_matches`], a `_` or anonymous name is compared like any
/// other.
pub(crate) fn hypothesis_named(actual: &SurfaceName, requested: &SurfaceName) -> bool {
    actual == requested && template_marks_admit(actual, requested)
}

/// Whether a hypothesis named `actual` may be what `requested` denotes, by
/// the hygiene marks of a notation or macro template's identifiers — Lean's
/// macro scopes, exactly as term elaboration reads them
/// (`ElabCtx::lookup_local_where`):
///
/// * a template PATTERN variable, or a template reference to one
///   (`TemplateScope`), is the hypothesis of that very scope, and a
///   hypothesis of a scope is no other name's;
/// * a template's FREE name (`TemplateOrigin`) is never a hypothesis of the
///   use site — `clear kh` in a template names no use-site `kh` (Lean's
///   `kh✝` matches no user local) — except the section variable it named
///   where the template was declared.
fn template_marks_admit(actual: &SurfaceName, requested: &SurfaceName) -> bool {
    match (requested.template_scope(), actual.template_scope()) {
        (Some(wanted), Some(found)) => return wanted == found,
        (Some(_), None) | (None, Some(_)) => return false,
        (None, None) => {}
    }
    requested
        .template_origin()
        .is_none_or(|origin| origin.section_variable && actual.is_section_variable())
}

pub(crate) fn require_binding_name(name: &SurfaceName, tactic: &str) -> TacticResult {
    if name.is_relative_constructor() || name.is_anonymous() {
        return Err(TacticError::InvalidTarget {
            tactic: tactic.into(),
            detail: "expected an exact non-relative binder name".into(),
        });
    }
    Ok(())
}

pub(crate) fn parse_binding_name(source: &str, tactic: &str) -> Result<SurfaceName, TacticError> {
    let name = clean_parser::parse_name(source).map_err(|error| TacticError::InvalidTarget {
        tactic: tactic.into(),
        detail: format!("invalid identifier: {error}"),
    })?;
    require_binding_name(&name, tactic)?;
    Ok(name)
}

/// Preserve familiar all-Str spelling without flattening path components.
/// Numeric names use a typed frame, disjoint from that spelling family.
pub(crate) fn generated_suffix(base: &SurfaceName, suffix: &str) -> SurfaceName {
    let mut parts = Vec::new();
    let mut cursor = base.name();
    while let NameInner::Str(parent, _) | NameInner::Num(parent, _) = cursor.inner() {
        parts.push(cursor.inner());
        cursor = parent;
    }
    parts.reverse();
    if !parts.is_empty() && parts.iter().all(|part| matches!(part, NameInner::Str(..))) {
        let NameInner::Str(parent, last) = base.name().inner() else {
            unreachable!()
        };
        return SurfaceName::from_name(parent.as_ref().clone().str(format!("{last}{suffix}")));
    }
    let mut name = Name::anon().num(0x5452_4859).num(parts.len() as u64);
    for part in parts {
        name = match part {
            NameInner::Str(_, text) => name.str(text.as_ref()),
            NameInner::Num(_, number) => name.num(*number),
            NameInner::Anon => unreachable!(),
        };
    }
    SurfaceName::from_name(name.str(suffix))
}
