//! Generated case labels only. Goal.case_binders, never these labels, owns fields.

use clean_kernel::Name;
use clean_parser::SurfaceName;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum CaseFieldKind {
    Field,
    InductionHypothesis,
}

pub(crate) fn generated_case_field_name(
    tag: &SurfaceName,
    index: u64,
    kind: CaseFieldKind,
) -> SurfaceName {
    match kind {
        CaseFieldKind::Field => super::pattern::names::generated_suffix(tag, &format!("_{index}")),
        CaseFieldKind::InductionHypothesis => {
            if let Some(component) = tag.component_text() {
                SurfaceName::from_name(Name::anon().str(format!("ih_{component}_{index}")))
            } else {
                super::pattern::names::generated_suffix(tag, &format!("_ih_{index}"))
            }
        }
    }
}
