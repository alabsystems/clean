// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Machine-readable diagnostics attached to an [`ElabError`].
//!
//! Split out of `error.rs` for file size: the error ENUM and its `From`
//! conversions stay there, the per-variant `AgentDiagnostic` mapping lives
//! here. Declared from `error.rs`, so this is `error::diagnostics`.

use super::*;

impl ElabError {
    /// Return machine-readable diagnostics attached to this elaboration error.
    #[must_use]
    pub fn agent_diagnostics(&self) -> Vec<AgentDiagnostic> {
        match self {
            // Attribution is presentation, not classification: a wrapped
            // error keeps the machine diagnostics of the error it wraps.
            Self::InTactic { source, .. } => source.agent_diagnostics(),
            Self::DerivingHandlerFailed { error, .. } => error.agent_diagnostics(),
            Self::UnknownIdentWithSuggestions { name, suggestions } => {
                let mut diag = AgentDiagnostic::error(
                    "ident.nearest_theorems",
                    format!("unknown identifier `{name}`"),
                )
                .with_fact("identifier", name.clone());
                for suggestion in suggestions {
                    diag = diag.with_suggestion(
                        format!("nearest theorem `{suggestion}`"),
                        Some(suggestion.clone()),
                    );
                }
                vec![diag]
            }
            // A self-reference carries the recursion FRAGMENT and the ways
            // across it. Deliberately no `replacement`: none of the three
            // options is a token swap, and offering one as if it were is the
            // failure mode this diagnostic replaces.
            Self::RecursionOutsideFragment {
                name,
                decl,
                params,
                detail,
            } => {
                vec![AgentDiagnostic::error(
                    "recursion.outside_fragment",
                    format!("`{name}` is the name being defined: `{decl}` is recursive"),
                )
                .with_facts([
                    ("identifier", name.clone()),
                    ("declaration", decl.clone()),
                    ("parameters", params.to_string()),
                    ("form", detail.clone()),
                    (
                        "supported",
                        "structural; well-founded with a termination_by measure \
                         naming ONE parameter"
                            .to_owned(),
                    ),
                ])
                .with_suggestion(
                    format!(
                        "restate `{decl}` structurally: match one parameter and \
                         recurse on its immediate sub-term"
                    ),
                    None,
                )
                .with_suggestion(
                    format!(
                        "give `{decl}` a `termination_by <parameter>` naming the ONE \
                         parameter that shrinks (the signature may stay as wide as it is)"
                    ),
                    None,
                )
                .with_suggestion(
                    format!(
                        "write `{decl}` in proof position — a signature plus the \
                         equations you rely on — where no emitted body is required"
                    ),
                    None,
                )]
            }
            Self::SameBatchHeaderUnavailable {
                name,
                sibling,
                reason,
            } => {
                vec![AgentDiagnostic::error(
                    "batch.header_unavailable",
                    format!("`{name}` names the same-batch declaration `{sibling}`"),
                )
                .with_facts([
                    ("identifier", name.clone()),
                    ("sibling", sibling.clone()),
                    ("reason", (*reason).to_owned()),
                ])
                .with_related(format!("`{sibling}` staged no header: {reason}"), None)
                .with_suggestion(
                    format!("repair `{sibling}`; every reference resolves once its signature does"),
                    None,
                )
                .with_suggestion(format!("write `{sibling}`'s result type explicitly"), None)
                .with_suggestion(format!("move `{sibling}` above this declaration"), None)]
            }
            Self::UnknownProjectionField {
                struct_name,
                field,
                suggestions,
            } => {
                let mut diag = AgentDiagnostic::error(
                    "structure.unknown_projection_field",
                    format!("unknown projection field `{field}` in `{struct_name}`"),
                )
                .with_facts([
                    ("structure", struct_name.to_string()),
                    ("field", field.clone()),
                    ("context", "projection".to_owned()),
                ]);
                for suggestion in suggestions {
                    diag = diag.with_suggestion(
                        format!("replace `{field}` with `{suggestion}`"),
                        Some(suggestion.clone()),
                    );
                }
                vec![diag]
            }
            Self::UnknownStructureField {
                struct_name,
                field,
                suggestions,
            } => {
                let mut diag = AgentDiagnostic::error(
                    "structure.unknown_field",
                    format!("unknown field `{field}` in `{struct_name}`"),
                )
                .with_facts([
                    ("structure", struct_name.to_string()),
                    ("field", field.clone()),
                ]);
                for suggestion in suggestions {
                    diag = diag.with_suggestion(
                        format!("replace `{field}` with `{suggestion}`"),
                        Some(suggestion.clone()),
                    );
                }
                vec![diag]
            }
            Self::MissingStructureFields {
                struct_name,
                fields,
            } => vec![AgentDiagnostic::error(
                "structure.missing_fields",
                format!("missing required field(s) for `{struct_name}`"),
            )
            .with_facts([
                ("structure", struct_name.to_string()),
                ("fields", fields.join(",")),
            ])],
            Self::StructureFieldTypeMismatch {
                struct_name,
                field,
                expected,
                actual,
            } => vec![AgentDiagnostic::error(
                "structure.field_type_mismatch",
                format!("field `{struct_name}.{field}` has the wrong type"),
            )
            .with_facts([
                ("structure", struct_name.to_string()),
                ("field", field.clone()),
                ("expected", expected.clone()),
                ("actual", actual.clone()),
            ])],
            Self::TacticFailed(err) => err.agent_diagnostics(),
            _ => Vec::new(),
        }
    }
}
