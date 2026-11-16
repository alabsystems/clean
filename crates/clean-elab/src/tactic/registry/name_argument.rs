//! Lossless internal transport for tactic identifier arguments, never a proof token.

use super::TacticError;
use clean_kernel::{Expr, ExprKind, MDataValue, Name};
use clean_parser::{NameComponentSyntax, SurfaceName};

fn key(suffix: &str) -> Name {
    Name::anon().str("_clean_tactic_name_v1").str(suffix)
}

/// Encode an identifier argument separately from elaborated term arguments.
pub(crate) fn encode_name_argument(name: &SurfaceName) -> Expr {
    let syntax: String = name
        .component_syntax()
        .iter()
        .map(|origin| match origin {
            NameComponentSyntax::Plain => 'p',
            NameComponentSyntax::Escaped => 'e',
            NameComponentSyntax::Generated => 'g',
        })
        .collect();
    // A notation or macro template's identifier carries its hygiene marks
    // (`clean_parser::TemplateScope`, `clean_parser::TemplateOrigin`): like
    // Lean's macro scopes they decide which hypothesis the name can denote
    // (`pattern::names::local_name_matches`), so they travel with it.
    let scope = name
        .template_scope()
        .map_or(0, |scope| scope.0.saturating_add(1));
    let template = match name.template_origin() {
        None => 0,
        Some(origin) if origin.section_variable => 2,
        Some(_) => 1,
    };
    Expr::mdata(
        vec![
            (key("version"), MDataValue::Nat(1)),
            (key("identity"), MDataValue::Name(name.name().clone())),
            (key("syntax"), MDataValue::String(syntax.into())),
            (
                key("relative"),
                MDataValue::Bool(name.is_relative_constructor()),
            ),
            (key("scope"), MDataValue::Nat(scope)),
            (key("template"), MDataValue::Nat(template)),
        ],
        Expr::const_(name.name().clone(), vec![]),
    )
}

/// Read the exact identifier protocol, refusing malformed wrappers.
/// A raw constant is a legacy generated identifier; an ordinary term returns None.
pub(crate) fn decode_name_argument(expr: &Expr) -> Result<Option<SurfaceName>, TacticError> {
    let invalid =
        || TacticError::TypeCheckFailed("malformed or oversized tactic identifier argument".into());
    match expr.kind() {
        ExprKind::Const(name, levels) if levels.is_empty() => {
            Ok(Some(SurfaceName::from_name(name.clone())))
        }
        ExprKind::MData(rows, inner) => {
            let [(version_key, MDataValue::Nat(1)), (identity_key, MDataValue::Name(identity)), (syntax_key, MDataValue::String(syntax)), (relative_key, MDataValue::Bool(relative)), (scope_key, MDataValue::Nat(scope)), (template_key, MDataValue::Nat(template))] =
                rows.as_slice()
            else {
                return Err(invalid());
            };
            if version_key != &key("version")
                || identity_key != &key("identity")
                || syntax_key != &key("syntax")
                || relative_key != &key("relative")
                || scope_key != &key("scope")
                || template_key != &key("template")
                || syntax.len() > 4096
                || *template > 2
            {
                return Err(invalid());
            }
            let ExprKind::Const(actual, levels) = inner.kind() else {
                return Err(invalid());
            };
            if actual != identity || !levels.is_empty() {
                return Err(invalid());
            }
            // Bound structural traversal before SurfaceName's metadata validation.
            let mut cursor = identity;
            let mut count = 0usize;
            while let clean_kernel::name::NameInner::Str(parent, _)
            | clean_kernel::name::NameInner::Num(parent, _) = cursor.inner()
            {
                count += 1;
                if count > syntax.len() {
                    return Err(invalid());
                }
                cursor = parent;
            }
            if count != syntax.len() {
                return Err(invalid());
            }
            let origins = syntax
                .bytes()
                .map(|tag| match tag {
                    b'p' => Ok(NameComponentSyntax::Plain),
                    b'e' => Ok(NameComponentSyntax::Escaped),
                    b'g' => Ok(NameComponentSyntax::Generated),
                    _ => Err(invalid()),
                })
                .collect::<Result<Vec<_>, _>>()?;
            let mut name = SurfaceName::from_syntax_parts(identity.clone(), origins, *relative)
                .map_err(|_| invalid())?;
            if *scope != 0 {
                name = name.with_template_scope(clean_parser::TemplateScope(*scope - 1));
            }
            if *template != 0 {
                // Only whether the name may denote a section variable is read
                // back (hypothesis matching); a template's GLOBAL names are
                // resolved before they are encoded.
                name =
                    name.with_template_origin(std::sync::Arc::new(clean_parser::TemplateOrigin {
                        namespace: Name::anon(),
                        section_variable: *template == 2,
                        site: None,
                    }));
            }
            Ok(Some(name))
        }
        _ => Ok(None),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn identifier_slots_preserve_structural_and_contextual_twins() {
        for spelling in ["_", "«_»", "A.B", "«A.B»", "«7»", "«_root_».x", ".ctor"] {
            let name = if spelling == "_" {
                SurfaceName::component("_", false)
            } else if spelling == ".ctor" {
                SurfaceName::component("ctor", false).with_relative_constructor()
            } else {
                clean_parser::parse_name(spelling).unwrap()
            };
            let decoded = decode_name_argument(&encode_name_argument(&name))
                .unwrap()
                .unwrap();
            assert!(name.same_syntax(&decoded), "{spelling}");
        }
        let numeric = SurfaceName::from_name(Name::anon().num(7));
        assert!(numeric.same_syntax(
            &decode_name_argument(&encode_name_argument(&numeric))
                .unwrap()
                .unwrap()
        ));
    }

    #[test]
    fn altered_identifier_payload_schema_and_population_refuse() {
        let name = SurfaceName::component("_", true);
        let ExprKind::MData(rows, inner) = encode_name_argument(&name).kind().clone() else {
            panic!()
        };
        let mut wrong_identity = rows.clone();
        wrong_identity[1].1 = MDataValue::Name(Name::anon().str("other"));
        let mut wrong_syntax = rows.clone();
        wrong_syntax[2].1 = MDataValue::String("pp".into());
        let mut duplicate = rows.clone();
        duplicate.push(rows[0].clone());
        let mut unknown = rows.clone();
        unknown[0].1 = MDataValue::Nat(2);
        for bad in [wrong_identity, wrong_syntax, duplicate, unknown] {
            assert!(decode_name_argument(&Expr::mdata(bad, inner.as_ref().clone())).is_err());
        }
        assert!(decode_name_argument(&Expr::mdata(
            rows,
            Expr::const_(name.into_name(), vec![clean_kernel::Level::zero()])
        ))
        .is_err());
        assert!(
            decode_name_argument(&Expr::fvar(clean_kernel::FVarId::new(0)))
                .unwrap()
                .is_none()
        );
    }
}
