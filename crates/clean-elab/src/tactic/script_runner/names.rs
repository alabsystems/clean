//! Source-token boundaries for the deliberately small script dispatcher.

use super::elab_tactic::TacticError;
use clean_parser::SurfaceName;

/// Split only at separators outside quoted names and string literals.
pub(super) fn words(input: &str, list: bool) -> Result<Vec<&str>, TacticError> {
    let mut result = Vec::new();
    let mut start = None;
    let mut quoted = false;
    let mut string = false;
    let mut escaped = false;
    for (offset, ch) in input.char_indices() {
        if quoted {
            if ch == '»' {
                quoted = false;
            }
        } else if string {
            if escaped {
                escaped = false;
            } else if ch == '\\' {
                escaped = true;
            } else if ch == '"' {
                string = false;
            }
        } else if ch.is_whitespace() || (list && matches!(ch, '[' | ']' | ',')) {
            if let Some(from) = start.take() {
                result.push(&input[from..offset]);
            }
            continue;
        } else if ch == '«' {
            quoted = true;
        } else if ch == '"' {
            string = true;
        }
        start.get_or_insert(offset);
    }
    if quoted || string {
        return Err(TacticError::ParseFailed {
            tactic: "script".into(),
            detail: "unterminated quoted identifier or string".into(),
        });
    }
    if let Some(from) = start {
        result.push(&input[from..]);
    }
    Ok(result)
}

pub(super) fn name(raw: &str) -> Result<SurfaceName, TacticError> {
    let name = clean_parser::parse_name(raw).map_err(|error| TacticError::ParseFailed {
        tactic: "script identifier".into(),
        detail: error.to_string(),
    })?;
    if name.is_relative_constructor() || name.is_anonymous() {
        return Err(TacticError::ParseFailed {
            tactic: "script identifier".into(),
            detail: "expected a non-relative identifier".into(),
        });
    }
    Ok(name)
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::Name;

    #[test]
    fn quoted_name_separators_and_numeric_identity_are_not_retokenized() {
        let tokens = words("intro «A B;--/-C»", false).unwrap();
        assert_eq!(tokens, ["intro", "«A B;--/-C»"]);
        assert_eq!(
            name(tokens[1]).unwrap().name(),
            &Name::anon().str("A B;--/-C")
        );
        assert_ne!(name("«7»").unwrap().name(), &Name::anon().num(7));
        assert_ne!(name("«A.B»").unwrap(), name("A.B").unwrap());
        assert!(words("intro «unterminated", false).is_err());
        assert!(name("x y").is_err());
        assert!(name(".ctor").is_err());
    }

    #[test]
    fn lemma_list_separators_inside_quoted_identifiers_remain_one_component() {
        let tokens = words("[«a,b] c», A.B]", true).unwrap();
        assert_eq!(tokens, ["«a,b] c»", "A.B"]);
        assert_eq!(name(tokens[0]).unwrap().name(), &Name::anon().str("a,b] c"));
    }
}
