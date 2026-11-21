// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Check K3 declaration bodies against their table prefix.

pub(super) mod inductive;

use super::{
    exact_fields, index, invalid, require_natural, K3DeclarationKind, K3ExportSyntaxError,
};
use crate::ndjson::json::JsonValue;
use std::collections::HashSet;
use std::fmt::Display;

pub(super) struct Statement {
    pub(super) parameters: Vec<usize>,
    pub(super) ty: usize,
    pub(super) value: usize,
    pub(super) eligible: bool,
}

pub(super) struct CheckedBody {
    pub(super) name: usize,
    pub(super) statement: Option<Statement>,
    pub(super) inductive_members: Option<Vec<usize>>,
}

impl CheckedBody {
    fn name_only(name: usize) -> Self {
        Self {
            name,
            statement: None,
            inductive_members: None,
        }
    }
}

struct Header {
    name: usize,
    parameters: Vec<usize>,
    ty: usize,
}

impl Header {
    fn with_value(self, value: usize, eligible: bool) -> CheckedBody {
        CheckedBody {
            name: self.name,
            statement: Some(Statement {
                parameters: self.parameters,
                ty: self.ty,
                value,
                eligible,
            }),
            inductive_members: None,
        }
    }
}

#[derive(Default)]
pub(super) struct BodyCheck {
    // The name table already enforces one ID per structural name. A set of
    // IDs therefore detects repeated names without building kernel names.
    declared: HashSet<usize>,
    check_inductive: bool,
}

impl BodyCheck {
    pub(super) fn all_declarations() -> Self {
        Self {
            check_inductive: true,
            ..Self::default()
        }
    }

    pub(super) fn visit(
        &mut self,
        line: usize,
        kind: K3DeclarationKind,
        body: &JsonValue,
        explicit_names: usize,
        explicit_expressions: usize,
    ) -> Result<Option<CheckedBody>, K3ExportSyntaxError> {
        let check = BodyFields {
            line,
            kind: kind.as_str(),
            explicit_names,
            explicit_expressions,
        };
        let checked = match kind {
            K3DeclarationKind::Def => {
                let [name, params, ty, value, safety, hints, all] = exact_fields(
                    line,
                    check.kind,
                    body,
                    [
                        "name",
                        "levelParams",
                        "type",
                        "value",
                        "safety",
                        "hints",
                        "all",
                    ],
                )?;
                let header = check.header(name, params, ty)?;
                let value = check.expression("value", value)?;
                check.one_of("safety", safety, &["safe", "unsafe", "partial"])?;
                check.hints(hints)?;
                check.all(all)?;
                let eligible = matches!(safety, JsonValue::String(safety) if safety == "safe");
                header.with_value(value, eligible)
            }
            K3DeclarationKind::Thm => {
                let [name, params, ty, value, all] = exact_fields(
                    line,
                    check.kind,
                    body,
                    ["name", "levelParams", "type", "value", "all"],
                )?;
                let header = check.header(name, params, ty)?;
                let value = check.expression("value", value)?;
                check.all(all)?;
                header.with_value(value, true)
            }
            K3DeclarationKind::Opaque => {
                let [name, params, ty, value, is_unsafe, all] = exact_fields(
                    line,
                    check.kind,
                    body,
                    ["name", "levelParams", "type", "value", "isUnsafe", "all"],
                )?;
                let header = check.header(name, params, ty)?;
                let value = check.expression("value", value)?;
                check.boolean("isUnsafe", is_unsafe)?;
                check.all(all)?;
                header.with_value(value, matches!(is_unsafe, JsonValue::Bool(false)))
            }
            K3DeclarationKind::Axiom => {
                let [name, params, ty, is_unsafe] = exact_fields(
                    line,
                    check.kind,
                    body,
                    ["name", "levelParams", "type", "isUnsafe"],
                )?;
                let header = check.header(name, params, ty)?;
                check.boolean("isUnsafe", is_unsafe)?;
                CheckedBody::name_only(header.name)
            }
            K3DeclarationKind::Quot => {
                let [name, params, ty, which] = exact_fields(
                    line,
                    check.kind,
                    body,
                    ["name", "levelParams", "type", "kind"],
                )?;
                let header = check.header(name, params, ty)?;
                check.one_of("kind", which, &["type", "ctor", "lift", "ind"])?;
                CheckedBody::name_only(header.name)
            }
            K3DeclarationKind::Inductive => {
                if !self.check_inductive {
                    return Ok(None);
                }
                let names = inductive::check(&check, body)?;
                let primary = names.first().copied();
                let mut distinct = HashSet::with_capacity(names.len());
                for &name in &names {
                    if self.declared.contains(&name) || !distinct.insert(name) {
                        return Err(self.duplicate(line, name));
                    }
                }
                self.declared.extend(distinct);
                return Ok(primary.map(|name| CheckedBody {
                    name,
                    statement: None,
                    inductive_members: Some(names),
                }));
            }
        };
        if !self.declared.insert(checked.name) {
            return Err(self.duplicate(line, checked.name));
        }
        Ok(Some(checked))
    }

    fn duplicate(&self, line: usize, name: usize) -> K3ExportSyntaxError {
        let scope = if self.check_inductive {
            "the export"
        } else {
            "non-inductive records"
        };
        invalid(line, format!("name {name} is declared twice by {scope}"))
    }

    pub(super) fn checked_count(&self) -> usize {
        self.declared.len()
    }
}

struct BodyFields {
    line: usize,
    kind: &'static str,
    explicit_names: usize,
    explicit_expressions: usize,
}

impl BodyFields {
    fn member(&self, kind: &'static str) -> Self {
        Self { kind, ..*self }
    }

    fn error(&self, field: &str, reason: impl Display) -> K3ExportSyntaxError {
        invalid(self.line, format!("{}.{field} {reason}", self.kind))
    }

    fn name(&self, field: &str, value: &JsonValue) -> Result<usize, K3ExportSyntaxError> {
        let id = index(value).ok_or_else(|| self.error(field, "expects a name index"))?;
        if id > self.explicit_names {
            return Err(self.error(
                field,
                format_args!("cites name {id}, which is not defined by an earlier row"),
            ));
        }
        Ok(id)
    }

    fn name_array<'value>(
        &self,
        field: &str,
        value: &'value JsonValue,
    ) -> Result<&'value [JsonValue], K3ExportSyntaxError> {
        match value {
            JsonValue::Array(items) => Ok(items),
            _ => Err(self.error(field, "expects an array of name indices")),
        }
    }

    fn expression(&self, field: &str, value: &JsonValue) -> Result<usize, K3ExportSyntaxError> {
        let id = index(value).ok_or_else(|| self.error(field, "expects an expression index"))?;
        if id >= self.explicit_expressions {
            return Err(self.error(
                field,
                format_args!("cites expression {id}, which is not defined by an earlier row"),
            ));
        }
        Ok(id)
    }

    fn header(
        &self,
        name: &JsonValue,
        params: &JsonValue,
        ty: &JsonValue,
    ) -> Result<Header, K3ExportSyntaxError> {
        Ok(Header {
            name: self.name("name", name)?,
            parameters: self.level_params(params)?,
            ty: self.expression("type", ty)?,
        })
    }

    fn level_params(&self, value: &JsonValue) -> Result<Vec<usize>, K3ExportSyntaxError> {
        let params = self.name_array("levelParams", value)?;
        let mut ids = Vec::with_capacity(params.len());
        let mut known_params = HashSet::new();
        for param in params {
            let id = self.name("levelParams", param)?;
            if !known_params.insert(id) {
                return Err(self.error("levelParams", "has a level parameter listed twice"));
            }
            ids.push(id);
        }
        Ok(ids)
    }

    fn all(&self, value: &JsonValue) -> Result<(), K3ExportSyntaxError> {
        for name in self.name_array("all", value)? {
            self.name("all", name)?;
        }
        Ok(())
    }

    fn boolean(&self, field: &str, value: &JsonValue) -> Result<(), K3ExportSyntaxError> {
        if matches!(value, JsonValue::Bool(_)) {
            Ok(())
        } else {
            Err(self.error(field, "expects a boolean"))
        }
    }

    fn one_of(
        &self,
        field: &str,
        value: &JsonValue,
        tags: &[&str],
    ) -> Result<(), K3ExportSyntaxError> {
        if matches!(value, JsonValue::String(tag) if tags.contains(&tag.as_str())) {
            Ok(())
        } else {
            Err(self.error(field, format_args!("expects one of {}", tags.join(", "))))
        }
    }

    fn hints(&self, value: &JsonValue) -> Result<(), K3ExportSyntaxError> {
        match value {
            JsonValue::String(hint) if matches!(hint.as_str(), "opaque" | "abbrev") => Ok(()),
            JsonValue::Object(_) => {
                let [height] = exact_fields(self.line, "def.hints", value, ["regular"])?;
                require_natural(self.line, "def.hints.regular", height)
            }
            _ => Err(self.error(
                "hints",
                "expects opaque, abbrev or an object with a regular field",
            )),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ndjson::json::parse_line;
    use K3DeclarationKind::{Axiom, Def, Inductive, Opaque, Quot, Thm};

    fn visit(
        check: &mut BodyCheck,
        kind: K3DeclarationKind,
        text: &str,
        names: usize,
        expressions: usize,
    ) -> Result<(), K3ExportSyntaxError> {
        let body = parse_line(text.as_bytes()).expect("JSON fixture");
        check
            .visit(138, kind, &body, names, expressions)
            .map(|_| ())
    }

    fn expect_invalid(
        check: &mut BodyCheck,
        kind: K3DeclarationKind,
        text: &str,
        names: usize,
        expressions: usize,
        needle: &str,
    ) {
        let before = check.checked_count();
        let Err(K3ExportSyntaxError::Invalid { line, reason }) =
            visit(check, kind, text, names, expressions)
        else {
            panic!("expected a K3 refusal for {text}");
        };
        assert_eq!(line, 138);
        assert!(reason.contains(needle), "{text}: {reason}");
        assert_eq!(check.checked_count(), before);
    }

    #[test]
    fn accepts_all_non_inductive_kinds_with_raw_hint_and_name_domains() {
        let mut check = BodyCheck::default();
        for (kind, body) in [
            (
                Def,
                r#"{"all":[0,5,5],"hints":{"regular":18446744073709551616},"safety":"partial","value":0,"type":1,"name":0,"levelParams":[0,2]}"#,
            ),
            (
                Def,
                r#"{"name":1,"levelParams":[],"type":0,"value":0,"safety":"unsafe","hints":"opaque","all":[]}"#,
            ),
            (
                Def,
                r#"{"name":2,"levelParams":[],"type":0,"value":0,"safety":"safe","hints":"abbrev","all":[]}"#,
            ),
            (
                Thm,
                r#"{"name":3,"levelParams":[],"type":0,"value":1,"all":[]}"#,
            ),
            (
                Opaque,
                r#"{"name":4,"levelParams":[],"type":0,"value":0,"isUnsafe":true,"all":[3]}"#,
            ),
            (
                Axiom,
                r#"{"name":5,"levelParams":[],"type":0,"isUnsafe":false}"#,
            ),
            (
                Quot,
                r#"{"name":6,"levelParams":[],"type":0,"kind":"ctor"}"#,
            ),
        ] {
            visit(&mut check, kind, body, 6, 2).expect("valid declaration body");
        }
        assert_eq!(check.checked_count(), 7);
    }

    #[test]
    fn refuses_wrong_body_shapes_values_and_tags() {
        let mut check = BodyCheck::default();
        for (kind, body, needle) in [
            (
                Axiom,
                r#"{"name":1,"levelParams":[],"type":0,"isUnsafe":false,"extra":0}"#,
                "exactly the fields",
            ),
            (
                Opaque,
                r#"{"name":1,"levelParams":[],"type":0,"value":0,"all":[]}"#,
                "exactly the fields",
            ),
            (
                Axiom,
                r#"{"name":1,"levelParams":[],"type":0,"isUnsafe":0}"#,
                "expects a boolean",
            ),
            (
                Thm,
                r#"{"name":1,"levelParams":[],"type":0,"value":0,"all":{}}"#,
                "all expects an array",
            ),
            (
                Def,
                r#"{"name":1,"levelParams":[],"type":0,"value":0,"safety":"permissive","hints":"opaque","all":[]}"#,
                "def.safety",
            ),
            (
                Def,
                r#"{"name":1,"levelParams":[],"type":0,"value":0,"safety":"safe","hints":{"regular":0,"extra":0},"all":[]}"#,
                "def.hints",
            ),
            (
                Def,
                r#"{"name":1,"levelParams":[],"type":0,"value":0,"safety":"safe","hints":{"regular":false},"all":[]}"#,
                "expects a natural number",
            ),
            (
                Quot,
                r#"{"name":1,"levelParams":[],"type":0,"kind":"mk"}"#,
                "quot.kind",
            ),
        ] {
            expect_invalid(&mut check, kind, body, 1, 1, needle);
        }
    }

    #[test]
    fn checks_prefix_bounds_and_duplicate_parameters_or_declarations() {
        let mut check = BodyCheck::default();
        for (kind, body, names, expressions, needle) in [
            (
                Axiom,
                r#"{"name":27,"levelParams":[],"type":0,"isUnsafe":false}"#,
                26,
                1,
                "name 27",
            ),
            (
                Axiom,
                r#"{"name":1,"levelParams":[],"type":0,"isUnsafe":false}"#,
                1,
                0,
                "expression 0",
            ),
            (
                Axiom,
                r#"{"name":1,"levelParams":[2],"type":0,"isUnsafe":false}"#,
                1,
                1,
                "levelParams",
            ),
            (
                Axiom,
                r#"{"name":1,"levelParams":[0,0],"type":0,"isUnsafe":false}"#,
                1,
                1,
                "listed twice",
            ),
            (
                Thm,
                r#"{"name":1,"levelParams":[],"type":0,"value":100,"all":[]}"#,
                1,
                100,
                "expression 100",
            ),
            (
                Thm,
                r#"{"name":1,"levelParams":[],"type":0,"value":0,"all":[2]}"#,
                1,
                1,
                "all",
            ),
        ] {
            expect_invalid(&mut check, kind, body, names, expressions, needle);
        }
        visit(
            &mut check,
            Inductive,
            r#"{"types":[],"ctors":[],"recs":[]}"#,
            0,
            0,
        )
        .unwrap();
        assert_eq!(check.checked_count(), 0);
        visit(
            &mut check,
            Axiom,
            r#"{"name":1,"levelParams":[],"type":0,"isUnsafe":false}"#,
            1,
            1,
        )
        .unwrap();
        expect_invalid(
            &mut check,
            Quot,
            r#"{"name":1,"levelParams":[],"type":0,"kind":"lift"}"#,
            1,
            1,
            "declared twice",
        );
    }
}
