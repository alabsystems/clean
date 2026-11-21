// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Check inductive member rows and the block's constructor roster.

use super::{BodyFields, JsonValue, K3ExportSyntaxError};
use crate::k3_export_syntax::{exact_fields, invalid, require_natural};

// The canonical base digest uses this same order, independent of JSON key order.
pub(in crate::k3_export_syntax) const BLOCK_KEYS: [&str; 3] = ["types", "ctors", "recs"];
pub(in crate::k3_export_syntax) const TYPE_KEYS: [&str; 11] = [
    "name",
    "levelParams",
    "type",
    "numParams",
    "numIndices",
    "all",
    "ctors",
    "numNested",
    "isRec",
    "isUnsafe",
    "isReflexive",
];
pub(in crate::k3_export_syntax) const CTOR_KEYS: [&str; 8] = [
    "name",
    "levelParams",
    "type",
    "induct",
    "cidx",
    "numParams",
    "numFields",
    "isUnsafe",
];
pub(in crate::k3_export_syntax) const REC_KEYS: [&str; 11] = [
    "name",
    "levelParams",
    "type",
    "all",
    "numParams",
    "numIndices",
    "numMotives",
    "numMinors",
    "rules",
    "k",
    "isUnsafe",
];
pub(in crate::k3_export_syntax) const RULE_KEYS: [&str; 3] = ["ctor", "nfields", "rhs"];

struct TypeRow<'row> {
    name: usize,
    level_params: Vec<usize>,
    // Already checked as a canonical natural, so equality compares its full
    // spelling without limiting the count to a machine-sized integer.
    num_params: &'row JsonValue,
    ctors: Vec<usize>,
}

struct CtorRow {
    name: usize,
    level_params: Vec<usize>,
    owner: usize,
}

pub(super) fn check(
    fields: &BodyFields,
    body: &JsonValue,
) -> Result<Vec<usize>, K3ExportSyntaxError> {
    let [types, ctors, recs] = exact_fields(fields.line, "inductive", body, BLOCK_KEYS)?;
    let types = array(fields, "types", types)?;
    let ctors = array(fields, "ctors", ctors)?;
    let recs = array(fields, "recs", recs)?;

    let type_fields = fields.member("inductive.types");
    let types = types
        .iter()
        .map(|row| type_row(&type_fields, row))
        .collect::<Result<Vec<_>, _>>()?;
    let ctor_fields = fields.member("inductive.ctors");
    let ctors = ctors
        .iter()
        .map(|row| ctor_row(&ctor_fields, row))
        .collect::<Result<Vec<_>, _>>()?;
    let rec_fields = fields.member("inductive.recs");
    let recs = recs
        .iter()
        .map(|row| rec_row(&rec_fields, row))
        .collect::<Result<Vec<_>, _>>()?;

    let first = types
        .first()
        .ok_or_else(|| invalid(fields.line, "inductive record has no type"))?;
    for ty in &types[1..] {
        if ty.level_params != first.level_params {
            return Err(invalid(
                fields.line,
                "inductive types state different level parameters",
            ));
        }
        if ty.num_params != first.num_params {
            return Err(invalid(
                fields.line,
                "inductive types state different numParams",
            ));
        }
    }
    for ctor in &ctors {
        if ctor.level_params != first.level_params {
            return Err(invalid(
                fields.line,
                "inductive constructor level parameters differ from the types' level parameters",
            ));
        }
    }
    let listed = types
        .iter()
        .flat_map(|ty| ty.ctors.iter().map(move |&ctor| (ctor, ty.name)));
    let supplied = ctors.iter().map(|ctor| (ctor.name, ctor.owner));
    if !listed.eq(supplied) {
        return Err(invalid(
            fields.line,
            "inductive constructors are not the types' ctors lists in order",
        ));
    }

    Ok(types
        .into_iter()
        .map(|ty| ty.name)
        .chain(ctors.into_iter().map(|ctor| ctor.name))
        .chain(recs)
        .collect())
}

fn array<'row>(
    fields: &BodyFields,
    key: &str,
    value: &'row JsonValue,
) -> Result<&'row [JsonValue], K3ExportSyntaxError> {
    match value {
        JsonValue::Array(items) => Ok(items),
        _ => Err(fields.error(key, "expects an array")),
    }
}

fn type_row<'row>(
    fields: &BodyFields,
    row: &'row JsonValue,
) -> Result<TypeRow<'row>, K3ExportSyntaxError> {
    let [name, level_params, ty, num_params, num_indices, all, ctors, num_nested, is_rec, is_unsafe, is_reflexive] =
        exact_fields(fields.line, fields.kind, row, TYPE_KEYS)?;
    let name = fields.name("name", name)?;
    let level_params = fields.level_params(level_params)?;
    fields.expression("type", ty)?;
    require_natural(fields.line, "inductive.types.numParams", num_params)?;
    require_natural(fields.line, "inductive.types.numIndices", num_indices)?;
    fields.all(all)?;
    let ctors = fields
        .name_array("ctors", ctors)?
        .iter()
        .map(|ctor| fields.name("ctors", ctor))
        .collect::<Result<Vec<_>, _>>()?;
    require_natural(fields.line, "inductive.types.numNested", num_nested)?;
    fields.boolean("isRec", is_rec)?;
    fields.boolean("isUnsafe", is_unsafe)?;
    fields.boolean("isReflexive", is_reflexive)?;
    Ok(TypeRow {
        name,
        level_params,
        num_params,
        ctors,
    })
}

fn ctor_row(fields: &BodyFields, row: &JsonValue) -> Result<CtorRow, K3ExportSyntaxError> {
    let [name, level_params, ty, owner, cidx, num_params, num_fields, is_unsafe] =
        exact_fields(fields.line, fields.kind, row, CTOR_KEYS)?;
    let name = fields.name("name", name)?;
    let level_params = fields.level_params(level_params)?;
    fields.expression("type", ty)?;
    let owner = fields.name("induct", owner)?;
    require_natural(fields.line, "inductive.ctors.cidx", cidx)?;
    require_natural(fields.line, "inductive.ctors.numParams", num_params)?;
    require_natural(fields.line, "inductive.ctors.numFields", num_fields)?;
    fields.boolean("isUnsafe", is_unsafe)?;
    Ok(CtorRow {
        name,
        level_params,
        owner,
    })
}

fn rec_row(fields: &BodyFields, row: &JsonValue) -> Result<usize, K3ExportSyntaxError> {
    let [name, level_params, ty, all, num_params, num_indices, num_motives, num_minors, rules, k, is_unsafe] =
        exact_fields(fields.line, fields.kind, row, REC_KEYS)?;
    let header = fields.header(name, level_params, ty)?;
    fields.all(all)?;
    require_natural(fields.line, "inductive.recs.numParams", num_params)?;
    require_natural(fields.line, "inductive.recs.numIndices", num_indices)?;
    require_natural(fields.line, "inductive.recs.numMotives", num_motives)?;
    require_natural(fields.line, "inductive.recs.numMinors", num_minors)?;
    let rule_fields = fields.member("inductive.recs.rules");
    for rule in array(fields, "rules", rules)? {
        let [ctor, nfields, rhs] =
            exact_fields(rule_fields.line, rule_fields.kind, rule, RULE_KEYS)?;
        rule_fields.name("ctor", ctor)?;
        require_natural(rule_fields.line, "inductive.recs.rules.nfields", nfields)?;
        rule_fields.expression("rhs", rhs)?;
    }
    fields.boolean("k", k)?;
    fields.boolean("isUnsafe", is_unsafe)?;
    Ok(header.name)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ndjson::json::parse_line;

    fn type_fixture(name: usize, ctors: &str) -> String {
        format!(
            concat!(
                r#"{{"name":{},"levelParams":[7,8],"type":0,"numParams":18446744073709551616,"#,
                r#""numIndices":0,"all":[1,1],"ctors":[{}],"numNested":1,"#,
                r#""isRec":true,"isUnsafe":false,"isReflexive":false}}"#
            ),
            name, ctors,
        )
    }

    fn ctor_fixture(name: usize, owner: usize) -> String {
        format!(
            concat!(
                r#"{{"name":{},"levelParams":[7,8],"type":0,"induct":{},"cidx":0,"#,
                r#""numParams":0,"numFields":18446744073709551616,"isUnsafe":false}}"#
            ),
            name, owner,
        )
    }

    const REC: &str = concat!(
        r#"{"name":6,"levelParams":[8,7],"type":0,"all":[],"numParams":0,"numIndices":0,"#,
        r#""numMotives":0,"numMinors":0,"rules":[{"ctor":9,"nfields":18446744073709551616,"rhs":1},"#,
        r#"{"ctor":9,"nfields":18446744073709551616,"rhs":1}],"k":false,"isUnsafe":false}"#
    );

    fn block(types: &[&str], ctors: &[&str], recs: &[&str]) -> String {
        format!(
            r#"{{"types":[{}],"ctors":[{}],"recs":[{}]}}"#,
            types.join(","),
            ctors.join(","),
            recs.join(","),
        )
    }

    fn mutual_block() -> String {
        block(
            &[&type_fixture(1, "3,4"), &type_fixture(2, "5")],
            &[
                &ctor_fixture(3, 1),
                &ctor_fixture(4, 1),
                &ctor_fixture(5, 2),
            ],
            &[REC],
        )
    }

    fn visit(text: &str) -> Result<Vec<usize>, K3ExportSyntaxError> {
        let body = parse_line(text.as_bytes()).expect("JSON fixture");
        check(
            &BodyFields {
                line: 20,
                kind: "inductive",
                explicit_names: 9,
                explicit_expressions: 2,
            },
            &body,
        )
    }

    fn expect_refusal(text: &str, expected: &str) {
        let Err(K3ExportSyntaxError::Invalid { line, reason }) = visit(text) else {
            panic!("expected refusal for {text}");
        };
        assert_eq!(line, 20);
        assert!(reason.contains(expected), "{expected}: {reason}");
    }

    #[test]
    fn accepts_group_order_and_independent_recursor_fields() {
        // This block uses wide counts, ordered mutual parameters, repeated
        // all entries, and repeated recursor rules about an earlier name
        // outside the block's constructor roster.
        assert_eq!(visit(&mutual_block()).unwrap(), [1, 2, 3, 4, 5, 6]);
        let empty_roster = block(&[&type_fixture(1, "")], &[], &[]);
        assert_eq!(visit(&empty_roster).unwrap(), [1]);
    }

    #[test]
    fn requires_exact_groups_and_member_objects() {
        expect_refusal(r#"{"types":[],"ctors":[],"recs":[]}"#, "no type");
        expect_refusal(r#"{"types":[],"ctors":[]}"#, "exactly the fields");
        expect_refusal(
            r#"{"types":[],"ctors":0,"recs":[]}"#,
            "ctors expects an array",
        );
        let text = mutual_block();
        for (from, to, expected) in [
            (
                r#","isReflexive":false"#,
                "",
                "inductive.types expects exactly",
            ),
            (
                r#""cidx":0"#,
                r#""cidx":0,"extra":0"#,
                "inductive.ctors expects exactly",
            ),
            (
                r#""numMinors":0"#,
                r#""extra":0"#,
                "inductive.recs expects exactly",
            ),
            (
                r#","nfields":18446744073709551616"#,
                "",
                "inductive.recs.rules expects exactly",
            ),
        ] {
            expect_refusal(&text.replacen(from, to, 1), expected);
        }
    }

    #[test]
    fn checks_member_field_kinds_and_prefix_references() {
        let text = mutual_block();
        for (from, to, expected) in [
            (
                r#""name":1"#,
                r#""name":10"#,
                "inductive.types.name cites name 10",
            ),
            (
                r#""type":0"#,
                r#""type":2"#,
                "inductive.types.type cites expression 2",
            ),
            (
                r#""numNested":1"#,
                r#""numNested":true"#,
                "inductive.types.numNested expects a natural",
            ),
            (
                r#""isReflexive":false"#,
                r#""isReflexive":0"#,
                "inductive.types.isReflexive expects a boolean",
            ),
            (
                r#""induct":1"#,
                r#""induct":10"#,
                "inductive.ctors.induct cites name 10",
            ),
            (
                r#""levelParams":[8,7]"#,
                r#""levelParams":[8,8]"#,
                "inductive.recs.levelParams has a level parameter listed twice",
            ),
            (
                r#""ctor":9"#,
                r#""ctor":10"#,
                "inductive.recs.rules.ctor cites name 10",
            ),
            (
                r#""rhs":1"#,
                r#""rhs":2"#,
                "inductive.recs.rules.rhs cites expression 2",
            ),
        ] {
            expect_refusal(&text.replacen(from, to, 1), expected);
        }
    }

    #[test]
    fn enforces_ordered_shared_parameters_and_exact_constructor_roster() {
        let text = mutual_block();
        expect_refusal(
            &text.replacen(
                r#""name":2,"levelParams":[7,8]"#,
                r#""name":2,"levelParams":[8,7]"#,
                1,
            ),
            "types state different level parameters",
        );
        expect_refusal(
            &text.replacen("18446744073709551616", "18446744073709551617", 1),
            "types state different numParams",
        );
        expect_refusal(
            &text.replacen(
                r#""name":3,"levelParams":[7,8]"#,
                r#""name":3,"levelParams":[8,7]"#,
                1,
            ),
            "constructor level parameters differ",
        );
        for (from, to) in [
            (r#""ctors":[3,4]"#, r#""ctors":[4,3]"#),
            (r#""ctors":[3,4]"#, r#""ctors":[3]"#),
            (r#""induct":1"#, r#""induct":2"#),
        ] {
            expect_refusal(
                &text.replacen(from, to, 1),
                "constructors are not the types' ctors lists in order",
            );
        }
    }
}
