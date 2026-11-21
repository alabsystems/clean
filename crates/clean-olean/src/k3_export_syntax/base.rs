// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Recognise the three pinned K3 base families by their canonical block digest.

use super::{
    bodies::inductive::{BLOCK_KEYS, CTOR_KEYS, REC_KEYS, RULE_KEYS, TYPE_KEYS},
    exact_fields,
    expressions::ExprRow,
    index,
    levels::LevelRow,
    names::NameTable,
    statement_echo::{write_expression, EchoOutput},
};
use crate::ndjson::json::JsonValue;
use sha2::{Digest, Sha256};
use std::collections::HashMap;
use std::fmt::{self, Write};

struct Family {
    name: &'static str,
    bytes: usize,
    digest: [u8; 32],
}

// The SHA-256 pins are from Raw.block_text in scripts/kcheck_coverage_export.py.
// These byte lengths also bound the work of emitting each candidate.
const FAMILIES: [Family; 3] = [
    Family {
        name: "[s3:Nat]",
        bytes: 1286,
        digest: [
            0x58, 0xbb, 0x6e, 0x44, 0xd8, 0x1e, 0xe4, 0x06, 0xa9, 0x7d, 0x6c, 0x44, 0x17, 0xb0,
            0xf0, 0x4d, 0xce, 0xe3, 0x61, 0x23, 0x3f, 0x25, 0xb6, 0x81, 0x61, 0xab, 0xe6, 0x3a,
            0x24, 0x27, 0x8e, 0xc5,
        ],
    },
    Family {
        name: "[s5:PUnit]",
        bytes: 715,
        digest: [
            0xfe, 0x62, 0x5f, 0xa3, 0x2f, 0x92, 0xa4, 0x3d, 0xb0, 0x42, 0xe6, 0x3b, 0xe9, 0xb1,
            0x72, 0x0d, 0x4a, 0x6b, 0xe1, 0x42, 0xdd, 0x5c, 0x02, 0x19, 0xe2, 0xd8, 0x6a, 0x01,
            0xcf, 0xee, 0xe6, 0xee,
        ],
    },
    Family {
        name: "[s2:Eq]",
        bytes: 1058,
        digest: [
            0x86, 0x4c, 0x55, 0xfd, 0x97, 0xbf, 0x5b, 0x5f, 0xb8, 0x2d, 0xe4, 0xa1, 0x21, 0x41,
            0x95, 0x1d, 0xae, 0x77, 0x1d, 0x12, 0x77, 0x22, 0xa0, 0x33, 0x96, 0x3b, 0x96, 0x8d,
            0x19, 0x31, 0xc6, 0x8d,
        ],
    },
];

pub(super) fn recognises(
    name: usize,
    body: &JsonValue,
    names: &NameTable,
    levels: &[LevelRow],
    expressions: &[ExprRow],
) -> bool {
    let Some(family) = FAMILIES
        .iter()
        .find(|family| names.matches_echo(name, family.name))
    else {
        return false;
    };
    let tables = EchoTables {
        names,
        levels,
        expressions,
    };
    let mut out = DigestOutput {
        digest: Sha256::new(),
        remaining: family.bytes,
    };
    if tables.write_block(name, body, &mut out).is_err() || out.remaining != 0 {
        return false;
    }
    let digest: [u8; 32] = out.digest.finalize().into();
    digest == family.digest
}

struct DigestOutput {
    digest: Sha256,
    remaining: usize,
}

impl Write for DigestOutput {
    fn write_str(&mut self, text: &str) -> fmt::Result {
        self.remaining = self.remaining.checked_sub(text.len()).ok_or(fmt::Error)?;
        self.digest.update(text.as_bytes());
        Ok(())
    }
}

impl EchoOutput for DigestOutput {
    fn remaining(&self) -> usize {
        self.remaining
    }
}

struct EchoTables<'export> {
    names: &'export NameTable,
    levels: &'export [LevelRow],
    expressions: &'export [ExprRow],
}

impl EchoTables<'_> {
    fn write_block(&self, name: usize, body: &JsonValue, out: &mut impl EchoOutput) -> fmt::Result {
        let [types, ctors, recs] = fields(body, BLOCK_KEYS)?;
        let first = array(types)?.first().ok_or(fmt::Error)?;
        let [primary_name, parameters, ..] = fields(first, TYPE_KEYS)?;
        if id(primary_name)? != name {
            return Err(fmt::Error);
        }
        let own = self.scope(parameters, out.remaining())?;
        let [type_group, ctor_group, rec_group] = BLOCK_KEYS;
        self.write_group(type_group, types, TYPE_KEYS, &own, out)?;
        self.write_group(ctor_group, ctors, CTOR_KEYS, &own, out)?;
        self.write_group(rec_group, recs, REC_KEYS, &own, out)
    }

    fn write_group<const N: usize>(
        &self,
        group: &str,
        rows: &JsonValue,
        keys: [&str; N],
        own: &HashMap<usize, usize>,
        out: &mut impl EchoOutput,
    ) -> fmt::Result {
        for row in array(rows)? {
            let values = fields(row, keys)?;
            let parameters = keys
                .iter()
                .zip(values)
                .find_map(|(&key, value)| (key == "levelParams").then_some(value))
                .ok_or(fmt::Error)?;
            out.write_str(group)?;
            let scope = self.scope(parameters, out.remaining())?;
            for (key, value) in keys.into_iter().zip(values) {
                write!(out, "\t{key}=")?;
                self.write_field(key, value, own, &scope, out)?;
            }
            out.write_char('\n')?;
        }
        Ok(())
    }

    fn scope(
        &self,
        parameters: &JsonValue,
        budget: usize,
    ) -> Result<HashMap<usize, usize>, fmt::Error> {
        let parameters = array(parameters)?;
        // Each parameter emits at least one byte, including a foreign one.
        if parameters.len() > budget {
            return Err(fmt::Error);
        }
        let mut scope = HashMap::with_capacity(parameters.len());
        for (position, value) in parameters.iter().enumerate() {
            let name = id(value)?;
            if name > self.names.explicit_count() || scope.insert(name, position).is_some() {
                return Err(fmt::Error);
            }
        }
        Ok(scope)
    }

    fn write_field(
        &self,
        key: &str,
        value: &JsonValue,
        own: &HashMap<usize, usize>,
        scope: &HashMap<usize, usize>,
        out: &mut impl EchoOutput,
    ) -> fmt::Result {
        match key {
            "name" | "induct" => self.names.write_echo(id(value)?, out),
            "all" | "ctors" => {
                out.write_char('[')?;
                for (position, value) in array(value)?.iter().enumerate() {
                    if position != 0 {
                        out.write_char(',')?;
                    }
                    self.names.write_echo(id(value)?, out)?;
                }
                out.write_char(']')
            }
            "levelParams" => {
                for (position, value) in array(value)?.iter().enumerate() {
                    if position != 0 {
                        out.write_char(',')?;
                    }
                    match own.get(&id(value)?) {
                        Some(position) => write!(out, "t{position}")?,
                        None => out.write_char('e')?,
                    }
                }
                Ok(())
            }
            "type" => self.write_expr(value, scope, out),
            "rules" => self.write_rules(value, scope, out),
            "numParams" | "numIndices" | "numNested" | "cidx" | "numFields" | "numMotives"
            | "numMinors" => out.write_str(natural_text(value)?),
            "isRec" | "isUnsafe" | "isReflexive" | "k" => match value {
                JsonValue::Bool(true) => out.write_str("true"),
                JsonValue::Bool(false) => out.write_str("false"),
                _ => Err(fmt::Error),
            },
            _ => Err(fmt::Error),
        }
    }

    fn write_rules(
        &self,
        value: &JsonValue,
        scope: &HashMap<usize, usize>,
        out: &mut impl EchoOutput,
    ) -> fmt::Result {
        for (position, rule) in array(value)?.iter().enumerate() {
            if position != 0 {
                out.write_char(';')?;
            }
            let [ctor, nfields, rhs] = fields(rule, RULE_KEYS)?;
            self.names.write_echo(id(ctor)?, out)?;
            write!(out, " {} ", natural_text(nfields)?)?;
            self.write_expr(rhs, scope, out)?;
        }
        Ok(())
    }

    fn write_expr(
        &self,
        value: &JsonValue,
        scope: &HashMap<usize, usize>,
        out: &mut impl EchoOutput,
    ) -> fmt::Result {
        write_expression(
            self.names,
            self.levels,
            self.expressions,
            scope,
            id(value)?,
            out,
        )
    }
}

fn fields<'row, const N: usize>(
    row: &'row JsonValue,
    keys: [&str; N],
) -> Result<[&'row JsonValue; N], fmt::Error> {
    exact_fields(0, "base block", row, keys).map_err(|_| fmt::Error)
}

fn array(value: &JsonValue) -> Result<&[JsonValue], fmt::Error> {
    match value {
        JsonValue::Array(values) => Ok(values),
        _ => Err(fmt::Error),
    }
}

fn id(value: &JsonValue) -> Result<usize, fmt::Error> {
    index(value).ok_or(fmt::Error)
}

fn natural_text(value: &JsonValue) -> Result<&str, fmt::Error> {
    match value {
        JsonValue::Number(number) if number.canonical_natural => Ok(&number.text),
        _ => Err(fmt::Error),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ndjson::json::parse_line;

    struct TextOutput {
        text: String,
        limit: usize,
    }

    impl Write for TextOutput {
        fn write_str(&mut self, text: &str) -> fmt::Result {
            if text.len() > self.remaining() {
                return Err(fmt::Error);
            }
            self.text.push_str(text);
            Ok(())
        }
    }

    impl EchoOutput for TextOutput {
        fn remaining(&self) -> usize {
            self.limit - self.text.len()
        }
    }

    #[test]
    fn canonical_bytes_use_schema_order_and_each_rows_parameter_scope() {
        let mut names = NameTable::default();
        for (line, row) in [
            r#"{"in":1,"str":{"pre":0,"str":"Nat"}}"#,
            r#"{"in":2,"str":{"pre":1,"str":"zero"}}"#,
            r#"{"in":3,"str":{"pre":1,"str":"rec"}}"#,
            r#"{"in":4,"str":{"pre":0,"str":"u"}}"#,
            r#"{"in":5,"str":{"pre":0,"str":"v"}}"#,
            r#"{"in":6,"str":{"pre":0,"str":"π]"}}"#,
        ]
        .into_iter()
        .enumerate()
        {
            let JsonValue::Object(entries) = parse_line(row.as_bytes()).unwrap() else {
                panic!("a name fixture must be a JSON object");
            };
            names.visit(line + 2, entries).unwrap();
        }
        let data = concat!(
            r#"{"recs":[{"name":3,"levelParams":[5,4],"type":3,"all":[1,1],"numParams":0,"numIndices":0,"#,
            r#""numMotives":1,"numMinors":1,"rules":[{"rhs":1,"nfields":0,"ctor":2},"#,
            r#"{"ctor":6,"nfields":18446744073709551616,"rhs":3}],"k":true,"isUnsafe":false}],"#,
            r#""ctors":[{"isUnsafe":false,"name":2,"levelParams":[4],"type":1,"induct":1,"cidx":0,"numParams":0,"numFields":0}],"#,
            r#""types":[{"numParams":0,"levelParams":[4],"name":1,"type":1,"all":[1],"ctors":[2],"#,
            r#""numIndices":0,"numNested":0,"isRec":true,"isUnsafe":false,"isReflexive":false}]}"#
        );
        let body = parse_line(data.as_bytes()).unwrap();
        let levels = [LevelRow::Zero, LevelRow::Param(4), LevelRow::Param(5)];
        let expressions = [
            ExprRow::Sort(0),
            ExprRow::Sort(1),
            ExprRow::Sort(2),
            ExprRow::MData(2),
        ];
        let tables = EchoTables {
            names: &names,
            levels: &levels,
            expressions: &expressions,
        };
        let expected = concat!(
            "types\tname=[s3:Nat]\tlevelParams=t0\ttype=(sort (p 0))\tnumParams=0\tnumIndices=0",
            "\tall=[[s3:Nat]]\tctors=[[s3:Nat s4:zero]]\tnumNested=0\tisRec=true\tisUnsafe=false\tisReflexive=false\n",
            "ctors\tname=[s3:Nat s4:zero]\tlevelParams=t0\ttype=(sort (p 0))\tinduct=[s3:Nat]",
            "\tcidx=0\tnumParams=0\tnumFields=0\tisUnsafe=false\n",
            "recs\tname=[s3:Nat s3:rec]\tlevelParams=e,t0\ttype=(sort (p 0))\tall=[[s3:Nat],[s3:Nat]]",
            "\tnumParams=0\tnumIndices=0\tnumMotives=1\tnumMinors=1\trules=[s3:Nat s4:zero] 0 (sort (p 1));",
            "[s3:π]] 18446744073709551616 (sort (p 0))\tk=true\tisUnsafe=false\n",
        );
        let mut actual = TextOutput {
            text: String::new(),
            limit: expected.len(),
        };
        tables.write_block(1, &body, &mut actual).unwrap();
        assert_eq!(actual.text, expected);
        assert!(!recognises(1, &body, &names, &levels, &expressions));

        let mut short = TextOutput {
            text: String::new(),
            limit: expected.len() - 1,
        };
        assert!(tables.write_block(1, &body, &mut short).is_err());
        actual.text.clear();
        assert!(tables.write_block(2, &body, &mut actual).is_err());
        assert!(actual.text.is_empty());

        let data = data.replace("[5,4]", "[5]");
        let unscoped = parse_line(data.as_bytes()).unwrap();
        assert!(tables.write_block(1, &unscoped, &mut actual).is_err());
    }

    #[test]
    fn digest_output_bounds_and_hashes_utf8_bytes() {
        let expected = "πx";
        let mut out = DigestOutput {
            digest: Sha256::new(),
            remaining: 3,
        };
        assert!(out.write_str("ππ").is_err());
        assert_eq!(out.remaining(), 3);
        out.write_char('π').unwrap();
        assert_eq!(out.remaining(), 1);
        out.write_char('x').unwrap();
        assert_eq!(out.remaining(), 0);
        assert!(out.write_char('!').is_err());
        assert_eq!(out.digest.finalize(), Sha256::digest(expected.as_bytes()));
    }
}
