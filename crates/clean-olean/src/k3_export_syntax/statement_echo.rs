// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Emit scoped statement echo bytes with an explicit traversal stack.

use super::{expressions::ExprRow, levels::LevelRow, names::NameTable};
use std::collections::HashMap;
use std::fmt;

pub(super) trait EchoOutput: fmt::Write {
    /// The maximum number of bytes that the sink can still accept.
    fn remaining(&self) -> usize;
}

struct Expected<'echo>(&'echo str);

impl fmt::Write for Expected<'_> {
    fn write_str(&mut self, text: &str) -> fmt::Result {
        self.0 = self.0.strip_prefix(text).ok_or(fmt::Error)?;
        Ok(())
    }
}

impl EchoOutput for Expected<'_> {
    fn remaining(&self) -> usize {
        self.0.len()
    }
}

enum Piece<'table> {
    Text(&'static str),
    Expr(usize),
    Level(usize),
    ConstLevels(&'table [usize]),
}

pub(super) fn matches_expression(
    names: &NameTable,
    levels: &[LevelRow],
    expressions: &[ExprRow],
    scope: &HashMap<usize, usize>,
    root: usize,
    expected: &str,
) -> bool {
    let mut out = Expected(expected);
    write_expression(names, levels, expressions, scope, root, &mut out).is_ok() && out.0.is_empty()
}

pub(super) fn write_expression(
    names: &NameTable,
    levels: &[LevelRow],
    expressions: &[ExprRow],
    scope: &HashMap<usize, usize>,
    root: usize,
    out: &mut impl EchoOutput,
) -> fmt::Result {
    use Piece::{ConstLevels, Expr, Level, Text};

    let mut pending = vec![Expr(root)];
    while let Some(piece) = pending.pop() {
        match piece {
            Text(text) => out.write_str(text)?,
            Expr(id) => match expressions.get(id).ok_or(fmt::Error)? {
                ExprRow::BVar(decimal) => write!(out, "(b {decimal})")?,
                ExprRow::Sort(level) => {
                    out.write_str("(sort ")?;
                    pending.extend([Text(")"), Level(*level)]);
                }
                ExprRow::Const { name, levels } => {
                    out.write_str("(c ")?;
                    names.write_echo(*name, out)?;
                    pending.push(ConstLevels(levels));
                }
                ExprRow::App(function, argument) => {
                    queue_pair(&mut pending, out, "(app ", Expr(*function), Expr(*argument))?;
                }
                ExprRow::Lam(domain, body) => {
                    queue_pair(&mut pending, out, "(lam ", Expr(*domain), Expr(*body))?;
                }
                ExprRow::Pi(domain, body) => {
                    queue_pair(&mut pending, out, "(pi ", Expr(*domain), Expr(*body))?;
                }
                ExprRow::Let(ty, value, body) => {
                    out.write_str("(let ")?;
                    pending.extend([
                        Text(")"),
                        Expr(*body),
                        Text(" "),
                        Expr(*value),
                        Text(" "),
                        Expr(*ty),
                    ]);
                }
                ExprRow::MData(child) => pending.push(Expr(*child)),
                ExprRow::Unsupported => return Err(fmt::Error),
            },
            Level(id) => match levels.get(id).ok_or(fmt::Error)? {
                LevelRow::Zero => out.write_char('0')?,
                LevelRow::Succ(level) => {
                    out.write_str("(s ")?;
                    pending.extend([Text(")"), Level(*level)]);
                }
                LevelRow::Max(left, right) => {
                    queue_pair(&mut pending, out, "(max ", Level(*left), Level(*right))?;
                }
                LevelRow::IMax(left, right) => {
                    queue_pair(&mut pending, out, "(imax ", Level(*left), Level(*right))?;
                }
                LevelRow::Param(name) => {
                    let ordinal = scope.get(name).ok_or(fmt::Error)?;
                    write!(out, "(p {ordinal})")?;
                }
            },
            ConstLevels(levels) => {
                if let Some((level, rest)) = levels.split_first() {
                    out.write_char(' ')?;
                    pending.extend([ConstLevels(rest), Level(*level)]);
                } else {
                    out.write_char(')')?;
                }
            }
        }
    }
    Ok(())
}

fn queue_pair<'table>(
    pending: &mut Vec<Piece<'table>>,
    out: &mut impl EchoOutput,
    open: &str,
    first: Piece<'table>,
    second: Piece<'table>,
) -> fmt::Result {
    out.write_str(open)?;
    pending.extend([Piece::Text(")"), second, Piece::Text(" "), first]);
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ndjson::json::{parse_line, JsonValue};

    fn names() -> NameTable {
        let mut names = NameTable::default();
        for (line, text) in [
            (2, r#"{"in":1,"str":{"pre":0,"str":"π"}}"#),
            (3, r#"{"in":2,"str":{"pre":1,"str":"é]"}}"#),
            (4, r#"{"in":3,"num":{"pre":0,"i":18446744073709551616}}"#),
        ] {
            let JsonValue::Object(entries) = parse_line(text.as_bytes()).unwrap() else {
                panic!("a name fixture must be a JSON object");
            };
            names.visit(line, entries).unwrap();
        }
        names
    }

    #[derive(Default)]
    struct BoundedText {
        text: String,
        limit: usize,
    }

    impl fmt::Write for BoundedText {
        fn write_str(&mut self, text: &str) -> fmt::Result {
            if text.len() > self.remaining() {
                return Err(fmt::Error);
            }
            self.text.push_str(text);
            Ok(())
        }
    }

    impl EchoOutput for BoundedText {
        fn remaining(&self) -> usize {
            self.limit - self.text.len()
        }
    }

    #[test]
    fn emits_names_and_expressions_with_exact_byte_budgets() {
        let names = names();
        let name = "[s2:π s3:é]]";
        let mut out = BoundedText {
            limit: name.len(),
            ..BoundedText::default()
        };
        names.write_echo(2, &mut out).unwrap();
        assert_eq!(out.text, name);
        assert_eq!(out.remaining(), 0);

        let mut out = BoundedText {
            limit: name.len() - 1,
            ..BoundedText::default()
        };
        assert!(names.write_echo(2, &mut out).is_err());
        assert!(out.text.is_empty());

        let levels = [LevelRow::Zero, LevelRow::Param(3)];
        let expressions = [ExprRow::Const {
            name: 2,
            levels: vec![0, 1, 0],
        }];
        let scope = HashMap::from([(3, 0)]);
        let expected = "(c [s2:π s3:é]] 0 (p 0) 0)";
        for limit in [expected.len() - 1, expected.len()] {
            let mut out = BoundedText {
                limit,
                ..BoundedText::default()
            };
            let result = write_expression(&names, &levels, &expressions, &scope, 0, &mut out);
            assert_eq!(result.is_ok(), limit == expected.len());
            assert_eq!(out.text, expected[..limit]);
        }
    }

    #[test]
    fn matches_exact_bytes_for_all_echo_forms() {
        let names = names();
        let levels = [
            LevelRow::Zero,
            LevelRow::Param(1),
            LevelRow::Param(2),
            LevelRow::Succ(1),
            LevelRow::Max(3, 2),
            LevelRow::IMax(4, 0),
        ];
        let wide = "18446744073709551616";
        let expressions = [
            ExprRow::BVar(wide.into()),
            ExprRow::Sort(5),
            ExprRow::Const {
                name: 2,
                levels: vec![2, 1, 2],
            },
            ExprRow::App(2, 0),
            ExprRow::Lam(1, 3),
            ExprRow::Pi(1, 4),
            ExprRow::Let(1, 4, 5),
            ExprRow::MData(6),
            ExprRow::Const {
                name: 3,
                levels: vec![],
            },
        ];
        let scope = HashMap::from([(1, 0), (2, 1)]);
        let sort = "(sort (imax (max (s (p 0)) (p 1)) 0))";
        let constant = "(c [s2:π s3:é]] (p 1) (p 0) (p 1))";
        let bvar = format!("(b {wide})");
        let app = format!("(app {constant} {bvar})");
        let lam = format!("(lam {sort} {app})");
        let pi = format!("(pi {sort} {lam})");
        let let_echo = format!("(let {sort} {lam} {pi})");
        for (root, expected) in [
            (0, bvar.as_str()),
            (1, sort),
            (2, constant),
            (3, &app),
            (4, &lam),
            (5, &pi),
            (6, &let_echo),
            (7, &let_echo),
            (8, "(c [n18446744073709551616])"),
        ] {
            assert!(
                matches_expression(&names, &levels, &expressions, &scope, root, expected),
                "{root}: {expected}"
            );
        }
        for alternate in [
            "(c [s2:π s2:é]] (p 1) (p 0) (p 1))",
            "(c [s2:π s3:é🙂 (p 1) (p 0) (p 1))",
            "(c [s2:π s3:é]] (p 1) (p 0))",
            "(c [s2:π s3:é]] (p 01) (p 0) (p 1))",
            "(c [s2:π s3:é]] (p 1) (p 0) (p 1))x",
        ] {
            assert!(
                !matches_expression(&names, &levels, &expressions, &scope, 2, alternate),
                "{alternate}"
            );
        }
    }

    #[test]
    fn follows_metadata_and_uses_the_declarations_parameter_order() {
        let names = NameTable::default();
        let levels = [LevelRow::Zero, LevelRow::Param(5), LevelRow::Param(1)];
        let expressions = [
            ExprRow::Sort(1),
            ExprRow::Sort(2),
            ExprRow::App(0, 1),
            ExprRow::MData(2),
            ExprRow::Unsupported,
            ExprRow::MData(4),
        ];
        let scope = HashMap::from([(5, 0), (1, 1)]);
        let reversed = HashMap::from([(1, 0), (5, 1)]);
        let missing = HashMap::from([(5, 0), (2, 1)]);
        let expected = "(app (sort (p 0)) (sort (p 1)))";
        assert!(matches_expression(
            &names,
            &levels,
            &expressions,
            &scope,
            3,
            expected
        ));
        assert!(matches_expression(
            &names,
            &levels,
            &expressions,
            &reversed,
            3,
            "(app (sort (p 1)) (sort (p 0)))"
        ));
        assert!(!matches_expression(
            &names,
            &levels,
            &expressions,
            &reversed,
            3,
            expected
        ));
        assert!(!matches_expression(
            &names,
            &levels,
            &expressions,
            &missing,
            3,
            expected
        ));
        assert!(!matches_expression(
            &names,
            &levels,
            &expressions,
            &scope,
            5,
            "(lit)"
        ));
        assert!(!matches_expression(
            &names,
            &levels,
            &expressions,
            &scope,
            6,
            expected
        ));
    }

    #[test]
    fn handles_deep_shared_nodes_and_wide_constant_lists_without_expansion() {
        let names = NameTable::default();
        let levels = [LevelRow::Zero];
        let scope = HashMap::new();
        let mut expressions = vec![ExprRow::BVar("0".into())];
        for child in 0..40_000 {
            expressions.push(ExprRow::MData(child));
        }
        assert!(matches_expression(
            &names,
            &levels,
            &expressions,
            &scope,
            40_000,
            "(b 0)"
        ));
        expressions.push(ExprRow::App(40_000, 40_000));
        assert!(matches_expression(
            &names,
            &levels,
            &expressions,
            &scope,
            40_001,
            "(app (b 0) (b 0))"
        ));
        for child in 40_001..40_004 {
            expressions.push(ExprRow::App(child, child));
        }
        assert!(!matches_expression(
            &names,
            &levels,
            &expressions,
            &scope,
            40_004,
            "(app (b 0) (b 0))"
        ));
        let root = expressions.len();
        expressions.push(ExprRow::Const {
            name: 0,
            levels: vec![0; 200_000],
        });
        assert!(!matches_expression(
            &names,
            &levels,
            &expressions,
            &scope,
            root,
            "(c [] 0)"
        ));
    }
}
