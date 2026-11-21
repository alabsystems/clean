// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Classify declarations using the validated export and earlier citable names.

use super::{bodies::Statement, expressions::ExprRow};
use std::collections::HashSet;

/// A declaration's class in the independent K3 fragment census.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum K3FragmentClass {
    /// The declaration falls outside the fragment.
    Outside,
    /// The declaration matches a pinned base family.
    Recognised,
    /// The declaration belongs to the fragment.
    Inside,
}

impl K3FragmentClass {
    /// The canonical short name of this class.
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Outside => "outside",
            Self::Recognised => "recognised",
            Self::Inside => "inside",
        }
    }
}

pub(super) fn classify<'row>(
    expressions: &[ExprRow],
    rows: impl IntoIterator<Item = (usize, Option<&'row Statement>, Option<&'row [usize]>)>,
) -> Vec<K3FragmentClass> {
    let mut citable = HashSet::new();
    let mut walk = ExpressionWalk::new(expressions);
    rows.into_iter()
        .enumerate()
        .map(|(ordinal, (name, statement, recognised))| {
            if let Some(members) = recognised {
                citable.extend(members.iter().copied());
                K3FragmentClass::Recognised
            } else if statement.is_some_and(|statement| {
                statement.eligible
                    && walk.visit(statement, ordinal + 1, |name| citable.contains(&name))
            }) {
                citable.insert(name);
                K3FragmentClass::Inside
            } else {
                K3FragmentClass::Outside
            }
        })
        .collect()
}

pub(super) struct ExpressionWalk<'table> {
    expressions: &'table [ExprRow],
    // Use a distinct nonzero declaration ordinal to visit each shared node
    // once per declaration without clearing the entire table between rows.
    visited: Vec<usize>,
    pending: Vec<usize>,
}

impl<'table> ExpressionWalk<'table> {
    pub(super) fn new(expressions: &'table [ExprRow]) -> Self {
        Self {
            expressions,
            visited: vec![0; expressions.len()],
            pending: Vec::new(),
        }
    }

    pub(super) fn visit(
        &mut self,
        statement: &Statement,
        stamp: usize,
        mut visit_constant: impl FnMut(usize) -> bool,
    ) -> bool {
        self.pending.clear();
        self.pending.extend([statement.value, statement.ty]);
        while let Some(id) = self.pending.pop() {
            let Some(row) = self.expressions.get(id) else {
                return false;
            };
            if self.visited[id] == stamp {
                continue;
            }
            self.visited[id] = stamp;
            match row {
                ExprRow::BVar(_) | ExprRow::Sort(_) => {}
                ExprRow::Const { name, .. } if visit_constant(*name) => {}
                ExprRow::Const { .. } | ExprRow::Unsupported => return false,
                ExprRow::App(first, second)
                | ExprRow::Lam(first, second)
                | ExprRow::Pi(first, second) => self.pending.extend([*second, *first]),
                ExprRow::Let(ty, value, body) => self.pending.extend([*body, *value, *ty]),
                ExprRow::MData(child) => self.pending.push(*child),
            }
        }
        true
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use K3FragmentClass::{Inside, Outside, Recognised};

    fn statement(ty: usize, value: usize) -> Statement {
        Statement {
            parameters: Vec::new(),
            ty,
            value,
            eligible: true,
        }
    }

    fn constant(name: usize) -> ExprRow {
        ExprRow::Const {
            name,
            levels: Vec::new(),
        }
    }

    #[test]
    fn makes_inside_names_and_all_recognised_members_citable_only_in_export_order() {
        let expressions = [
            ExprRow::BVar("0".into()),
            constant(3),
            constant(11),
            constant(9),
            constant(8),
            constant(10),
            constant(2),
            constant(1),
        ];
        let cite_self = statement(4, 0);
        let cite_member = statement(1, 0);
        let clean = statement(0, 0);
        let cite_prior = statement(2, 0);
        let cite_outside = statement(3, 0);
        let cite_other_members = statement(6, 7);
        let cite_transitive = statement(5, 0);
        let members: &[usize] = &[1, 2, 3];
        let rows = [
            (8, Some(&cite_self), None),
            (9, Some(&cite_member), None),
            (1, None, Some(members)),
            (10, Some(&cite_member), None),
            (11, Some(&clean), None),
            (12, Some(&cite_prior), None),
            (13, Some(&cite_outside), None),
            (14, Some(&cite_other_members), None),
            (15, Some(&cite_transitive), None),
        ];
        assert_eq!(
            classify(&expressions, rows),
            [Outside, Outside, Recognised, Inside, Inside, Inside, Outside, Inside, Inside,]
        );
        assert_eq!(
            [Outside.as_str(), Recognised.as_str(), Inside.as_str()],
            ["outside", "recognised", "inside"]
        );
    }

    #[test]
    fn checks_both_roots_and_every_child() {
        let expressions = [
            ExprRow::BVar("18446744073709551616".into()),
            ExprRow::Sort(0),
            ExprRow::Lam(0, 1),
            ExprRow::Unsupported,
            ExprRow::MData(3),
            ExprRow::App(4, 0),
            ExprRow::App(0, 4),
            ExprRow::Lam(4, 0),
            ExprRow::Lam(0, 4),
            ExprRow::Pi(4, 0),
            ExprRow::Pi(0, 4),
            ExprRow::Let(4, 0, 0),
            ExprRow::Let(0, 4, 0),
            ExprRow::Let(0, 0, 4),
            ExprRow::Let(0, 1, 2),
            ExprRow::MData(14),
        ];
        let statements = (3..14)
            .flat_map(|root| [statement(root, 0), statement(0, root)])
            .chain([statement(1, 15)])
            .collect::<Vec<_>>();
        let classes = classify(
            &expressions,
            statements
                .iter()
                .enumerate()
                .map(|(name, statement)| (name, Some(statement), None)),
        );
        assert_eq!(
            classes.split_last(),
            Some((&Inside, [Outside; 22].as_slice()))
        );
    }

    #[test]
    fn leaves_ineligible_and_non_ordinary_names_uncitable() {
        let expressions = [ExprRow::Sort(0), constant(1), constant(2)];
        let clean = statement(0, 0);
        let ineligible = Statement {
            eligible: false,
            ..statement(0, 0)
        };
        let cites_ineligible = statement(1, 0);
        let cites_non_ordinary = statement(0, 2);
        let rows = [
            (1, Some(&ineligible), None),
            (2, None, None),
            (3, Some(&cites_ineligible), None),
            (4, Some(&cites_non_ordinary), None),
            (5, Some(&clean), None),
        ];
        assert_eq!(
            classify(&expressions, rows),
            [Outside, Outside, Outside, Outside, Inside]
        );
    }

    #[test]
    fn visits_a_shared_subterm_once_per_declaration() {
        let mut expressions = vec![constant(1)];
        for child in 0..18 {
            expressions.push(ExprRow::App(child, child));
        }
        let mut walk = ExpressionWalk::new(&expressions);
        let declaration = statement(18, 18);
        for stamp in [1, 2] {
            let mut seen = Vec::new();
            assert!(walk.visit(&declaration, stamp, |name| {
                seen.push(name);
                true
            }));
            assert_eq!(seen, [1]);
        }
    }
}
