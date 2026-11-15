// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Untrusted rank-candidate generation from the current elaborated environment.
//!
//! This decoder reads the actual `KDefSig` BODY fields, including an in-memory
//! regenerated reflection. It does not remap an old rank table or infer edges
//! from declaration types. The unchanged kernel theorem
//! `def_env_ranked_b (red_def the_red_env) = true` remains the final authority.

use std::collections::{BTreeMap, BTreeSet, VecDeque};

use clean_kernel::{Expr, ExprKind, Literal, Name, TransparencyMode, TypeChecker};

use crate::red_env_reflect::{parse_interning_tsv, COMMITTED_INTERNING_TSV};
use crate::spec::error::SpecError;
use crate::spec::Specification;

fn invalid(detail: impl std::fmt::Display) -> SpecError {
    SpecError::EnvError(format!("actual reflected delta-rank candidate: {detail}"))
}

struct Decoder<'a> {
    tc: TypeChecker<'a>,
    tag_count: usize,
}

impl Decoder<'_> {
    fn normalized(&self, phase: &str, value: &Expr) -> Result<Expr, SpecError> {
        let normalized = self.tc.whnf(value);
        if self.tc.heartbeat_spent() {
            return Err(invalid(format!(
                "{phase}: WHNF exhausted its heartbeat budget; input={value:?}; partial normalized={normalized:?}"
            )));
        }
        Ok(normalized)
    }

    fn constructor(&self, phase: &str, value: &Expr) -> Result<(String, Vec<Expr>), SpecError> {
        let normalized = self.normalized(phase, value)?;
        Self::constructor_from_normalized(phase, value, &normalized)
    }

    fn constructor_from_normalized(
        phase: &str,
        value: &Expr,
        normalized: &Expr,
    ) -> Result<(String, Vec<Expr>), SpecError> {
        let ExprKind::Const(name, levels) = normalized.get_app_fn().kind() else {
            return Err(invalid(format!(
                "{phase}: expected a closed constructor-headed data value; input={value:?}; normalized={normalized:?}"
            )));
        };
        if !levels.is_empty() {
            return Err(invalid(format!(
                "{phase}: unexpected universe arguments on data constructor {name}; normalized={normalized:?}"
            )));
        }
        Ok((
            name.to_string(),
            normalized.get_app_args().into_iter().cloned().collect(),
        ))
    }

    fn tag_nat(&self, value: &Expr) -> Result<usize, SpecError> {
        let mut cursor = value.clone();
        let mut successors = 0_usize;
        loop {
            let normalized = self.normalized("interned name tag", &cursor)?;
            if let ExprKind::Lit(Literal::Nat(n)) = normalized.kind() {
                let literal = n
                    .to_u64()
                    .and_then(|n| usize::try_from(n).ok())
                    .ok_or_else(|| invalid("name tag literal is out of range"))?;
                let tag = successors
                    .checked_add(literal)
                    .ok_or_else(|| invalid("name tag overflow"))?;
                return self.checked_tag(tag);
            }
            // Inspect this SAME normalization result after the literal case.
            // A further WHNF call may turn `Nat.succ <reducible alias>` into
            // a native Nat literal. Constructor-only dispatch after that
            // second call would reject a valid tag (observed at tag 100).
            let (constructor, args) =
                Self::constructor_from_normalized("interned name tag", &cursor, &normalized)?;
            match (constructor.as_str(), args.as_slice()) {
                ("Nat.zero", []) => return self.checked_tag(successors),
                ("Nat.succ", [predecessor]) => {
                    successors = successors
                        .checked_add(1)
                        .ok_or_else(|| invalid("name tag overflow"))?;
                    if successors >= self.tag_count {
                        return Err(invalid("name tag exceeds the current interning table"));
                    }
                    cursor = predecessor.clone();
                }
                _ => return Err(invalid("name tag is not a natural-number value")),
            }
        }
    }

    fn checked_tag(&self, tag: usize) -> Result<usize, SpecError> {
        if tag < self.tag_count {
            Ok(tag)
        } else {
            Err(invalid(format!(
                "name tag {tag} exceeds the current {}-entry interning table",
                self.tag_count
            )))
        }
    }

    fn name_tag(&self, value: &Expr) -> Result<usize, SpecError> {
        let (constructor, args) = self.constructor("interned name", value)?;
        let ("Name.str", [parent, tag]) = (constructor.as_str(), args.as_slice()) else {
            return Err(invalid("expected a flat interned Name.str anonymous tag"));
        };
        let (parent_constructor, parent_args) = self.constructor("interned name parent", parent)?;
        if parent_constructor != "Name.anonymous" || !parent_args.is_empty() {
            return Err(invalid("interned name has a non-anonymous parent"));
        }
        self.tag_nat(tag)
    }

    fn body_dependencies(&self, tag: usize, body: &Expr) -> Result<BTreeSet<usize>, SpecError> {
        let mut pending = vec![body.clone()];
        let mut dependencies = BTreeSet::new();
        while let Some(node) = pending.pop() {
            let (constructor, args) =
                self.constructor(&format!("definition tag {tag} body"), &node)?;
            match (constructor.as_str(), args.as_slice()) {
                ("KExpr.sort" | "KExpr.bvar" | "KExpr.lit", [_]) => {}
                ("KExpr.const", [name, _levels]) => {
                    dependencies.insert(self.name_tag(name)?);
                }
                ("KExpr.app" | "KExpr.lam" | "KExpr.pi", [left, right]) => {
                    pending.push(left.clone());
                    pending.push(right.clone());
                }
                ("KExpr.let_", [type_, value, body]) => {
                    pending.push(type_.clone());
                    pending.push(value.clone());
                    pending.push(body.clone());
                }
                ("KExpr.proj", [_structure, _field, body]) => pending.push(body.clone()),
                _ => {
                    return Err(invalid(format!(
                        "malformed or unsupported KExpr node {constructor}/{}",
                        args.len()
                    )))
                }
            }
        }
        Ok(dependencies)
    }
}

/// Compute a candidate from the already elaborated current reflection.
/// Failure is conservative: malformed data, unknown tags, duplicate bindings,
/// and dependency cycles are rejected, never assigned guessed ranks.
pub(super) fn actual_ranks(spec: &Specification) -> Result<Vec<u64>, SpecError> {
    let table = parse_interning_tsv(
        spec.red_env_interning_override
            .as_deref()
            .unwrap_or(COMMITTED_INTERNING_TSV),
    )
    .map_err(invalid)?;
    for name in ["red_def", "kernel_core_red_env"] {
        let declaration = spec
            .env()
            .get_const(&Name::from_string(name))
            .ok_or_else(|| invalid(format!("missing elaborated {name}")))?;
        if declaration.value.is_none() {
            return Err(invalid(format!("{name} has no elaborated value")));
        }
    }
    let decoder = Decoder {
        tc: TypeChecker::with_transparency(spec.env(), TransparencyMode::All),
        tag_count: table.len(),
    };
    let mut cursor = Expr::app(
        Expr::const_str("red_def"),
        Expr::const_str("kernel_core_red_env"),
    );
    let mut graph = BTreeMap::new();
    loop {
        let (constructor, args) = decoder.constructor("DefEnv spine", &cursor)?;
        match (constructor.as_str(), args.as_slice()) {
            ("DefEnv.empty", []) => break,
            ("DefEnv.addDef", [tail, name, definition]) => {
                let tag = decoder.name_tag(name)?;
                let (def_constructor, def_args) =
                    decoder.constructor(&format!("definition tag {tag} record"), definition)?;
                let ("KDefSig.mk", [signature, body]) =
                    (def_constructor.as_str(), def_args.as_slice())
                else {
                    return Err(invalid("definition payload is not a KDefSig.mk record"));
                };
                let (sig_constructor, sig_args) =
                    decoder.constructor(&format!("definition tag {tag} signature"), signature)?;
                if sig_constructor != "KConstSig.mk" || sig_args.len() != 2 {
                    return Err(invalid("definition signature is not a KConstSig.mk record"));
                }
                // The declaration signature's type is deliberately not an edge.
                // Binder types INSIDE the body are edges, exactly as in the
                // kernel's rank_dominates_b recursion over KExpr.
                if graph
                    .insert(tag, decoder.body_dependencies(tag, body)?)
                    .is_some()
                {
                    return Err(invalid(format!(
                        "duplicate definition binding at tag {tag}"
                    )));
                }
                cursor = tail.clone();
            }
            _ => {
                return Err(invalid(
                    "environment is not a concrete DefEnv constructor spine",
                ))
            }
        }
    }
    rank_graph(table.len(), &graph)
}

fn rank_graph(
    tag_count: usize,
    graph: &BTreeMap<usize, BTreeSet<usize>>,
) -> Result<Vec<u64>, SpecError> {
    let mut ranks = vec![0_u64; tag_count];
    let mut remaining = BTreeMap::new();
    let mut users: BTreeMap<usize, Vec<usize>> = BTreeMap::new();
    let mut ready = VecDeque::new();
    for (&name, dependencies) in graph {
        if name >= tag_count || dependencies.iter().any(|&tag| tag >= tag_count) {
            return Err(invalid(
                "dependency graph references a tag absent from its table",
            ));
        }
        let mut unresolved = 0_usize;
        for &dependency in dependencies {
            if graph.contains_key(&dependency) {
                unresolved += 1;
                users.entry(dependency).or_default().push(name);
            }
        }
        remaining.insert(name, unresolved);
        if unresolved == 0 {
            ready.push_back(name);
        }
    }
    let mut processed = 0_usize;
    while let Some(name) = ready.pop_front() {
        let dependencies = graph
            .get(&name)
            .ok_or_else(|| invalid("internal candidate graph key is missing"))?;
        let maximum = dependencies
            .iter()
            .map(|&tag| ranks[tag])
            .max()
            .unwrap_or(0);
        ranks[name] = maximum
            .checked_add(1)
            .ok_or_else(|| invalid("candidate rank overflow"))?;
        processed += 1;
        for &user in users.get(&name).into_iter().flatten() {
            let unresolved = remaining
                .get_mut(&user)
                .ok_or_else(|| invalid("internal candidate graph user is missing"))?;
            *unresolved = unresolved
                .checked_sub(1)
                .ok_or_else(|| invalid("internal candidate graph dependency underflow"))?;
            if *unresolved == 0 {
                ready.push_back(user);
            }
        }
    }
    if processed != graph.len() {
        return Err(invalid(
            "actual reflected definition bodies contain a dependency cycle",
        ));
    }
    Ok(ranks)
}

#[cfg(test)]
mod tests {
    use super::{rank_graph, Decoder};
    use clean_kernel::{Declaration, Environment, Expr, Name, TransparencyMode, TypeChecker};
    use std::collections::{BTreeMap, BTreeSet};

    fn graph(edges: &[(usize, &[usize])]) -> BTreeMap<usize, BTreeSet<usize>> {
        edges
            .iter()
            .map(|(n, ds)| (*n, ds.iter().copied().collect()))
            .collect()
    }

    #[test]
    fn diamond_uses_actual_dependencies_and_undefined_zero() {
        let graph = graph(&[(0, &[1, 2]), (1, &[3]), (2, &[3]), (3, &[4])]);
        assert_eq!(rank_graph(5, &graph).expect("acyclic"), vec![3, 2, 2, 1, 0]);
    }

    #[test]
    fn cycles_and_out_of_table_tags_fail_closed() {
        assert!(rank_graph(2, &graph(&[(0, &[1]), (1, &[0])])).is_err());
        assert!(rank_graph(1, &graph(&[(0, &[0])])).is_err());
        assert!(rank_graph(2, &graph(&[(0, &[2])])).is_err());
        assert!(rank_graph(2, &graph(&[(2, &[])])).is_err());
    }

    #[test]
    fn renumbering_preserves_semantic_ranks() {
        let original = graph(&[(0, &[1, 2]), (1, &[3]), (2, &[3]), (3, &[4])]);
        let permutation = [4, 2, 0, 3, 1];
        let renumbered = original
            .iter()
            .map(|(&n, ds)| (permutation[n], ds.iter().map(|&d| permutation[d]).collect()))
            .collect();
        let before = rank_graph(5, &original).expect("original acyclic");
        let after = rank_graph(5, &renumbered).expect("renumbered acyclic");
        for old in 0..5 {
            assert_eq!(before[old], after[permutation[old]]);
        }
    }

    #[test]
    fn changing_a_body_edge_changes_the_candidate() {
        assert_eq!(
            rank_graph(3, &graph(&[(0, &[]), (1, &[2])])).expect("acyclic"),
            vec![1, 1, 0]
        );
        assert_eq!(
            rank_graph(3, &graph(&[(0, &[1]), (1, &[2])])).expect("acyclic"),
            vec![2, 1, 0]
        );
    }

    #[test]
    fn actual_type_checker_decodes_literal_unary_and_reducible_alias_tags() {
        crate::test_utils::run_with_stack(|| {
            let mut env = Environment::new();
            env.init_nat().expect("checked Nat prelude");
            // Match the generated pool's actual representation, not a mock
            // normalizer or a pre-converted vector of numeric tags.
            for n in 0..=100 {
                let value = if n == 0 {
                    Expr::const_str("Nat.zero")
                } else {
                    Expr::app(
                        Expr::const_str("Nat.succ"),
                        Expr::const_str(&format!("rank_test_nat_{}", n - 1)),
                    )
                };
                env.add_decl(Declaration::Definition {
                    name: Name::from_string(&format!("rank_test_nat_{n}")),
                    level_params: vec![],
                    type_: Expr::const_str("Nat"),
                    value,
                    is_reducible: true,
                })
                .expect("checked reducible Nat alias");
            }
            for (value, expected) in [
                (Expr::nat_lit(100), 100),
                (Expr::const_str("Nat.zero"), 0),
                (
                    Expr::app(
                        Expr::const_str("Nat.succ"),
                        Expr::app(Expr::const_str("Nat.succ"), Expr::const_str("Nat.zero")),
                    ),
                    2,
                ),
                (
                    Expr::app(
                        Expr::const_str("Nat.succ"),
                        Expr::const_str("rank_test_nat_99"),
                    ),
                    100,
                ),
                (Expr::const_str("rank_test_nat_100"), 100),
            ] {
                // Each case starts with an unwarmed actual checker. Do not
                // require WHNF to select either native or unary Nat syntax.
                let decoder = Decoder {
                    tc: TypeChecker::with_transparency(&env, TransparencyMode::All),
                    tag_count: 101,
                };
                assert_eq!(decoder.tag_nat(&value).expect("valid Nat tag"), expected);
            }
            let decoder = Decoder {
                tc: TypeChecker::with_transparency(&env, TransparencyMode::All),
                tag_count: 101,
            };
            assert!(decoder.tag_nat(&Expr::nat_lit(101)).is_err());
            assert!(decoder
                .tag_nat(&Expr::app(
                    Expr::const_str("Nat.succ"),
                    Expr::const_str("rank_test_nat_100"),
                ))
                .is_err());
            let error = decoder
                .tag_nat(&Expr::bvar(0))
                .expect_err("open terms are not interned Nat tags")
                .to_string();
            assert!(error.contains("interned name tag"), "{error}");
            assert!(error.contains("normalized=BVar(0)"), "{error}");
        });
    }
}
