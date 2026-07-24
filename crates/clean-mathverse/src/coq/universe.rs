// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Coq universe polymorphism: constraint parsing, graph resolution, and
//! monomorphization of universe-polymorphic constants for Mathverse import.

use clean_kernel::flat::FlatLevel;

#[cfg(test)]
use crate::coq::alpha::parse_sexp;
use crate::coq::alpha::{cic_to_flat_expr, CicCase, CicStructFix, CicTerm, Sexp};
use crate::error::{MathverseError, MathverseResult};
use crate::shard::ShardWriter;
#[cfg(test)]
use crate::types::AxiomProfile;
use crate::types::{
    ContentDomain, ImportConfidence, MathverseConstantHeader, SourceSystem, NO_VALUE,
};

/// A universe expression in Coq's constraint system.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum UniverseExpr {
    Level(String),
    Max(Vec<String>),
    Succ(Box<UniverseExpr>, u32),
    Prop,
    Set,
    Type(u32),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ConstraintRelation {
    Le,
    Lt,
    Eq,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct UniverseConstraint {
    pub left: UniverseExpr,
    pub relation: ConstraintRelation,
    pub right: UniverseExpr,
}

#[derive(Clone, Debug)]
pub enum UniverseError {
    Inconsistent(String),
    Unresolvable(String),
}

impl std::fmt::Display for UniverseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Inconsistent(m) => write!(f, "inconsistent: {m}"),
            Self::Unresolvable(m) => write!(f, "unresolvable: {m}"),
        }
    }
}

// -- Constraint graph --------------------------------------------------------

#[derive(Clone, Debug)]
struct Edge {
    target: usize,
    weight: u32,
}

/// Constraint graph with Bellman-Ford resolution.
pub struct UniverseGraph {
    levels: Vec<String>,
    level_to_idx: hashbrown::HashMap<String, usize>,
    constraints: Vec<UniverseConstraint>,
    edges: Vec<Vec<Edge>>,
}

impl UniverseGraph {
    pub fn new() -> Self {
        Self {
            levels: Vec::new(),
            level_to_idx: hashbrown::HashMap::new(),
            constraints: Vec::new(),
            edges: Vec::new(),
        }
    }
    pub fn add_level(&mut self, name: &str) -> usize {
        if let Some(&idx) = self.level_to_idx.get(name) {
            return idx;
        }
        let idx = self.levels.len();
        self.levels.push(name.to_owned());
        self.level_to_idx.insert(name.to_owned(), idx);
        self.edges.push(Vec::new());
        idx
    }
    pub fn add_constraint(&mut self, c: UniverseConstraint) {
        self.add_edges(&c);
        self.constraints.push(c);
    }
    fn add_edges(&mut self, c: &UniverseConstraint) {
        let (l, r) = match (&c.left, &c.right) {
            (UniverseExpr::Level(l), UniverseExpr::Level(r)) => (l.clone(), r.clone()),
            _ => return,
        };
        let (li, ri) = (self.add_level(&l), self.add_level(&r));
        match c.relation {
            ConstraintRelation::Le => self.edges[li].push(Edge {
                target: ri,
                weight: 0,
            }),
            ConstraintRelation::Lt => self.edges[li].push(Edge {
                target: ri,
                weight: 1,
            }),
            ConstraintRelation::Eq => {
                self.edges[li].push(Edge {
                    target: ri,
                    weight: 0,
                });
                self.edges[ri].push(Edge {
                    target: li,
                    weight: 0,
                });
            }
        }
    }
    pub fn is_consistent(&self) -> bool {
        self.resolve().is_ok()
    }
    /// Resolve levels to minimal concrete numbers. Positive-weight cycle = error.
    pub fn resolve(&self) -> Result<hashbrown::HashMap<String, u32>, UniverseError> {
        let n = self.levels.len();
        if n == 0 {
            return Ok(hashbrown::HashMap::new());
        }
        let mut dist = vec![0i64; n];
        for _ in 0..n {
            let mut changed = false;
            for (s, edges) in self.edges.iter().enumerate() {
                for e in edges {
                    let nd = dist[s] + e.weight as i64;
                    if nd > dist[e.target] {
                        dist[e.target] = nd;
                        changed = true;
                    }
                }
            }
            if !changed {
                break;
            }
        }
        for (s, edges) in self.edges.iter().enumerate() {
            for e in edges {
                if dist[s] + e.weight as i64 > dist[e.target] {
                    return Err(UniverseError::Inconsistent(format!(
                        "cycle: {} and {}",
                        self.levels[s], self.levels[e.target]
                    )));
                }
            }
        }
        let mn = dist.iter().copied().min().unwrap_or(0);
        Ok(self
            .levels
            .iter()
            .enumerate()
            .map(|(i, name)| (name.clone(), (dist[i] - mn) as u32))
            .collect())
    }
    /// Lower resolved levels into the FlatLevel arena.
    pub fn lower_levels(
        &self,
        resolution: &hashbrown::HashMap<String, u32>,
        w: &mut ShardWriter,
    ) -> hashbrown::HashMap<String, u32> {
        resolution
            .iter()
            .map(|(name, &level)| {
                let mut idx = w.add_level(FlatLevel::zero());
                for _ in 0..level {
                    idx = w.add_level(FlatLevel::succ(idx));
                }
                (name.clone(), idx)
            })
            .collect()
    }
}

impl Default for UniverseGraph {
    fn default() -> Self {
        Self::new()
    }
}

// -- Universe-polymorphic constants ------------------------------------------

#[derive(Clone, Debug)]
pub struct PolyConstant {
    pub name: String,
    pub universe_params: Vec<String>,
    pub constraints: Vec<UniverseConstraint>,
    pub type_: CicTerm,
    pub body: Option<CicTerm>,
}

/// Instantiate universe params with concrete levels in type and body.
pub fn instantiate_poly(
    c: &PolyConstant,
    levels: &[u32],
) -> Result<(CicTerm, Option<CicTerm>), UniverseError> {
    if levels.len() != c.universe_params.len() {
        return Err(UniverseError::Unresolvable(format!(
            "expected {} levels, got {}",
            c.universe_params.len(),
            levels.len()
        )));
    }
    let subst: hashbrown::HashMap<String, u32> = c
        .universe_params
        .iter()
        .cloned()
        .zip(levels.iter().copied())
        .collect();
    Ok((
        subst_universes(&c.type_, &subst),
        c.body.as_ref().map(|b| subst_universes(b, &subst)),
    ))
}

fn subst_universes(term: &CicTerm, s: &hashbrown::HashMap<String, u32>) -> CicTerm {
    match term {
        CicTerm::Var(name) => match s.get(name) {
            Some(&l) => CicTerm::Sort(crate::coq::alpha::CicSort::type_at(l)),
            None => term.clone(),
        },
        CicTerm::Prod(n, ty, b) => CicTerm::Prod(
            n.clone(),
            Box::new(subst_universes(ty, s)),
            Box::new(subst_universes(b, s)),
        ),
        CicTerm::Lambda(n, ty, b) => CicTerm::Lambda(
            n.clone(),
            Box::new(subst_universes(ty, s)),
            Box::new(subst_universes(b, s)),
        ),
        CicTerm::LetIn(n, v, ty, b) => CicTerm::LetIn(
            n.clone(),
            Box::new(subst_universes(v, s)),
            Box::new(subst_universes(ty, s)),
            Box::new(subst_universes(b, s)),
        ),
        CicTerm::App(f, args) => CicTerm::App(
            Box::new(subst_universes(f, s)),
            args.iter().map(|a| subst_universes(a, s)).collect(),
        ),
        CicTerm::Case(case) => CicTerm::Case(Box::new(CicCase {
            ind_name: case.ind_name.clone(),
            ind_idx: case.ind_idx,
            params: case.params.iter().map(|p| subst_universes(p, s)).collect(),
            motive: Box::new(subst_universes(&case.motive, s)),
            branches: case
                .branches
                .iter()
                .map(|b| subst_universes(b, s))
                .collect(),
            discriminant: Box::new(subst_universes(&case.discriminant, s)),
        })),
        CicTerm::Fix(bs, i) => CicTerm::Fix(
            bs.iter()
                .map(|(n, ty, b)| {
                    (
                        n.clone(),
                        Box::new(subst_universes(ty, s)),
                        Box::new(subst_universes(b, s)),
                    )
                })
                .collect(),
            *i,
        ),
        CicTerm::CoFix(bs, i) => CicTerm::CoFix(
            bs.iter()
                .map(|(n, ty, b)| {
                    (
                        n.clone(),
                        Box::new(subst_universes(ty, s)),
                        Box::new(subst_universes(b, s)),
                    )
                })
                .collect(),
            *i,
        ),
        CicTerm::Proj(n, i, inner) => {
            CicTerm::Proj(n.clone(), *i, Box::new(subst_universes(inner, s)))
        }
        CicTerm::StructFix(fix) => CicTerm::StructFix(Box::new(CicStructFix {
            ind_name: fix.ind_name.clone(),
            ind_idx: fix.ind_idx,
            rec_level: fix.rec_level,
            prop_only: fix.prop_only,
            params: fix.params.iter().map(|p| subst_universes(p, s)).collect(),
            pre_binders: fix
                .pre_binders
                .iter()
                .map(|p| subst_universes(p, s))
                .collect(),
            struct_ty: Box::new(subst_universes(&fix.struct_ty, s)),
            post_binders: fix
                .post_binders
                .iter()
                .map(|p| subst_universes(p, s))
                .collect(),
            indices: fix.indices.iter().map(|x| subst_universes(x, s)).collect(),
            motive: Box::new(subst_universes(&fix.motive, s)),
            branches: fix.branches.iter().map(|b| subst_universes(b, s)).collect(),
        })),
        _ => term.clone(),
    }
}

/// Import a universe-polymorphic constant: resolve constraints, monomorphize, write to shard.
pub fn import_poly_constant(
    constant: &PolyConstant,
    module_path: &str,
    writer: &mut ShardWriter,
) -> MathverseResult<u32> {
    let mut graph = UniverseGraph::new();
    for p in &constant.universe_params {
        graph.add_level(p);
    }
    for c in &constant.constraints {
        graph.add_constraint(c.clone());
    }
    let resolution = graph.resolve().map_err(|e| uerr(&e.to_string()))?;
    let levels: Vec<u32> = constant
        .universe_params
        .iter()
        .map(|p| resolution.get(p).copied().unwrap_or(0))
        .collect();
    let (ty, body) = instantiate_poly(constant, &levels).map_err(|e| uerr(&e.to_string()))?;
    let type_idx = cic_to_flat_expr(&ty, writer);
    let value_idx = body
        .as_ref()
        .map(|b| cic_to_flat_expr(b, writer))
        .unwrap_or(NO_VALUE);
    let profile = crate::coq::alpha::classify_coq_module(module_path);
    let confidence = if value_idx == NO_VALUE {
        ImportConfidence::Axiomatized
    } else {
        ImportConfidence::Translated
    };
    // Universe-polymorphic constant with a body → Definition; without → Axiom.
    let kind = if value_idx == NO_VALUE {
        crate::types::DeclKind::Axiom
    } else {
        crate::types::DeclKind::Definition
    };
    let name_idx = writer.add_string(&constant.name);
    Ok(writer.add_constant(MathverseConstantHeader {
        name_idx,
        type_idx,
        value_idx,
        source_system: SourceSystem::Coq as u8,
        import_confidence: confidence as u8,
        content_domain: ContentDomain::PureMath as u8,
        decl_kind: kind as u8,
        axiom_profile: profile,
        sidecar_digest: 0,
        provenance_idx: 0,
        level_params_start: 0,
        level_params_count: 0,
        _pad2: [0u8; 26],
    }))
}

// -- S-expression parsing ----------------------------------------------------

/// Parse a universe expression from an s-expression.
pub fn parse_universe_expr(sexp: &Sexp) -> Result<UniverseExpr, MathverseError> {
    match sexp {
        Sexp::Atom(s) => match s.as_str() {
            "Prop" => Ok(UniverseExpr::Prop),
            "Set" => Ok(UniverseExpr::Set),
            _ => s
                .parse::<u32>()
                .map(UniverseExpr::Type)
                .or_else(|_| Ok(UniverseExpr::Level(s.clone()))),
        },
        Sexp::List(items) if items.is_empty() => Err(uerr("empty list")),
        Sexp::List(items) => {
            let head = match &items[0] {
                Sexp::Atom(s) => s.as_str(),
                _ => return Err(uerr("expected atom head")),
            };
            match head {
                "Type" => match items.get(1) {
                    Some(Sexp::Atom(s)) => Ok(UniverseExpr::Type(
                        s.parse().map_err(|_| uerr("invalid Type level"))?,
                    )),
                    _ => Err(uerr("Type requires numeric argument")),
                },
                "Succ" if items.len() >= 3 => {
                    let inner = parse_universe_expr(&items[1])?;
                    let off = match &items[2] {
                        Sexp::Atom(s) => s.parse().map_err(|_| uerr("invalid Succ offset"))?,
                        _ => return Err(uerr("Succ offset must be a number")),
                    };
                    Ok(UniverseExpr::Succ(Box::new(inner), off))
                }
                "Succ" => Err(uerr("Succ requires expression and offset")),
                "Max" => {
                    let names: Result<Vec<_>, _> = items[1..]
                        .iter()
                        .map(|item| match item {
                            Sexp::Atom(s) => Ok(s.clone()),
                            _ => Err(uerr("Max expects atom level names")),
                        })
                        .collect();
                    Ok(UniverseExpr::Max(names?))
                }
                _ => Err(uerr(&format!("unknown form: {head}"))),
            }
        }
    }
}

/// Parse constraints from `(Constraints ((Level.Le u1 u2) ...))`.
pub fn parse_constraints(sexp: &Sexp) -> Result<Vec<UniverseConstraint>, MathverseError> {
    let items = match sexp {
        Sexp::List(v) if !v.is_empty() => v,
        _ => return Err(uerr("expected list for Constraints")),
    };
    match &items[0] {
        Sexp::Atom(s) if s == "Constraints" => {}
        _ => return Err(uerr("expected Constraints head")),
    }
    let clist = if items.len() == 2 {
        match &items[1] {
            Sexp::List(inner) => inner.as_slice(),
            _ => return Ok(Vec::new()),
        }
    } else {
        &items[1..]
    };
    let mut result = Vec::new();
    for item in clist {
        let cv = match item {
            Sexp::List(v) if v.len() >= 3 => v,
            _ => continue,
        };
        let rel = match &cv[0] {
            Sexp::Atom(s) => match s.as_str() {
                "Level.Le" => ConstraintRelation::Le,
                "Level.Lt" => ConstraintRelation::Lt,
                "Level.Eq" => ConstraintRelation::Eq,
                _ => continue,
            },
            _ => continue,
        };
        result.push(UniverseConstraint {
            left: parse_universe_expr(&cv[1])?,
            relation: rel,
            right: parse_universe_expr(&cv[2])?,
        });
    }
    Ok(result)
}

fn uerr(reason: &str) -> MathverseError {
    MathverseError::ImportFailed {
        system: "Coq/universe".into(),
        reason: reason.into(),
    }
}

// -- Tests -------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::coq::alpha::{CicSort, CoqUniverseLevel};

    fn uc(l: &str, rel: ConstraintRelation, r: &str) -> UniverseConstraint {
        UniverseConstraint {
            left: UniverseExpr::Level(l.into()),
            relation: rel,
            right: UniverseExpr::Level(r.into()),
        }
    }
    fn graph_with(names: &[&str], cs: &[UniverseConstraint]) -> UniverseGraph {
        let mut g = UniverseGraph::new();
        for n in names {
            g.add_level(n);
        }
        for c in cs {
            g.add_constraint(c.clone());
        }
        g
    }

    #[test]
    fn test_parse_constraints() {
        let cs = parse_constraints(
            &parse_sexp("(Constraints ((Level.Le u v) (Level.Lt v w)))").unwrap(),
        )
        .unwrap();
        assert_eq!(cs.len(), 2);
        assert_eq!(cs[0].left, UniverseExpr::Level("u".into()));
        assert_eq!(
            (cs[0].relation, cs[1].relation),
            (ConstraintRelation::Le, ConstraintRelation::Lt)
        );
        // Eq, empty, flat forms
        let cs = parse_constraints(&parse_sexp("(Constraints ((Level.Eq u v)))").unwrap()).unwrap();
        assert_eq!(cs[0].relation, ConstraintRelation::Eq);
        assert!(parse_constraints(&parse_sexp("(Constraints ())").unwrap())
            .unwrap()
            .is_empty());
        assert_eq!(
            parse_constraints(&parse_sexp("(Constraints (Level.Le a b) (Level.Lt b c))").unwrap())
                .unwrap()
                .len(),
            2
        );
        // Errors
        assert!(parse_constraints(&Sexp::Atom("bad".into())).is_err());
        assert!(
            parse_constraints(&parse_sexp("(NotConstraints ((Level.Le u v)))").unwrap()).is_err()
        );
    }

    #[test]
    fn test_parse_universe_expr() {
        assert_eq!(
            parse_universe_expr(&Sexp::Atom("Prop".into())).unwrap(),
            UniverseExpr::Prop
        );
        assert_eq!(
            parse_universe_expr(&Sexp::Atom("Set".into())).unwrap(),
            UniverseExpr::Set
        );
        assert_eq!(
            parse_universe_expr(&Sexp::Atom("u".into())).unwrap(),
            UniverseExpr::Level("u".into())
        );
        assert_eq!(
            parse_universe_expr(&Sexp::Atom("3".into())).unwrap(),
            UniverseExpr::Type(3)
        );
        assert_eq!(
            parse_universe_expr(&parse_sexp("(Type 5)").unwrap()).unwrap(),
            UniverseExpr::Type(5)
        );
        assert_eq!(
            parse_universe_expr(&parse_sexp("(Succ u 1)").unwrap()).unwrap(),
            UniverseExpr::Succ(Box::new(UniverseExpr::Level("u".into())), 1)
        );
        assert_eq!(
            parse_universe_expr(&parse_sexp("(Max u v w)").unwrap()).unwrap(),
            UniverseExpr::Max(vec!["u".into(), "v".into(), "w".into()])
        );
        assert!(parse_universe_expr(&Sexp::List(vec![])).is_err());
        assert!(parse_universe_expr(&parse_sexp("(Succ u)").unwrap()).is_err());
    }

    #[test]
    fn test_graph_empty_and_chains() {
        let g = UniverseGraph::new();
        assert!(g.is_consistent() && g.resolve().unwrap().is_empty());
        // Lt chain: u < v < w
        let g = graph_with(
            &["u", "v", "w"],
            &[
                uc("u", ConstraintRelation::Lt, "v"),
                uc("v", ConstraintRelation::Lt, "w"),
            ],
        );
        let r = g.resolve().unwrap();
        assert_eq!((r["u"], r["v"], r["w"]), (0, 1, 2));
        // Le chain: all at 0
        let g = graph_with(
            &["u", "v", "w"],
            &[
                uc("u", ConstraintRelation::Le, "v"),
                uc("v", ConstraintRelation::Le, "w"),
            ],
        );
        let r = g.resolve().unwrap();
        assert_eq!((r["u"], r["v"], r["w"]), (0, 0, 0));
    }

    #[test]
    fn test_graph_diamond_and_parallel() {
        let g = graph_with(
            &["u", "v", "w", "x"],
            &[
                uc("u", ConstraintRelation::Lt, "v"),
                uc("u", ConstraintRelation::Lt, "w"),
                uc("v", ConstraintRelation::Le, "x"),
                uc("w", ConstraintRelation::Le, "x"),
            ],
        );
        let r = g.resolve().unwrap();
        assert_eq!(r["u"], 0);
        assert!(r["v"] >= 1 && r["w"] >= 1 && r["x"] >= 1);
        // Parallel independent chains
        let g = graph_with(
            &["a", "b", "c", "d"],
            &[
                uc("a", ConstraintRelation::Lt, "b"),
                uc("c", ConstraintRelation::Lt, "d"),
            ],
        );
        let r = g.resolve().unwrap();
        assert_eq!((r["a"], r["b"], r["c"], r["d"]), (0, 1, 0, 1));
    }

    #[test]
    fn test_graph_eq_and_cycles() {
        // Eq constraint
        let g = graph_with(
            &["u", "v", "w"],
            &[
                uc("u", ConstraintRelation::Eq, "v"),
                uc("v", ConstraintRelation::Lt, "w"),
            ],
        );
        let r = g.resolve().unwrap();
        assert_eq!(r["u"], r["v"]);
        assert!(r["w"] > r["v"]);
        // Lt cycle: inconsistent
        let g = graph_with(
            &["u", "v"],
            &[
                uc("u", ConstraintRelation::Lt, "v"),
                uc("v", ConstraintRelation::Lt, "u"),
            ],
        );
        assert!(!g.is_consistent() && g.resolve().is_err());
        // Le cycle: consistent (same level)
        let g = graph_with(
            &["u", "v"],
            &[
                uc("u", ConstraintRelation::Le, "v"),
                uc("v", ConstraintRelation::Le, "u"),
            ],
        );
        assert!(g.is_consistent());
        assert_eq!(g.resolve().unwrap()["u"], g.resolve().unwrap()["v"]);
    }

    #[test]
    fn test_lower_levels() {
        let g = UniverseGraph::new();
        let mut res = hashbrown::HashMap::new();
        res.insert("u".to_owned(), 0u32);
        res.insert("v".to_owned(), 2u32);
        let mut w = ShardWriter::new();
        let flat = g.lower_levels(&res, &mut w);
        assert!(flat.contains_key("u") && flat.contains_key("v") && flat["v"] > flat["u"]);
    }

    #[test]
    fn test_instantiate_poly() {
        let pc = PolyConstant {
            name: "id".into(),
            universe_params: vec!["u".into()],
            constraints: vec![],
            type_: CicTerm::Prod(
                "A".into(),
                Box::new(CicTerm::Var("u".into())),
                Box::new(CicTerm::Prod(
                    "x".into(),
                    Box::new(CicTerm::Rel(0)),
                    Box::new(CicTerm::Rel(1)),
                )),
            ),
            body: Some(CicTerm::Lambda(
                "A".into(),
                Box::new(CicTerm::Var("u".into())),
                Box::new(CicTerm::Lambda(
                    "x".into(),
                    Box::new(CicTerm::Rel(0)),
                    Box::new(CicTerm::Rel(0)),
                )),
            )),
        };
        let (ty, body) = instantiate_poly(&pc, &[3]).unwrap();
        match &ty {
            CicTerm::Prod(_, t, _) => {
                assert!(matches!(
                    t.as_ref(),
                    CicTerm::Sort(CicSort::Type(CoqUniverseLevel::Type(3)))
                ))
            }
            other => panic!("expected Prod, got {other:?}"),
        }
        assert!(body.is_some());
        // Wrong level count
        let pc2 = PolyConstant {
            name: "f".into(),
            universe_params: vec!["u".into(), "v".into()],
            constraints: vec![],
            type_: CicTerm::Sort(CicSort::Prop),
            body: None,
        };
        assert!(instantiate_poly(&pc2, &[1]).is_err());
        // Empty params
        let pc3 = PolyConstant {
            name: "f".into(),
            universe_params: vec![],
            constraints: vec![],
            type_: CicTerm::Sort(CicSort::Prop),
            body: None,
        };
        let (ty, body) = instantiate_poly(&pc3, &[]).unwrap();
        assert!(matches!(ty, CicTerm::Sort(CicSort::Prop)) && body.is_none());
    }

    #[test]
    fn test_import_poly_constant() {
        let pc = PolyConstant {
            name: "id".into(),
            universe_params: vec!["u".into()],
            constraints: vec![],
            type_: CicTerm::Prod(
                "A".into(),
                Box::new(CicTerm::Var("u".into())),
                Box::new(CicTerm::Rel(0)),
            ),
            body: Some(CicTerm::Lambda(
                "A".into(),
                Box::new(CicTerm::Var("u".into())),
                Box::new(CicTerm::Rel(0)),
            )),
        };
        let mut w = ShardWriter::new();
        assert_eq!(
            import_poly_constant(&pc, "Coq.Init.Datatypes", &mut w).unwrap(),
            0
        );
        let mut buf = Vec::new();
        w.write(&mut buf).unwrap();
        let rd = crate::shard::ShardReader::from_bytes(&buf).unwrap();
        assert_eq!(rd.header.constant_count, 1);
        assert_eq!(rd.strings[rd.constants[0].name_idx as usize], "id");
        assert!(rd.constants[0].has_value() && rd.constants[0].profile().is_pure());
    }

    #[test]
    fn test_import_poly_axiom_and_constrained() {
        // Axiom with classical choice
        let pc = PolyConstant {
            name: "ax".into(),
            universe_params: vec!["u".into()],
            constraints: vec![],
            type_: CicTerm::Sort(CicSort::Prop),
            body: None,
        };
        let mut w = ShardWriter::new();
        import_poly_constant(&pc, "Coq.Logic.ClassicalChoice", &mut w).unwrap();
        let mut buf = Vec::new();
        w.write(&mut buf).unwrap();
        let rd = crate::shard::ShardReader::from_bytes(&buf).unwrap();
        assert!(
            !rd.constants[0].has_value() && rd.constants[0].profile().has(AxiomProfile::CHOICE)
        );
        // Constrained poly constant
        let pc = PolyConstant {
            name: "lift".into(),
            universe_params: vec!["u".into(), "v".into()],
            constraints: vec![uc("u", ConstraintRelation::Lt, "v")],
            type_: CicTerm::Prod(
                "A".into(),
                Box::new(CicTerm::Var("u".into())),
                Box::new(CicTerm::Var("v".into())),
            ),
            body: None,
        };
        let mut w = ShardWriter::new();
        assert_eq!(import_poly_constant(&pc, "Coq.Init", &mut w).unwrap(), 0);
        let mut buf = Vec::new();
        w.write(&mut buf).unwrap();
        assert_eq!(
            crate::shard::ShardReader::from_bytes(&buf)
                .unwrap()
                .header
                .constant_count,
            1
        );
    }
}
