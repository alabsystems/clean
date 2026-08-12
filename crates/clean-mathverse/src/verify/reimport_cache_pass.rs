// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Re-import verdict-cache **population pass** (P1 brick 3a) — see
//! `designs/2026-06-27-reimport-at-the-speed-of-a-hash.md`.
//!
//! This is a *post-pass*: it consumes a verify run's outputs (a constant
//! resolver + the list of `KernelVerified` names) and records each verified
//! declaration's verdict into a [`VerdictCache`] keyed by its Merkle-DAG
//! verified hash. It does **not** touch the verify loop and changes **no**
//! verdict — running it is observationally invisible to verification, so a real
//! run's `KernelVerified` count is unaffected. Its only effect is to populate a
//! cache that a *future* run can consult (the skip-path is a later brick).
//!
//! ALGORITHM: for each `KernelVerified` root, an iterative (stack-safe)
//! post-order traversal of its dependency closure computes, per constant, both
//! its verified hash `vh` and its transitive axiom closure, memoized across
//! roots. A constant on a dependency cycle — or transitively depending on an
//! unresolved name — is conservatively left uncomputed, so it is simply not
//! cached (and will be re-verified next time) rather than cached unsoundly.
//!
//! TRUSTED-DEP NOTE: imported constants are resolved from their `ConstantInfo`;
//! value-less family members (recursors/constructors) hash by type. Genuine
//! axioms (`ConstantKind::Axiom`) — and only those — enter the axiom closure.

use std::collections::{BTreeSet, HashMap, HashSet};

use clean_kernel::env::ConstantInfo;
use clean_kernel::{ConstantKind, Declaration, Environment, Name};

use super::verdict_cache::{CachedVerdict, VerdictCache};
use crate::verify::fingerprint::{decl_content_fingerprint, direct_dep_names};

/// A constant resolved into the form the pass needs: a [`Declaration`] to
/// fingerprint, plus whether it is a genuine axiom (for the axiom closure).
#[derive(Clone, Debug)]
pub(crate) struct ResolvedDecl {
    /// The declaration to fingerprint.
    pub(crate) decl: Declaration,
    /// Whether this constant is a genuine `ConstantKind::Axiom` (only these
    /// enter the transitive axiom closure — value-less recursors/constructors
    /// rendered as `Axiom` declarations for hashing do NOT).
    pub(crate) is_axiom: bool,
}

/// Memoized per-constant result: its verified hash and transitive axiom closure.
#[derive(Clone)]
struct NodeHash {
    vh: [u8; 32],
    axioms: BTreeSet<Name>,
}

/// What the population pass did.
#[derive(Debug, Default, PartialEq, Eq)]
pub(crate) struct PopulateStats {
    /// Verdicts recorded into the cache.
    pub(crate) recorded: usize,
    /// `KernelVerified` roots whose verified hash could not be computed (a
    /// dependency cycle or an unresolved dependency) and so were not cached.
    pub(crate) unresolved_or_cyclic: usize,
}

/// Render a kernel [`ConstantInfo`] as the [`Declaration`] used for content
/// fingerprinting. Value-bearing constants map to their kind; value-less
/// constants (axioms, and family members stored without a value) hash by type.
pub(crate) fn ci_to_declaration(name: &Name, ci: &ConstantInfo) -> Declaration {
    let level_params = ci.level_params.clone();
    let type_ = ci.type_.clone();
    match (ci.kind, ci.value.clone()) {
        (ConstantKind::Theorem, Some(value)) => Declaration::Theorem {
            name: name.clone(),
            level_params,
            type_,
            value,
        },
        (ConstantKind::Opaque, Some(value)) => Declaration::Opaque {
            name: name.clone(),
            level_params,
            type_,
            value,
        },
        (ConstantKind::Definition, Some(value)) => Declaration::Definition {
            name: name.clone(),
            level_params,
            type_,
            value,
            is_reducible: ci.is_reducible,
        },
        _ => Declaration::Axiom {
            name: name.clone(),
            level_params,
            type_,
        },
    }
}

/// Resolve a constant name against a kernel [`Environment`]. The env-backed
/// resolver the verify-path wiring (brick 3b) passes to [`populate_verdict_cache`].
pub(crate) fn env_resolved(env: &Environment, name: &Name) -> Option<ResolvedDecl> {
    let ci = env.get_const(name)?;
    Some(ResolvedDecl {
        decl: ci_to_declaration(name, ci),
        is_axiom: matches!(ci.kind, ConstantKind::Axiom),
    })
}

/// Resolve with a side cache so each name is resolved at most once.
fn resolve_cached(
    name: &Name,
    resolve: &impl Fn(&Name) -> Option<ResolvedDecl>,
    resolved: &mut HashMap<Name, Option<ResolvedDecl>>,
) -> Option<ResolvedDecl> {
    if let Some(cached) = resolved.get(name) {
        return cached.clone();
    }
    let rd = resolve(name);
    resolved.insert(name.clone(), rd.clone());
    rd
}

enum Step {
    Enter(Name),
    Exit(Name),
}

/// Populate `memo` with the verified hash + axiom closure of every computable
/// constant in `root`'s dependency closure (iterative post-order, stack-safe).
fn build_node_hash(
    root: &Name,
    resolve: &impl Fn(&Name) -> Option<ResolvedDecl>,
    memo: &mut HashMap<Name, NodeHash>,
    resolved: &mut HashMap<Name, Option<ResolvedDecl>>,
) {
    let mut stack = vec![Step::Enter(root.clone())];
    let mut on_path: HashSet<Name> = HashSet::new();
    while let Some(step) = stack.pop() {
        match step {
            Step::Enter(name) => {
                // Already hashed, or a back-edge (cycle): do not descend. A
                // cyclic node stays unmemoized, so its dependents skip it.
                if memo.contains_key(&name) || on_path.contains(&name) {
                    continue;
                }
                let Some(rd) = resolve_cached(&name, resolve, resolved) else {
                    continue; // unresolved name: leave unmemoized
                };
                on_path.insert(name.clone());
                stack.push(Step::Exit(name.clone()));
                for dep in direct_dep_names(&rd.decl) {
                    if !memo.contains_key(&dep) {
                        stack.push(Step::Enter(dep));
                    }
                }
            }
            Step::Exit(name) => {
                on_path.remove(&name);
                let Some(rd) = resolve_cached(&name, resolve, resolved) else {
                    continue;
                };
                let Ok(leaf) = decl_content_fingerprint(&rd.decl) else {
                    continue;
                };
                let mut dep_vhs: Vec<[u8; 32]> = Vec::new();
                let mut axioms: BTreeSet<Name> = BTreeSet::new();
                let mut all_deps_hashed = true;
                for dep in direct_dep_names(&rd.decl) {
                    match memo.get(&dep) {
                        Some(n) => {
                            dep_vhs.push(n.vh);
                            axioms.extend(n.axioms.iter().cloned());
                        }
                        None => {
                            all_deps_hashed = false; // a dep is cyclic/unresolved
                            break;
                        }
                    }
                }
                if !all_deps_hashed {
                    continue;
                }
                if rd.is_axiom {
                    axioms.insert(name.clone());
                }
                dep_vhs.sort_unstable();
                let mut hasher = blake3::Hasher::new();
                hasher.update(&leaf);
                for d in &dep_vhs {
                    hasher.update(d);
                }
                memo.insert(
                    name,
                    NodeHash {
                        vh: *hasher.finalize().as_bytes(),
                        axioms,
                    },
                );
            }
        }
    }
}

/// Record a `{kernel_verified, axiom_closure}` verdict for every name in
/// `kernel_verified_names` whose verified hash is computable, keyed by that
/// hash. Returns what was recorded vs. skipped. Soundness-neutral: it only
/// reads through `resolve` and writes to `cache`.
pub(crate) fn populate_verdict_cache(
    resolve: impl Fn(&Name) -> Option<ResolvedDecl>,
    kernel_verified_names: &[Name],
    cache: &mut VerdictCache,
) -> PopulateStats {
    let mut memo: HashMap<Name, NodeHash> = HashMap::new();
    let mut resolved: HashMap<Name, Option<ResolvedDecl>> = HashMap::new();
    for root in kernel_verified_names {
        build_node_hash(root, &resolve, &mut memo, &mut resolved);
    }
    let mut stats = PopulateStats::default();
    for root in kernel_verified_names {
        match memo.get(root) {
            Some(node) => {
                cache.record(
                    node.vh,
                    CachedVerdict {
                        kernel_verified: true,
                        axiom_closure: node.axioms.iter().cloned().collect(),
                    },
                );
                stats.recorded += 1;
            }
            None => stats.unresolved_or_cyclic += 1,
        }
    }
    stats
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::verify::fingerprint::decl_verified_hash;
    use clean_kernel::expr::{Expr, ExprKind};

    fn bv0() -> Expr {
        Expr::from_kind(ExprKind::BVar(0)) // a leaf with no constant dependencies
    }
    fn cst(s: &str) -> Expr {
        Expr::from_kind(ExprKind::Const(Name::from_string(s), Default::default()))
    }
    fn axiom(name: &str, type_: Expr) -> ResolvedDecl {
        ResolvedDecl {
            decl: Declaration::Axiom {
                name: Name::from_string(name),
                level_params: vec![],
                type_,
            },
            is_axiom: true,
        }
    }
    fn def(name: &str, type_: Expr, value: Expr) -> ResolvedDecl {
        ResolvedDecl {
            decl: Declaration::Definition {
                name: Name::from_string(name),
                level_params: vec![],
                type_,
                value,
                is_reducible: false,
            },
            is_axiom: false,
        }
    }
    fn thm(name: &str, type_: Expr, value: Expr) -> ResolvedDecl {
        ResolvedDecl {
            decl: Declaration::Theorem {
                name: Name::from_string(name),
                level_params: vec![],
                type_,
                value,
            },
            is_axiom: false,
        }
    }
    fn world(pairs: Vec<(&str, ResolvedDecl)>) -> HashMap<Name, ResolvedDecl> {
        pairs
            .into_iter()
            .map(|(n, rd)| (Name::from_string(n), rd))
            .collect()
    }

    #[test]
    fn test_populate_records_verified_hashes_and_axiom_closure() {
        // Leaf (axiom, no deps) <- Mid (def) <- Top (thm). Top and Mid both
        // transitively depend on the axiom Leaf.
        let w = world(vec![
            ("Leaf", axiom("Leaf", bv0())),
            ("Mid", def("Mid", bv0(), cst("Leaf"))),
            ("Top", thm("Top", cst("Mid"), cst("Leaf"))),
        ]);
        let mut cache = VerdictCache::new();
        let kv = [Name::from_string("Top"), Name::from_string("Mid")];
        let stats = populate_verdict_cache(|n| w.get(n).cloned(), &kv, &mut cache);
        assert_eq!(
            stats,
            PopulateStats {
                recorded: 2,
                unresolved_or_cyclic: 0
            }
        );

        // The pass must produce exactly the brick-2 verified hash. Recompute
        // Mid's vh independently and confirm its cached verdict.
        let vh_leaf = decl_verified_hash(&w[&Name::from_string("Leaf")].decl, |_| None)
            .unwrap()
            .unwrap();
        let vh_mid = decl_verified_hash(&w[&Name::from_string("Mid")].decl, |d| {
            (d == &Name::from_string("Leaf")).then_some(vh_leaf)
        })
        .unwrap()
        .unwrap();
        let verdict = cache.lookup(&vh_mid).expect("Mid cached under its vh");
        assert!(verdict.kernel_verified);
        assert_eq!(
            verdict.axiom_closure,
            vec![Name::from_string("Leaf")],
            "Mid's transitive axiom closure is {{Leaf}}"
        );
    }

    #[test]
    fn test_populate_skips_dependency_cycle() {
        // C1 <-> C2 mutual cycle: neither is cacheable.
        let w = world(vec![
            ("C1", def("C1", bv0(), cst("C2"))),
            ("C2", def("C2", bv0(), cst("C1"))),
        ]);
        let mut cache = VerdictCache::new();
        let stats = populate_verdict_cache(
            |n| w.get(n).cloned(),
            &[Name::from_string("C1")],
            &mut cache,
        );
        assert_eq!(
            stats,
            PopulateStats {
                recorded: 0,
                unresolved_or_cyclic: 1
            }
        );
        assert!(cache.is_empty(), "a cyclic decl is never cached");
    }

    #[test]
    fn test_populate_skips_unresolved_dependency() {
        // U depends on Missing, which the resolver does not know.
        let w = world(vec![("U", thm("U", cst("Missing"), bv0()))]);
        let mut cache = VerdictCache::new();
        let stats =
            populate_verdict_cache(|n| w.get(n).cloned(), &[Name::from_string("U")], &mut cache);
        assert_eq!(
            stats,
            PopulateStats {
                recorded: 0,
                unresolved_or_cyclic: 1
            }
        );
        assert!(cache.is_empty(), "an unresolved-dep decl is never cached");
    }

    /// Brick 3b's core claim: the env-backed resolver [`env_resolved`] +
    /// [`populate_verdict_cache`] work against a REAL kernel [`Environment`] —
    /// resolving genuine `ConstantInfo`s, hashing their real dependency closures,
    /// and computing real transitive axiom closures.
    #[test]
    fn test_populate_over_real_kernel_environment() {
        use clean_kernel::Environment;

        // Prelude + two axioms: `A : Prop`, and `B : A` (B depends on A).
        let mut env = Environment::with_prelude();
        let a = Name::from_string("ReimportTest.A");
        let b = Name::from_string("ReimportTest.B");
        env.add_decl(Declaration::Axiom {
            name: a.clone(),
            level_params: vec![],
            type_: Expr::prop(),
        })
        .expect("add axiom A : Prop");
        env.add_decl(Declaration::Axiom {
            name: b.clone(),
            level_params: vec![],
            type_: Expr::from_kind(ExprKind::Const(a.clone(), Default::default())),
        })
        .expect("add axiom B : A");

        let mut cache = VerdictCache::new();
        let stats = populate_verdict_cache(
            |n| env_resolved(&env, n),
            &[a.clone(), b.clone()],
            &mut cache,
        );
        assert_eq!(
            stats,
            PopulateStats {
                recorded: 2,
                unresolved_or_cyclic: 0
            },
            "both real-env axioms hash + cache via env_resolved"
        );

        // Cross-check the pass's vh against brick-2's decl_verified_hash on the
        // SAME real-env declarations, and confirm B's transitive axiom closure.
        let vh_a = decl_verified_hash(&env_resolved(&env, &a).unwrap().decl, |_| None)
            .unwrap()
            .unwrap();
        let vh_b = decl_verified_hash(&env_resolved(&env, &b).unwrap().decl, |d| {
            (d == &a).then_some(vh_a)
        })
        .unwrap()
        .unwrap();
        let verdict_b = cache.lookup(&vh_b).expect("B cached under its real-env vh");
        assert!(verdict_b.kernel_verified);
        assert!(
            verdict_b.axiom_closure.contains(&a) && verdict_b.axiom_closure.contains(&b),
            "B's transitive axiom closure is {{A, B}}"
        );
        assert_eq!(verdict_b.axiom_closure.len(), 2);
    }
}
