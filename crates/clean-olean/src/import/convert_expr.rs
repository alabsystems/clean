// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Expression conversion from parsed .olean format to kernel `Expr`.
//!
//! Handles iterative (stack-safe) conversion of `ParsedExpr` trees to kernel
//! `Expr` with hash-consing for structure sharing (#2383).

use super::{ExprInternCache, ExprSharingStats, ImportError};
use crate::expr::{ParsedBinderInfo, ParsedExpr, ParsedLiteral};
use crate::level::ParsedLevel;
use clean_kernel::expr::{BigNat, BinderInfo, Expr, ExprKind, FVarId, LevelVec, Literal, MDataMap};
use clean_kernel::level::Level;
use clean_kernel::name::Name;
use smallvec::SmallVec;
use std::hash::{BuildHasher, Hasher};
use std::sync::Arc;

use ahash::RandomState;

pub(crate) fn convert_binder_info(info: ParsedBinderInfo) -> BinderInfo {
    match info {
        ParsedBinderInfo::Default => BinderInfo::Default,
        ParsedBinderInfo::Implicit => BinderInfo::Implicit,
        ParsedBinderInfo::StrictImplicit => BinderInfo::StrictImplicit,
        ParsedBinderInfo::InstImplicit => BinderInfo::InstImplicit,
        // Unknown binder kinds from future Lean versions - treat as explicit.
        // The Unknown variant preserves the tag value for callers that want
        // stricter checking via ParsedBinderInfo::is_unknown().
        _ => BinderInfo::Default,
    }
}

pub(crate) fn convert_level(name: &str, level: &ParsedLevel) -> Result<Level, ImportError> {
    match level {
        ParsedLevel::Zero => Ok(Level::zero()),
        ParsedLevel::Succ(l) => Ok(Level::succ(convert_level(name, l)?)),
        ParsedLevel::Max(l, r) => Ok(Level::max(convert_level(name, l)?, convert_level(name, r)?)),
        ParsedLevel::IMax(l, r) => Ok(Level::imax(
            convert_level(name, l)?,
            convert_level(name, r)?,
        )),
        // Level parameters often reuse names like "u", "v" across many constants
        ParsedLevel::Param(n) => Ok(Level::param(Name::interned(n))),
        ParsedLevel::MVar(_) => Err(ImportError::UnsupportedMVar(name.to_string())),
    }
}

pub(super) fn convert_level_params(params: &[String]) -> Vec<Name> {
    params
        .iter()
        .map(|p| {
            if p.is_empty() {
                Name::anon()
            } else {
                Name::interned(p)
            }
        })
        .collect()
}

/// Work item for iterative expression conversion (avoids stack overflow on deep trees).
enum ConvertWork<'a> {
    /// Process this expression and push children
    Process(&'a ParsedExpr),
    /// Build App from top 2 results
    BuildApp,
    /// Build Lam from top 2 results
    BuildLam(BinderInfo),
    /// Build Pi from top 2 results
    BuildPi(BinderInfo),
    /// Build Let from top 3 results, carrying binder name and nonDep flag
    BuildLet(Name, bool),
    /// Build MData from top result
    BuildMData,
    /// Build Proj from top result
    BuildProj(Name, u32),
}

/// Look up or insert an expression in the intern cache.
///
/// Returns a shared `Arc<Expr>` — structurally identical expressions share the
/// same heap allocation, preserving the structure sharing from the olean's
/// compacted region at the kernel Expr level.
///
/// Returns `(arc, was_hit)` where `was_hit` is true if a cached Arc was reused.
pub(crate) fn intern_expr(cache: &mut ExprInternCache, expr: Expr) -> (Arc<Expr>, bool) {
    let h = expr.hash_cached();
    let bucket = cache.map.entry(h).or_default();
    for existing in bucket.iter() {
        if **existing == expr {
            return (Arc::clone(existing), true);
        }
    }
    let arc = Arc::new(expr);
    bucket.push(Arc::clone(&arc));
    cache.total_entries += 1;
    (arc, false)
}

/// Iterative expression conversion with hash-consing for structure sharing.
///
/// Structurally identical sub-expressions share the same `Arc<Expr>` allocation.
/// This preserves the structure sharing that exists in Lean 4's compacted region
/// format, reducing memory proportional to the sharing factor (#2383).
///
/// The `intern` cache is shared across all constants in a module so that common
/// sub-expressions (e.g. `Nat`, `Prop`, `List Nat`) are deduplicated globally.
///
/// Returns the converted expression and per-call sharing statistics.
/// `unique_exprs` is the per-call delta (new entries added to the shared cache).
pub(crate) fn convert_expr(
    name: &str,
    expr: &ParsedExpr,
    intern: &mut ExprInternCache,
) -> Result<(Expr, ExprSharingStats), ImportError> {
    let mut work: SmallVec<[ConvertWork<'_>; 64]> = SmallVec::new();
    // Results stack holds Arc<Expr> so Build* steps reuse interned children
    // directly as ExprKind fields, giving true pointer-level sharing.
    let mut results: SmallVec<[Arc<Expr>; 32]> = SmallVec::new();
    let cache_size_before: u64 = intern.total_entries;
    let mut cache_hits: u64 = 0;
    let mut total_intern_calls: u64 = 0;

    // Helper: call intern_expr and track stats inline via the returned hit flag.
    macro_rules! do_intern {
        ($cache:expr, $e:expr) => {{
            let (arc, was_hit) = intern_expr($cache, $e);
            total_intern_calls += 1;
            if was_hit {
                cache_hits += 1;
            }
            arc
        }};
    }

    work.push(ConvertWork::Process(expr));

    while let Some(item) = work.pop() {
        match item {
            ConvertWork::Process(e) => match e {
                ParsedExpr::BVar(i) => {
                    if *i > u64::from(Expr::MAX_BVAR_INDEX) {
                        return Err(ImportError::ExprConversion {
                            name: name.to_string(),
                            message: format!(
                                "bvar index too large: {i} (max {})",
                                Expr::MAX_BVAR_INDEX
                            ),
                        });
                    }
                    results.push(do_intern!(intern, Expr::bvar(*i as u32)));
                }
                ParsedExpr::FVar(id) => {
                    results.push(do_intern!(intern, Expr::fvar(FVarId::new(hash_str(id)))));
                }
                ParsedExpr::MVar(_) => {
                    return Err(ImportError::UnsupportedMVar(name.to_string()));
                }
                ParsedExpr::Sort(lvl) => {
                    results.push(do_intern!(intern, Expr::sort(convert_level(name, lvl)?)));
                }
                ParsedExpr::Const(n, lvls) => {
                    let levels: LevelVec = lvls
                        .iter()
                        .map(|l| convert_level(name, l))
                        .collect::<Result<_, _>>()?;
                    results.push(do_intern!(intern, Expr::const_(Name::interned(n), levels)));
                }
                ParsedExpr::Lit(lit) => {
                    let expr = match lit {
                        ParsedLiteral::Nat(n) => {
                            let kernel_bignat = match n {
                                crate::expr::BigNat::Small(v) => BigNat::Small(*v),
                                crate::expr::BigNat::Big(limbs) => {
                                    BigNat::from_limbs(limbs.clone())
                                }
                            };
                            Expr::from_kind(ExprKind::Lit(Literal::Nat(kernel_bignat)))
                        }
                        ParsedLiteral::String(s) => {
                            Expr::from_kind(ExprKind::Lit(Literal::String(s.clone().into())))
                        }
                    };
                    results.push(do_intern!(intern, expr));
                }
                ParsedExpr::App(f, a) => {
                    work.push(ConvertWork::BuildApp);
                    work.push(ConvertWork::Process(a));
                    work.push(ConvertWork::Process(f));
                }
                ParsedExpr::Lam(_, ty, body, info) => {
                    let binder_info = convert_binder_info(*info);
                    work.push(ConvertWork::BuildLam(binder_info));
                    work.push(ConvertWork::Process(body));
                    work.push(ConvertWork::Process(ty));
                }
                ParsedExpr::ForallE(_, ty, body, info) => {
                    let binder_info = convert_binder_info(*info);
                    work.push(ConvertWork::BuildPi(binder_info));
                    work.push(ConvertWork::Process(body));
                    work.push(ConvertWork::Process(ty));
                }
                ParsedExpr::LetE(decl_name, ty, val, body, nondep) => {
                    let let_name = Name::from_string(decl_name);
                    work.push(ConvertWork::BuildLet(let_name, *nondep));
                    work.push(ConvertWork::Process(body));
                    work.push(ConvertWork::Process(val));
                    work.push(ConvertWork::Process(ty));
                }
                ParsedExpr::MData(inner) => {
                    work.push(ConvertWork::BuildMData);
                    work.push(ConvertWork::Process(inner));
                }
                ParsedExpr::Proj(struct_name, idx, inner) => {
                    if *idx > u64::from(u32::MAX) {
                        return Err(ImportError::ExprConversion {
                            name: name.to_string(),
                            message: format!("projection index too large: {idx}"),
                        });
                    }
                    work.push(ConvertWork::BuildProj(
                        Name::interned(struct_name),
                        *idx as u32,
                    ));
                    work.push(ConvertWork::Process(inner));
                }
            },
            ConvertWork::BuildApp => {
                let arg = results.pop().expect("stack balance invariant");
                let func = results.pop().expect("stack balance invariant");
                let kind = ExprKind::App(func, arg);
                results.push(do_intern!(intern, Expr::from_kind(kind)));
            }
            ConvertWork::BuildLam(info) => {
                let body = results.pop().expect("stack balance invariant");
                let ty = results.pop().expect("stack balance invariant");
                let kind = ExprKind::Lam(info.into(), ty, body);
                results.push(do_intern!(intern, Expr::from_kind(kind)));
            }
            ConvertWork::BuildPi(info) => {
                let body = results.pop().expect("stack balance invariant");
                let ty = results.pop().expect("stack balance invariant");
                let kind = ExprKind::Pi(info.into(), ty, body);
                results.push(do_intern!(intern, Expr::from_kind(kind)));
            }
            ConvertWork::BuildLet(let_name, nondep) => {
                let body = results.pop().expect("stack balance invariant");
                let val = results.pop().expect("stack balance invariant");
                let ty = results.pop().expect("stack balance invariant");
                let kind = ExprKind::Let(let_name, ty, val, body, nondep);
                results.push(do_intern!(intern, Expr::from_kind(kind)));
            }
            ConvertWork::BuildMData => {
                let inner = results.pop().expect("stack balance invariant");
                let kind = ExprKind::MData(MDataMap::new(), inner);
                results.push(do_intern!(intern, Expr::from_kind(kind)));
            }
            ConvertWork::BuildProj(struct_name, idx) => {
                let inner = results.pop().expect("stack balance invariant");
                let kind = ExprKind::Proj(struct_name, idx, inner);
                results.push(do_intern!(intern, Expr::from_kind(kind)));
            }
        }
    }

    debug_assert_eq!(results.len(), 1);
    let unique_exprs = intern.total_entries - cache_size_before;
    let stats = ExprSharingStats {
        total_intern_calls,
        cache_hits,
        unique_exprs,
    };
    let result_arc = results.pop().expect("stack balance invariant");
    Ok((
        Arc::try_unwrap(result_arc).unwrap_or_else(|arc| (*arc).clone()),
        stats,
    ))
}

/// Deterministic hash of an FVar/MVar name into an `FVarId`.
///
/// Fixed-seed ahash (`with_seeds(0,0,0,0)`) — process-independent and stable
/// across runs and crates. This is the SINGLE source of truth for FVar
/// identity in BOTH the eager olean import (`convert_expr_direct`) and the lazy
/// `.mathverse` shard builder (`clean_mathverse::lean4::olean::alpha`). Using a
/// different hasher in either path gives a different id for the same name, which
/// makes the reconstructed `Expr` non-identical and breaks eager-vs-lazy
/// KernelVerified verdict parity (observed: `FVar(0)` vs `FVar(1)` type
/// mismatches on the `Membership`-binder-heavy decls in `Mathlib/Logic/Basic`).
pub fn hash_str(s: &str) -> u64 {
    let mut hasher = RandomState::with_seeds(0, 0, 0, 0).build_hasher();
    hasher.write(s.as_bytes());
    hasher.finish()
}
