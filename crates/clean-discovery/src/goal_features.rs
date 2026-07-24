// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Goal feature extraction for the tactic learning k-NN recommender.
//!
//! Extracts structural features from goal expressions (head symbol, argument
//! types, depth, size, binder count) and produces normalized feature vectors
//! for distance-based similarity computation.
//!
//! Part of #3187.

use clean_kernel::{Expr, ExprKind, Literal};
use serde::{Deserialize, Serialize};

/// Tag classifying the head type of a goal argument for fingerprinting.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[non_exhaustive]
pub enum ArgTypeTag {
    /// Prop sort (Sort with level 0).
    Prop,
    /// Natural number literal.
    NatLit,
    /// Non-Prop sort.
    Sort,
    /// Named constant at application head.
    NamedConst,
    /// Application expression.
    App,
    /// Binder (Pi or Lam).
    Binder,
    /// Variable (bound or free).
    Var,
    /// Anything else.
    Other,
}

/// Structural features extracted from a goal expression.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct GoalFeatures {
    /// Head symbol of the goal's application spine (if it is a constant).
    pub head_symbol: Option<String>,
    /// Number of arguments in the application spine.
    pub arg_count: usize,
    /// Maximum nesting depth of the expression tree.
    pub depth: usize,
    /// Total node count in the expression tree.
    pub size: usize,
    /// Count of Pi and Lam (binder) nodes.
    pub num_binders: usize,
    /// Count of App nodes.
    pub num_apps: usize,
    /// Whether a Prop sort appears anywhere in the tree.
    pub has_prop: bool,
    /// Whether a natural number literal appears anywhere in the tree.
    pub has_nat_lit: bool,
    /// Type tags for each argument in the application spine.
    pub arg_type_fingerprint: Vec<ArgTypeTag>,
}

/// Normalized feature vector for distance computation.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct FeatureVector {
    /// Normalized feature values in [0, 1].
    pub values: Vec<f64>,
}

/// Internal metrics gathered in a single tree walk.
struct TreeMetrics {
    size: usize,
    num_binders: usize,
    num_apps: usize,
    has_prop: bool,
    has_nat_lit: bool,
}

/// Extract structural features from a goal expression.
///
/// Uses iterative traversal (explicit work stack) to avoid stack overflow
/// on deeply nested expressions.
#[must_use]
pub fn extract_goal_features(expr: &Expr) -> GoalFeatures {
    // Head symbol via application spine.
    let head = expr.get_app_fn();
    let head_symbol = if let ExprKind::Const(name, _) = head.kind() {
        Some(name.to_string())
    } else {
        None
    };

    // Arguments of the application spine.
    let args = expr.get_app_args();
    let arg_count = args.len();
    let arg_type_fingerprint: Vec<ArgTypeTag> = args.iter().map(|a| classify_arg_type(a)).collect();

    let depth = compute_depth(expr);
    let metrics = compute_metrics(expr);

    GoalFeatures {
        head_symbol,
        arg_count,
        depth,
        size: metrics.size,
        num_binders: metrics.num_binders,
        num_apps: metrics.num_apps,
        has_prop: metrics.has_prop,
        has_nat_lit: metrics.has_nat_lit,
        arg_type_fingerprint,
    }
}

/// Classify the head type of an argument expression.
pub fn classify_arg_type(expr: &Expr) -> ArgTypeTag {
    let head = expr.get_app_fn();
    match head.kind() {
        ExprKind::Sort(level) => {
            if level.is_zero() {
                ArgTypeTag::Prop
            } else {
                ArgTypeTag::Sort
            }
        }
        ExprKind::Const(_, _) => ArgTypeTag::NamedConst,
        ExprKind::Lit(Literal::Nat(_)) => ArgTypeTag::NatLit,
        ExprKind::Lit(_) => ArgTypeTag::Other,
        ExprKind::App(_, _) => ArgTypeTag::App,
        ExprKind::Pi(_, _, _) | ExprKind::Lam(_, _, _) => ArgTypeTag::Binder,
        ExprKind::BVar(_) | ExprKind::FVar(_) => ArgTypeTag::Var,
        _ => ArgTypeTag::Other,
    }
}

/// Compute the maximum nesting depth of an expression tree iteratively.
///
/// Each node contributes depth 1; children are explored via explicit stack.
fn compute_depth(expr: &Expr) -> usize {
    // Stack entries: (expression, current_depth)
    let mut stack: Vec<(&Expr, usize)> = vec![(expr, 1)];
    let mut max_depth: usize = 0;

    while let Some((e, d)) = stack.pop() {
        if d > max_depth {
            max_depth = d;
        }
        match e.kind() {
            ExprKind::BVar(_)
            | ExprKind::FVar(_)
            | ExprKind::Sort(_)
            | ExprKind::Const(_, _)
            | ExprKind::Lit(_) => {}
            ExprKind::App(f, a) => {
                stack.push((f, d + 1));
                stack.push((a, d + 1));
            }
            ExprKind::Lam(_, domain, body) | ExprKind::Pi(_, domain, body) => {
                stack.push((domain, d + 1));
                stack.push((body, d + 1));
            }
            ExprKind::Let(_, ty, val, body, _) => {
                stack.push((ty, d + 1));
                stack.push((val, d + 1));
                stack.push((body, d + 1));
            }
            ExprKind::Proj(_, _, inner) | ExprKind::MData(_, inner) => {
                stack.push((inner, d + 1));
            }
            _ => {}
        }
    }

    max_depth
}

/// Single-pass iterative walk to gather tree metrics.
fn compute_metrics(expr: &Expr) -> TreeMetrics {
    let mut metrics = TreeMetrics {
        size: 0,
        num_binders: 0,
        num_apps: 0,
        has_prop: false,
        has_nat_lit: false,
    };

    let mut stack: Vec<&Expr> = vec![expr];

    while let Some(e) = stack.pop() {
        metrics.size += 1;

        match e.kind() {
            ExprKind::Sort(level) if level.is_zero() => {
                metrics.has_prop = true;
            }
            ExprKind::Lit(Literal::Nat(_)) => {
                metrics.has_nat_lit = true;
            }
            ExprKind::App(f, a) => {
                metrics.num_apps += 1;
                stack.push(f);
                stack.push(a);
            }
            ExprKind::Lam(_, domain, body) | ExprKind::Pi(_, domain, body) => {
                metrics.num_binders += 1;
                stack.push(domain);
                stack.push(body);
            }
            ExprKind::Let(_, ty, val, body, _) => {
                stack.push(ty);
                stack.push(val);
                stack.push(body);
            }
            ExprKind::Proj(_, _, inner) | ExprKind::MData(_, inner) => {
                stack.push(inner);
            }
            _ => {}
        }
    }

    metrics
}

// ── Normalization constants ──────────────────────────────────────────────

const MAX_DEPTH_NORM: f64 = 50.0;
const MAX_SIZE_NORM: f64 = 500.0;
const MAX_BINDERS_NORM: f64 = 20.0;
const MAX_APPS_NORM: f64 = 50.0;
const MAX_ARGS_NORM: f64 = 20.0;

impl GoalFeatures {
    /// Convert to a normalized feature vector for distance computation.
    ///
    /// Features are clamped to [0, 1].
    #[must_use]
    pub fn to_feature_vector(&self) -> FeatureVector {
        let values = vec![
            (self.depth as f64 / MAX_DEPTH_NORM).min(1.0),
            (self.size as f64 / MAX_SIZE_NORM).min(1.0),
            (self.num_binders as f64 / MAX_BINDERS_NORM).min(1.0),
            (self.num_apps as f64 / MAX_APPS_NORM).min(1.0),
            (self.arg_count as f64 / MAX_ARGS_NORM).min(1.0),
            if self.has_prop { 1.0 } else { 0.0 },
            if self.has_nat_lit { 1.0 } else { 0.0 },
        ];
        FeatureVector { values }
    }
}

impl FeatureVector {
    /// Euclidean (L2) distance between two feature vectors.
    ///
    /// Dimensions beyond the shorter vector are treated as zero.
    #[must_use]
    pub fn euclidean_distance(&self, other: &FeatureVector) -> f64 {
        let max_len = self.values.len().max(other.values.len());
        let mut sum = 0.0_f64;
        for i in 0..max_len {
            let a = self.values.get(i).copied().unwrap_or(0.0);
            let b = other.values.get(i).copied().unwrap_or(0.0);
            let diff = a - b;
            sum += diff * diff;
        }
        sum.sqrt()
    }

    /// Weighted Euclidean distance. Falls back to unweighted for dimensions
    /// beyond the weights vector.
    #[must_use]
    pub fn weighted_distance(&self, other: &FeatureVector, weights: &[f64]) -> f64 {
        let max_len = self.values.len().max(other.values.len());
        let mut sum = 0.0_f64;
        for i in 0..max_len {
            let a = self.values.get(i).copied().unwrap_or(0.0);
            let b = other.values.get(i).copied().unwrap_or(0.0);
            let w = weights.get(i).copied().unwrap_or(1.0);
            let diff = a - b;
            sum += w * diff * diff;
        }
        sum.sqrt()
    }

    /// Cosine similarity in [−1, 1].
    ///
    /// Returns 0.0 when either vector has zero magnitude.
    #[must_use]
    pub fn cosine_similarity(&self, other: &FeatureVector) -> f64 {
        let max_len = self.values.len().max(other.values.len());
        let mut dot = 0.0_f64;
        let mut mag_a = 0.0_f64;
        let mut mag_b = 0.0_f64;
        for i in 0..max_len {
            let a = self.values.get(i).copied().unwrap_or(0.0);
            let b = other.values.get(i).copied().unwrap_or(0.0);
            dot += a * b;
            mag_a += a * a;
            mag_b += b * b;
        }
        let denom = mag_a.sqrt() * mag_b.sqrt();
        if denom < f64::EPSILON {
            return 0.0;
        }
        dot / denom
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_extract_features_const() {
        let expr = Expr::const_str("Nat.add");
        let features = extract_goal_features(&expr);
        assert_eq!(features.head_symbol.as_deref(), Some("Nat.add"));
        assert_eq!(features.arg_count, 0);
        assert_eq!(features.size, 1);
        assert_eq!(features.depth, 1);
        assert!(!features.has_prop);
        assert!(!features.has_nat_lit);
    }

    #[test]
    fn test_extract_features_app() {
        let f = Expr::const_str("f");
        let x = Expr::const_str("x");
        let app = Expr::app(f, x);
        let features = extract_goal_features(&app);
        assert_eq!(features.head_symbol.as_deref(), Some("f"));
        assert_eq!(features.arg_count, 1);
        assert_eq!(features.num_apps, 1);
        assert_eq!(features.size, 3); // app + f + x
        assert_eq!(features.depth, 2);
    }

    #[test]
    fn test_extract_features_nested_app() {
        let f = Expr::const_str("g");
        let a = Expr::const_str("a");
        let b = Expr::const_str("b");
        let inner = Expr::app(f, a);
        let outer = Expr::app(inner, b);
        let features = extract_goal_features(&outer);
        assert_eq!(features.head_symbol.as_deref(), Some("g"));
        assert_eq!(features.arg_count, 2);
        assert_eq!(features.num_apps, 2);
        assert_eq!(features.size, 5);
    }

    #[test]
    fn test_extract_features_prop_sort() {
        let prop = Expr::prop();
        let features = extract_goal_features(&prop);
        assert!(features.has_prop);
        assert_eq!(features.size, 1);
        assert!(features.head_symbol.is_none());
    }

    #[test]
    fn test_feature_vector_euclidean_distance_identical() {
        let features = GoalFeatures {
            head_symbol: Some("f".to_string()),
            arg_count: 2,
            depth: 3,
            size: 5,
            num_binders: 0,
            num_apps: 2,
            has_prop: false,
            has_nat_lit: false,
            arg_type_fingerprint: vec![],
        };
        let v = features.to_feature_vector();
        let dist = v.euclidean_distance(&v);
        assert!(
            dist.abs() < 1e-10,
            "distance of identical vectors should be ~0"
        );
    }

    #[test]
    fn test_feature_vector_cosine_similarity_identical() {
        let v = FeatureVector {
            values: vec![1.0, 2.0, 3.0],
        };
        let sim = v.cosine_similarity(&v);
        assert!(
            (sim - 1.0).abs() < 1e-10,
            "cosine similarity of identical vectors should be ~1.0"
        );
    }

    #[test]
    fn test_feature_vector_cosine_similarity_zero() {
        let v = FeatureVector {
            values: vec![0.0, 0.0],
        };
        let sim = v.cosine_similarity(&v);
        assert!(
            sim.abs() < 1e-10,
            "cosine similarity of zero vectors should be 0"
        );
    }

    #[test]
    fn test_classify_arg_type_const() {
        let c = Expr::const_str("Nat");
        assert_eq!(classify_arg_type(&c), ArgTypeTag::NamedConst);
    }

    #[test]
    fn test_classify_arg_type_prop() {
        let p = Expr::prop();
        assert_eq!(classify_arg_type(&p), ArgTypeTag::Prop);
    }

    #[test]
    fn test_classify_arg_type_bvar() {
        let v = Expr::bvar(0);
        assert_eq!(classify_arg_type(&v), ArgTypeTag::Var);
    }

    #[test]
    fn test_weighted_distance_matches_unweighted_with_unit_weights() {
        let a = FeatureVector {
            values: vec![0.1, 0.5, 0.9],
        };
        let b = FeatureVector {
            values: vec![0.2, 0.6, 0.8],
        };
        let unit_weights = vec![1.0, 1.0, 1.0];
        let d1 = a.euclidean_distance(&b);
        let d2 = a.weighted_distance(&b, &unit_weights);
        assert!(
            (d1 - d2).abs() < 1e-10,
            "unit-weighted distance should equal euclidean"
        );
    }
}
