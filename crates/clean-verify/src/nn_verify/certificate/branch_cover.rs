// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Branch-cover certificate checks for simple numeric domains.
//!
//! The verifier is intentionally small and conservative: a certificate is a
//! declared axis-aligned input box plus a finite set of branch boxes. It accepts
//! only when every branch stays inside the declared domain and every cell in
//! the finite breakpoint grid induced by branch/domain bounds is covered.
//!
//! This lane backs the `broken_branch_cover` false control
//! (`clean_mathverse::false_control_suite::FalseControlId::BrokenBranchCover`):
//! a cover with a hole, an escaping branch, or a malformed box must be
//! REJECTED. Every check below is fail-closed; there is no "accept on doubt"
//! branch.

use thiserror::Error;

/// Absolute slack applied to every bound comparison.
///
/// Branch boxes come from float-valued analyses whose endpoints agree only up
/// to rounding, so exact `==` on a shared breakpoint would report spurious
/// holes. The tolerance is one-sided in the accepting direction, which is why
/// gaps thinner than `EPSILON` are treated as closed.
const EPSILON: f64 = 1e-9;

/// One closed numeric interval `[lower, upper]`.
///
/// Distinct from [`crate::interval_arith::Interval`], which is exact over
/// `Rational64`: branch-cover certificates carry the `f64` endpoints emitted by
/// external NN analyses, so this type is deliberately float-valued and
/// epsilon-tolerant.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct NumericInterval {
    /// Lower bound.
    pub lower: f64,
    /// Upper bound.
    pub upper: f64,
}

impl NumericInterval {
    /// Construct a closed interval.
    #[must_use]
    pub fn new(lower: f64, upper: f64) -> Self {
        Self { lower, upper }
    }

    /// Reject non-finite or inverted bounds.
    ///
    /// SOUNDNESS: NaN fails `is_finite`, so it rejects here rather than
    /// silently poisoning the `<=` comparisons downstream (every NaN
    /// comparison is `false`, which would make containment tests unreliable).
    fn validate(self) -> Result<(), BranchCoverError> {
        if !self.lower.is_finite() {
            return Err(BranchCoverError::NonFiniteBound {
                bound: "lower",
                value: self.lower,
            });
        }
        if !self.upper.is_finite() {
            return Err(BranchCoverError::NonFiniteBound {
                bound: "upper",
                value: self.upper,
            });
        }
        if self.lower > self.upper + EPSILON {
            return Err(BranchCoverError::InvalidInterval {
                lower: self.lower,
                upper: self.upper,
            });
        }
        Ok(())
    }

    fn contains(self, x: f64) -> bool {
        x >= self.lower - EPSILON && x <= self.upper + EPSILON
    }

    fn is_subset_of(self, other: Self) -> bool {
        self.lower >= other.lower - EPSILON && self.upper <= other.upper + EPSILON
    }
}

/// A single branch's claimed input subdomain.
#[derive(Debug, Clone, PartialEq)]
pub struct BranchDomain {
    /// Stable branch identifier used in diagnostics.
    pub id: String,
    /// Axis-aligned branch box, one interval per input dimension.
    pub intervals: Vec<NumericInterval>,
}

impl BranchDomain {
    /// Construct a branch domain.
    #[must_use]
    pub fn new(id: impl Into<String>, intervals: Vec<NumericInterval>) -> Self {
        Self {
            id: id.into(),
            intervals,
        }
    }

    /// Membership test for one point.
    ///
    /// SOUNDNESS: the explicit arity guard is not redundant with
    /// [`validate_certificate`]. `zip` stops at the shorter side, so a branch
    /// with more intervals than the point has coordinates would report
    /// containment from a prefix match alone. Length disagreement is never
    /// containment.
    fn contains_point(&self, point: &[f64]) -> bool {
        self.intervals.len() == point.len()
            && self
                .intervals
                .iter()
                .zip(point)
                .all(|(interval, coord)| interval.contains(*coord))
    }
}

/// Branch cover certificate for an input domain.
#[derive(Debug, Clone, PartialEq)]
pub struct BranchCoverCertificate {
    /// Declared input box.
    pub input_domain: Vec<NumericInterval>,
    /// Branch boxes whose union must equal `input_domain`.
    pub branches: Vec<BranchDomain>,
}

impl BranchCoverCertificate {
    /// Construct a branch-cover certificate.
    #[must_use]
    pub fn new(input_domain: Vec<NumericInterval>, branches: Vec<BranchDomain>) -> Self {
        Self {
            input_domain,
            branches,
        }
    }
}

/// Successful verification metadata.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BranchCoverReport {
    /// Number of branches checked.
    pub branch_count: usize,
    /// Number of representative grid points checked.
    pub representative_points_checked: usize,
}

/// Branch-cover verification failures.
#[derive(Debug, Clone, PartialEq, Error)]
#[non_exhaustive]
pub enum BranchCoverError {
    /// The declared input domain has no dimensions.
    #[error("input domain must have at least one dimension")]
    EmptyInputDomain,
    /// A non-empty input domain cannot be covered by zero branches.
    #[error("branch cover must contain at least one branch")]
    EmptyBranches,
    /// A branch has a different dimension than the declared input domain.
    #[error("branch {branch_id} has dimension {got}, expected {expected}")]
    DimensionMismatch {
        /// Branch id.
        branch_id: String,
        /// Expected dimension.
        expected: usize,
        /// Actual dimension.
        got: usize,
    },
    /// An interval has lower bound greater than upper bound.
    #[error("invalid interval [{lower}, {upper}]")]
    InvalidInterval {
        /// Lower bound.
        lower: f64,
        /// Upper bound.
        upper: f64,
    },
    /// Bounds must be finite.
    #[error("non-finite {bound} bound {value}")]
    NonFiniteBound {
        /// Bound name.
        bound: &'static str,
        /// Non-finite value.
        value: f64,
    },
    /// A branch claims input outside the declared input domain.
    #[error(
        "branch {branch_id} escapes input domain at dimension {dimension}: branch [{branch_lower}, {branch_upper}], input [{input_lower}, {input_upper}]"
    )]
    BranchOutsideInputDomain {
        /// Branch id.
        branch_id: String,
        /// Dimension index.
        dimension: usize,
        /// Branch lower bound.
        branch_lower: f64,
        /// Branch upper bound.
        branch_upper: f64,
        /// Input lower bound.
        input_lower: f64,
        /// Input upper bound.
        input_upper: f64,
    },
    /// A representative point in the declared domain is not covered.
    #[error("branch cover leaves input witness {witness:?} uncovered")]
    UncoveredWitness {
        /// Representative uncovered point.
        witness: Vec<f64>,
    },
}

/// Verify that branch domains cover exactly the declared input domain.
///
/// Accepts only when the certificate is well formed (non-empty, uniform
/// dimension, finite non-inverted boxes), every branch box is contained in the
/// declared input domain, and every cell of the breakpoint grid induced by the
/// domain and branch bounds has a covering branch.
pub fn verify_branch_cover(
    cert: &BranchCoverCertificate,
) -> Result<BranchCoverReport, BranchCoverError> {
    validate_certificate(cert)?;

    let representatives = representative_grid(&cert.input_domain, &cert.branches);
    let checked = representatives.len();
    for point in representatives {
        if !cert
            .branches
            .iter()
            .any(|branch| branch.contains_point(&point))
        {
            return Err(BranchCoverError::UncoveredWitness { witness: point });
        }
    }

    Ok(BranchCoverReport {
        branch_count: cert.branches.len(),
        representative_points_checked: checked,
    })
}

/// Structural validation: shape, finiteness, and containment in the domain.
///
/// SOUNDNESS: this runs before [`representative_grid`], which indexes branch
/// intervals by dimension. The dimension check is what makes that indexing
/// total.
fn validate_certificate(cert: &BranchCoverCertificate) -> Result<(), BranchCoverError> {
    if cert.input_domain.is_empty() {
        return Err(BranchCoverError::EmptyInputDomain);
    }
    if cert.branches.is_empty() {
        return Err(BranchCoverError::EmptyBranches);
    }

    for interval in &cert.input_domain {
        interval.validate()?;
    }

    let expected_dim = cert.input_domain.len();
    for branch in &cert.branches {
        if branch.intervals.len() != expected_dim {
            return Err(BranchCoverError::DimensionMismatch {
                branch_id: branch.id.clone(),
                expected: expected_dim,
                got: branch.intervals.len(),
            });
        }
        for (dimension, (branch_interval, input_interval)) in
            branch.intervals.iter().zip(&cert.input_domain).enumerate()
        {
            branch_interval.validate()?;
            if !branch_interval.is_subset_of(*input_interval) {
                return Err(BranchCoverError::BranchOutsideInputDomain {
                    branch_id: branch.id.clone(),
                    dimension,
                    branch_lower: branch_interval.lower,
                    branch_upper: branch_interval.upper,
                    input_lower: input_interval.lower,
                    input_upper: input_interval.upper,
                });
            }
        }
    }

    Ok(())
}

/// Cartesian product of the per-dimension representative points.
fn representative_grid(domain: &[NumericInterval], branches: &[BranchDomain]) -> Vec<Vec<f64>> {
    let per_dim: Vec<Vec<f64>> = (0..domain.len())
        .map(|dimension| representative_points_for_dimension(domain, branches, dimension))
        .collect();

    let mut out = Vec::new();
    let mut current = Vec::with_capacity(domain.len());
    build_cartesian_points(&per_dim, 0, &mut current, &mut out);
    out
}

/// One representative per cell of the breakpoint partition along `dimension`.
///
/// Every branch bound is a breakpoint, so any hole between two branches is a
/// whole cell and its midpoint witnesses the hole.
fn representative_points_for_dimension(
    domain: &[NumericInterval],
    branches: &[BranchDomain],
    dimension: usize,
) -> Vec<f64> {
    let mut bounds = vec![domain[dimension].lower, domain[dimension].upper];
    for branch in branches {
        bounds.push(branch.intervals[dimension].lower);
        bounds.push(branch.intervals[dimension].upper);
    }

    bounds.sort_by(f64::total_cmp);
    bounds.dedup_by(|a, b| (*a - *b).abs() <= EPSILON);

    if bounds.len() == 1 {
        return bounds;
    }

    let mut representatives = Vec::new();
    for pair in bounds.windows(2) {
        let lower = pair[0];
        let upper = pair[1];
        if upper - lower <= EPSILON {
            representatives.push(lower);
        } else {
            representatives.push((lower + upper) / 2.0);
        }
    }
    representatives
}

fn build_cartesian_points(
    per_dim: &[Vec<f64>],
    dimension: usize,
    current: &mut Vec<f64>,
    out: &mut Vec<Vec<f64>>,
) {
    if dimension == per_dim.len() {
        out.push(current.clone());
        return;
    }

    for value in &per_dim[dimension] {
        current.push(*value);
        build_cartesian_points(per_dim, dimension + 1, current, out);
        current.pop();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn interval(lower: f64, upper: f64) -> NumericInterval {
        NumericInterval::new(lower, upper)
    }

    #[test]
    fn accepts_complete_one_dimensional_cover() {
        let cert = BranchCoverCertificate::new(
            vec![interval(0.0, 1.0)],
            vec![
                BranchDomain::new("left", vec![interval(0.0, 0.5)]),
                BranchDomain::new("right", vec![interval(0.5, 1.0)]),
            ],
        );

        let report = verify_branch_cover(&cert).expect("complete cover should verify");
        assert_eq!(report.branch_count, 2);
        assert_eq!(report.representative_points_checked, 2);
    }

    #[test]
    fn rejects_missing_branch_interval() {
        let cert = BranchCoverCertificate::new(
            vec![interval(0.0, 1.0)],
            vec![
                BranchDomain::new("left", vec![interval(0.0, 0.4)]),
                BranchDomain::new("right", vec![interval(0.6, 1.0)]),
            ],
        );

        let err = verify_branch_cover(&cert).expect_err("gap must be rejected");
        assert!(matches!(err, BranchCoverError::UncoveredWitness { .. }));
    }

    #[test]
    fn rejects_branch_outside_declared_domain() {
        let cert = BranchCoverCertificate::new(
            vec![interval(0.0, 1.0)],
            vec![BranchDomain::new("bad", vec![interval(-0.1, 1.0)])],
        );

        let err = verify_branch_cover(&cert).expect_err("escape must be rejected");
        assert!(matches!(
            err,
            BranchCoverError::BranchOutsideInputDomain {
                branch_id,
                dimension: 0,
                ..
            } if branch_id == "bad"
        ));
    }

    #[test]
    fn accepts_complete_two_dimensional_cover() {
        let cert = BranchCoverCertificate::new(
            vec![interval(0.0, 1.0), interval(0.0, 1.0)],
            vec![
                BranchDomain::new("bottom", vec![interval(0.0, 1.0), interval(0.0, 0.5)]),
                BranchDomain::new("top", vec![interval(0.0, 1.0), interval(0.5, 1.0)]),
            ],
        );

        verify_branch_cover(&cert).expect("2D split cover should verify");
    }

    #[test]
    fn rejects_two_dimensional_cover_with_a_hole() {
        let cert = BranchCoverCertificate::new(
            vec![interval(0.0, 1.0), interval(0.0, 1.0)],
            vec![
                BranchDomain::new("bottom_left", vec![interval(0.0, 0.5), interval(0.0, 0.5)]),
                BranchDomain::new("bottom_right", vec![interval(0.5, 1.0), interval(0.0, 0.5)]),
                BranchDomain::new("top_left", vec![interval(0.0, 0.5), interval(0.5, 1.0)]),
                // top_right quadrant is missing.
            ],
        );

        let err = verify_branch_cover(&cert).expect_err("a missing quadrant must be rejected");
        let BranchCoverError::UncoveredWitness { witness } = err else {
            panic!("expected an uncovered-witness rejection, got {err:?}");
        };
        assert_eq!(witness.len(), 2);
        assert!(
            witness[0] > 0.5,
            "witness must land in the missing quadrant"
        );
        assert!(
            witness[1] > 0.5,
            "witness must land in the missing quadrant"
        );
    }

    #[test]
    fn rejects_empty_input_domain() {
        let cert = BranchCoverCertificate::new(
            vec![],
            vec![BranchDomain::new("only", vec![interval(0.0, 1.0)])],
        );

        assert_eq!(
            verify_branch_cover(&cert).expect_err("a zero-dimensional domain is malformed"),
            BranchCoverError::EmptyInputDomain
        );
    }

    #[test]
    fn rejects_empty_branch_set() {
        let cert = BranchCoverCertificate::new(vec![interval(0.0, 1.0)], vec![]);

        assert_eq!(
            verify_branch_cover(&cert).expect_err("zero branches cannot cover a non-empty box"),
            BranchCoverError::EmptyBranches
        );
    }

    #[test]
    fn rejects_branch_of_wrong_dimension() {
        let cert = BranchCoverCertificate::new(
            vec![interval(0.0, 1.0), interval(0.0, 1.0)],
            vec![BranchDomain::new("flat", vec![interval(0.0, 1.0)])],
        );

        let err = verify_branch_cover(&cert).expect_err("dimension disagreement must be rejected");
        assert!(matches!(
            err,
            BranchCoverError::DimensionMismatch {
                branch_id,
                expected: 2,
                got: 1
            } if branch_id == "flat"
        ));
    }

    #[test]
    fn rejects_inverted_interval() {
        let cert = BranchCoverCertificate::new(
            vec![interval(1.0, 0.0)],
            vec![BranchDomain::new("only", vec![interval(0.0, 1.0)])],
        );

        let err = verify_branch_cover(&cert).expect_err("lower > upper must be rejected");
        assert!(matches!(err, BranchCoverError::InvalidInterval { .. }));
    }

    #[test]
    fn rejects_non_finite_bound() {
        let cert = BranchCoverCertificate::new(
            vec![interval(0.0, f64::INFINITY)],
            vec![BranchDomain::new("only", vec![interval(0.0, 1.0)])],
        );

        let err = verify_branch_cover(&cert).expect_err("an infinite bound must be rejected");
        assert!(matches!(
            err,
            BranchCoverError::NonFiniteBound { bound: "upper", .. }
        ));
    }

    #[test]
    fn rejects_nan_bound() {
        let cert = BranchCoverCertificate::new(
            vec![interval(f64::NAN, 1.0)],
            vec![BranchDomain::new("only", vec![interval(0.0, 1.0)])],
        );

        let err = verify_branch_cover(&cert).expect_err("NaN must reject, not silently compare");
        assert!(matches!(
            err,
            BranchCoverError::NonFiniteBound { bound: "lower", .. }
        ));
    }

    #[test]
    fn accepts_degenerate_point_domain() {
        let cert = BranchCoverCertificate::new(
            vec![interval(0.5, 0.5)],
            vec![BranchDomain::new("point", vec![interval(0.5, 0.5)])],
        );

        let report = verify_branch_cover(&cert).expect("a point domain covered by a point branch");
        assert_eq!(report.branch_count, 1);
        assert_eq!(report.representative_points_checked, 1);
    }

    #[test]
    fn rejects_gap_wider_than_epsilon() {
        // A hole two orders of magnitude above the tolerance must still be a
        // hole: the epsilon slack closes rounding noise, not real gaps.
        let cert = BranchCoverCertificate::new(
            vec![interval(0.0, 1.0)],
            vec![
                BranchDomain::new("left", vec![interval(0.0, 0.5)]),
                BranchDomain::new("right", vec![interval(0.5 + 1e-7, 1.0)]),
            ],
        );

        let err = verify_branch_cover(&cert).expect_err("a supra-epsilon gap must be rejected");
        assert!(matches!(err, BranchCoverError::UncoveredWitness { .. }));
    }

    #[test]
    fn rejects_partial_cover_of_one_dimension_in_two_d() {
        // Covers x fully but only the lower half of y.
        let cert = BranchCoverCertificate::new(
            vec![interval(0.0, 1.0), interval(0.0, 1.0)],
            vec![BranchDomain::new(
                "bottom",
                vec![interval(0.0, 1.0), interval(0.0, 0.5)],
            )],
        );

        let err = verify_branch_cover(&cert).expect_err("an uncovered half must be rejected");
        assert!(matches!(err, BranchCoverError::UncoveredWitness { .. }));
    }
}
