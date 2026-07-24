// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use std::fmt;

use crate::cert::builder::{CertBuilder, NodeId};
use crate::cert::types::{CertError, ProofCert};
use crate::expr::Expr;

/// Result of building a single certificate in a batch.
#[derive(Debug, Clone)]
pub struct BatchBuildResult {
    pub id: String,
    pub success: bool,
    pub cert: Option<ProofCert>,
    pub computed_type: Option<Expr>,
    pub error: Option<CertError>,
    pub time_us: u64,
}

impl BatchBuildResult {
    pub(crate) fn success(id: String, cert: ProofCert, ty: Expr, time_us: u64) -> Self {
        Self {
            id,
            success: true,
            cert: Some(cert),
            computed_type: Some(ty),
            error: None,
            time_us,
        }
    }

    pub(crate) fn failure(id: String, error: CertError, time_us: u64) -> Self {
        Self {
            id,
            success: false,
            cert: None,
            computed_type: None,
            error: Some(error),
            time_us,
        }
    }
}

/// Statistics for batch building.
#[derive(Debug, Clone, Default)]
pub struct BatchBuildStats {
    pub total: usize,
    pub successful: usize,
    pub failed: usize,
    pub wall_time_us: u64,
    pub sum_build_time_us: u64,
    pub min_time_us: u64,
    pub max_time_us: u64,
    pub avg_success_time_us: u64,
    pub avg_fail_time_us: u64,
    pub speedup: f64,
}

impl fmt::Display for BatchBuildStats {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "BatchBuildStats {{ total: {}, success: {}, failed: {}, wall_time: {}µs, min: {}µs, max: {}µs, avg_success: {}µs, avg_fail: {}µs, speedup: {:.2}x }}",
            self.total,
            self.successful,
            self.failed,
            self.wall_time_us,
            self.min_time_us,
            self.max_time_us,
            self.avg_success_time_us,
            self.avg_fail_time_us,
            self.speedup
        )
    }
}

pub(crate) fn compute_build_stats(
    results: &[BatchBuildResult],
    wall_time_us: u64,
) -> BatchBuildStats {
    let total = results.len();
    let mut successful = 0usize;
    let mut failed = 0usize;
    let mut sum_build_time_us = 0u64;
    let mut min_time_us = u64::MAX;
    let mut max_time_us = 0u64;
    let mut sum_success_time = 0u64;
    let mut sum_fail_time = 0u64;

    for result in results {
        sum_build_time_us += result.time_us;
        min_time_us = min_time_us.min(result.time_us);
        max_time_us = max_time_us.max(result.time_us);
        if result.success {
            successful += 1;
            sum_success_time += result.time_us;
        } else {
            failed += 1;
            sum_fail_time += result.time_us;
        }
    }

    if total == 0 {
        min_time_us = 0;
    }

    let avg_success_time_us = if successful > 0 {
        sum_success_time / successful as u64
    } else {
        0
    };
    let avg_fail_time_us = if failed > 0 {
        sum_fail_time / failed as u64
    } else {
        0
    };
    let speedup = if wall_time_us > 0 {
        sum_build_time_us as f64 / wall_time_us as f64
    } else {
        1.0
    };

    BatchBuildStats {
        total,
        successful,
        failed,
        wall_time_us,
        sum_build_time_us,
        min_time_us,
        max_time_us,
        avg_success_time_us,
        avg_fail_time_us,
        speedup,
    }
}

/// Builder function type for incremental certificate construction.
pub type BuilderFn = Box<dyn FnOnce(&mut CertBuilder<'_>) -> Result<NodeId, CertError> + Send>;

/// Input for batch building: an ID paired with a builder function.
pub struct BatchBuildInput {
    pub id: String,
    pub builder_fn: BuilderFn,
}

impl BatchBuildInput {
    pub fn new<F>(id: impl Into<String>, builder_fn: F) -> Self
    where
        F: FnOnce(&mut CertBuilder<'_>) -> Result<NodeId, CertError> + Send + 'static,
    {
        Self {
            id: id.into(),
            builder_fn: Box::new(builder_fn),
        }
    }
}
