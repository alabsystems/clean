// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Parallel batch SMT proof search with rayon.
//!
//! This module provides a parallel dispatcher for running multiple proof
//! queries through the automation engine simultaneously. Each query gets
//! its own solver instance (per the single-shot bridge contract, #2836),
//! and rayon handles work-stealing across available cores.
//!
//! # Architecture
//!
//! ```text
//! ┌─────────────────────────────────────────┐
//! │           BatchDispatcher               │
//! │  ┌──────┐ ┌──────┐ ┌──────┐            │
//! │  │Query0│ │Query1│ │Query2│  ...        │
//! │  └──┬───┘ └──┬───┘ └──┬───┘            │
//! │     │        │        │   rayon par_iter│
//! │  ┌──▼───┐ ┌──▼───┐ ┌──▼───┐            │
//! │  │Engine│ │Engine│ │Engine│              │
//! │  │+Bridge││+Bridge││+Bridge│             │
//! │  └──┬───┘ └──┬───┘ └──┬───┘            │
//! │     │        │        │                 │
//! │  ┌──▼───┐ ┌──▼───┐ ┌──▼───┐            │
//! │  │Result│ │Result│ │Result│              │
//! │  └──────┘ └──────┘ └──────┘             │
//! │              │                          │
//! │         BatchAggregator                 │
//! │         (stats, grouping)               │
//! └─────────────────────────────────────────┘
//! ```
//!
//! # Usage
//!
//! ```text
//! use clean_auto::batch::{BatchDispatcher, BatchConfig, BatchQuery, QueryId, BatchAggregator};
//!
//! let config = BatchConfig::new()
//!     .with_max_parallel(4)
//!     .with_default_timeout_ms(5_000);
//! let dispatcher = BatchDispatcher::new(config);
//!
//! let queries = vec![
//!     BatchQuery::new(QueryId(0), goal_a, 5_000),
//!     BatchQuery::new(QueryId(1), goal_b, 5_000).with_priority(10),
//! ];
//!
//! let dispatch_result = dispatcher.dispatch(&env, &queries);
//! let aggregator = BatchAggregator::new(
//!     dispatch_result.results,
//!     dispatch_result.stats.total_time_ns,
//! );
//! let stats = aggregator.summarize();
//! tracing::info!("proved: {}/{}", stats.proved, stats.total);
//! ```

pub mod aggregator;
pub mod dispatcher;
pub mod types;

pub use aggregator::{BatchAggregator, StatusGroups};
pub use dispatcher::{BatchDispatcher, DispatchResult};
pub use types::{BatchConfig, BatchQuery, BatchQueryStatus, BatchResult, BatchStats, QueryId};

#[cfg(test)]
mod tests;
