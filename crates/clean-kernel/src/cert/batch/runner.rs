// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use crate::env::Environment;

use super::build::{
    batch_build_verify, batch_build_verify_sequential, batch_build_verify_sequential_with_stats,
    batch_build_verify_with_stats, batch_build_verify_with_stats_progress,
    batch_build_verify_with_stats_threads, batch_build_verify_with_threads,
};
use super::build_types::{BatchBuildInput, BatchBuildResult, BatchBuildStats};
use super::verify::{
    batch_verify, batch_verify_sequential, batch_verify_sequential_with_stats,
    batch_verify_with_stats, batch_verify_with_stats_progress, batch_verify_with_stats_threads,
    batch_verify_with_threads, BatchVerifyInput, BatchVerifyResult, BatchVerifyStats,
};

/// Builder for configuring batch verification operations.
pub struct BatchVerifier<'a, F = fn(&BatchVerifyResult)>
where
    F: Fn(&BatchVerifyResult) + Send + Sync,
{
    env: &'a Environment,
    inputs: Vec<BatchVerifyInput>,
    sequential: bool,
    num_threads: Option<usize>,
    progress_callback: Option<F>,
}

impl<'a> BatchVerifier<'a, fn(&BatchVerifyResult)> {
    pub fn new(env: &'a Environment, inputs: Vec<BatchVerifyInput>) -> Self {
        Self {
            env,
            inputs,
            sequential: false,
            num_threads: None,
            progress_callback: None,
        }
    }
}

impl<'a, F> BatchVerifier<'a, F>
where
    F: Fn(&BatchVerifyResult) + Send + Sync,
{
    pub fn sequential(mut self) -> Self {
        self.sequential = true;
        self
    }

    pub fn with_threads(mut self, num_threads: usize) -> Self {
        self.num_threads = Some(num_threads);
        self
    }

    pub fn with_progress<G>(self, callback: G) -> BatchVerifier<'a, G>
    where
        G: Fn(&BatchVerifyResult) + Send + Sync,
    {
        BatchVerifier {
            env: self.env,
            inputs: self.inputs,
            sequential: self.sequential,
            num_threads: self.num_threads,
            progress_callback: Some(callback),
        }
    }

    pub fn with_stats(self) -> Self {
        self
    }

    pub fn run(self) -> Vec<BatchVerifyResult> {
        if let Some(callback) = self.progress_callback {
            let threads = self.num_threads.unwrap_or(0);
            let (results, _) =
                batch_verify_with_stats_progress(self.env, self.inputs, threads, callback);
            results
        } else if self.sequential {
            batch_verify_sequential(self.env, self.inputs)
        } else if let Some(threads) = self.num_threads {
            batch_verify_with_threads(self.env, self.inputs, threads)
        } else {
            batch_verify(self.env, self.inputs)
        }
    }

    pub fn run_with_stats(self) -> (Vec<BatchVerifyResult>, BatchVerifyStats) {
        if let Some(callback) = self.progress_callback {
            let threads = self.num_threads.unwrap_or(0);
            batch_verify_with_stats_progress(self.env, self.inputs, threads, callback)
        } else if self.sequential {
            batch_verify_sequential_with_stats(self.env, self.inputs)
        } else if let Some(threads) = self.num_threads {
            batch_verify_with_stats_threads(self.env, self.inputs, threads)
        } else {
            batch_verify_with_stats(self.env, self.inputs)
        }
    }
}

/// Builder for configuring batch build-and-verify operations.
pub struct BatchBuildVerifier<'a, F = fn(&BatchBuildResult)>
where
    F: Fn(&BatchBuildResult) + Send + Sync,
{
    env: &'a Environment,
    inputs: Vec<BatchBuildInput>,
    sequential: bool,
    num_threads: Option<usize>,
    progress_callback: Option<F>,
}

impl<'a> BatchBuildVerifier<'a, fn(&BatchBuildResult)> {
    pub fn new(env: &'a Environment, inputs: Vec<BatchBuildInput>) -> Self {
        Self {
            env,
            inputs,
            sequential: false,
            num_threads: None,
            progress_callback: None,
        }
    }
}

impl<'a, F> BatchBuildVerifier<'a, F>
where
    F: Fn(&BatchBuildResult) + Send + Sync,
{
    pub fn sequential(mut self) -> Self {
        self.sequential = true;
        self
    }

    pub fn with_threads(mut self, num_threads: usize) -> Self {
        self.num_threads = Some(num_threads);
        self
    }

    pub fn with_progress<G>(self, callback: G) -> BatchBuildVerifier<'a, G>
    where
        G: Fn(&BatchBuildResult) + Send + Sync,
    {
        BatchBuildVerifier {
            env: self.env,
            inputs: self.inputs,
            sequential: self.sequential,
            num_threads: self.num_threads,
            progress_callback: Some(callback),
        }
    }

    pub fn with_stats(self) -> Self {
        self
    }

    pub fn run(self) -> Vec<BatchBuildResult> {
        if let Some(callback) = self.progress_callback {
            let threads = self.num_threads.unwrap_or(0);
            let (results, _) =
                batch_build_verify_with_stats_progress(self.env, self.inputs, threads, callback);
            results
        } else if self.sequential {
            batch_build_verify_sequential(self.env, self.inputs)
        } else if let Some(threads) = self.num_threads {
            batch_build_verify_with_threads(self.env, self.inputs, threads)
        } else {
            batch_build_verify(self.env, self.inputs)
        }
    }

    pub fn run_with_stats(self) -> (Vec<BatchBuildResult>, BatchBuildStats) {
        if let Some(callback) = self.progress_callback {
            let threads = self.num_threads.unwrap_or(0);
            batch_build_verify_with_stats_progress(self.env, self.inputs, threads, callback)
        } else if self.sequential {
            batch_build_verify_sequential_with_stats(self.env, self.inputs)
        } else if let Some(threads) = self.num_threads {
            batch_build_verify_with_stats_threads(self.env, self.inputs, threads)
        } else {
            batch_build_verify_with_stats(self.env, self.inputs)
        }
    }
}
