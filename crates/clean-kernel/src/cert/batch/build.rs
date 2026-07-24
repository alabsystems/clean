// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use std::{sync::Arc, time::Instant};

use rayon::prelude::*;

use crate::cert::builder::{CertBuilder, NodeId, WhnfCache};
use crate::env::Environment;
use crate::expr::{Expr, ExprKind};
use crate::level::Level;

use super::build_types::{compute_build_stats, BatchBuildInput, BatchBuildResult, BatchBuildStats};
use super::common::{micros_to_u64, with_stats, with_thread_pool};

fn fallback_type() -> Expr {
    Expr::from_kind(ExprKind::Sort(Level::zero()))
}

fn computed_type(builder: &CertBuilder<'_>, root_id: NodeId) -> Expr {
    builder
        .try_type_of(root_id)
        .cloned()
        .unwrap_or_else(fallback_type)
}

fn build_verify_one(
    env: &Environment,
    input: BatchBuildInput,
    whnf_cache: &Arc<WhnfCache>,
) -> BatchBuildResult {
    let start = Instant::now();
    let mut builder = CertBuilder::new(env).with_whnf_cache(Arc::clone(whnf_cache));
    match (input.builder_fn)(&mut builder) {
        Ok(root_id) => {
            let ty = computed_type(&builder, root_id);
            match builder.finish(root_id) {
                Ok(cert) => BatchBuildResult::success(
                    input.id,
                    cert,
                    ty,
                    micros_to_u64(start.elapsed().as_micros()),
                ),
                Err(error) => BatchBuildResult::failure(
                    input.id,
                    error,
                    micros_to_u64(start.elapsed().as_micros()),
                ),
            }
        }
        Err(error) => {
            BatchBuildResult::failure(input.id, error, micros_to_u64(start.elapsed().as_micros()))
        }
    }
}

fn build_parallel(
    env: &Environment,
    inputs: Vec<BatchBuildInput>,
    whnf_cache: Arc<WhnfCache>,
) -> Vec<BatchBuildResult> {
    inputs
        .into_par_iter()
        .map(|input| build_verify_one(env, input, &whnf_cache))
        .collect()
}

fn build_parallel_with_callback<F>(
    env: &Environment,
    inputs: Vec<BatchBuildInput>,
    whnf_cache: Arc<WhnfCache>,
    callback: Arc<F>,
) -> Vec<BatchBuildResult>
where
    F: Fn(&BatchBuildResult) + Send + Sync,
{
    inputs
        .into_par_iter()
        .map(|input| {
            let result = build_verify_one(env, input, &whnf_cache);
            callback(&result);
            result
        })
        .collect()
}

fn build_sequential(
    env: &Environment,
    inputs: Vec<BatchBuildInput>,
    whnf_cache: Arc<WhnfCache>,
) -> Vec<BatchBuildResult> {
    inputs
        .into_iter()
        .map(|input| build_verify_one(env, input, &whnf_cache))
        .collect()
}

pub fn batch_build_verify(
    env: &Environment,
    inputs: Vec<BatchBuildInput>,
) -> Vec<BatchBuildResult> {
    build_parallel(env, inputs, Arc::new(WhnfCache::new()))
}

pub fn batch_build_verify_with_stats(
    env: &Environment,
    inputs: Vec<BatchBuildInput>,
) -> (Vec<BatchBuildResult>, BatchBuildStats) {
    with_stats(|| batch_build_verify(env, inputs), compute_build_stats)
}

pub fn batch_build_verify_sequential(
    env: &Environment,
    inputs: Vec<BatchBuildInput>,
) -> Vec<BatchBuildResult> {
    build_sequential(env, inputs, Arc::new(WhnfCache::new()))
}

pub fn batch_build_verify_sequential_with_stats(
    env: &Environment,
    inputs: Vec<BatchBuildInput>,
) -> (Vec<BatchBuildResult>, BatchBuildStats) {
    with_stats(
        || batch_build_verify_sequential(env, inputs),
        compute_build_stats,
    )
}

pub fn batch_build_verify_with_threads(
    env: &Environment,
    inputs: Vec<BatchBuildInput>,
    num_threads: usize,
) -> Vec<BatchBuildResult> {
    let whnf_cache = Arc::new(WhnfCache::new());
    with_thread_pool(num_threads, || build_parallel(env, inputs, whnf_cache))
}

pub fn batch_build_verify_with_stats_threads(
    env: &Environment,
    inputs: Vec<BatchBuildInput>,
    num_threads: usize,
) -> (Vec<BatchBuildResult>, BatchBuildStats) {
    with_stats(
        || batch_build_verify_with_threads(env, inputs, num_threads),
        compute_build_stats,
    )
}

pub fn batch_build_verify_with_stats_progress<F>(
    env: &Environment,
    inputs: Vec<BatchBuildInput>,
    threads: usize,
    on_result: F,
) -> (Vec<BatchBuildResult>, BatchBuildStats)
where
    F: Fn(&BatchBuildResult) + Send + Sync,
{
    let callback = Arc::new(on_result);
    let whnf_cache = Arc::new(WhnfCache::new());
    with_stats(
        || {
            if threads > 0 {
                let callback = Arc::clone(&callback);
                let whnf_cache = Arc::clone(&whnf_cache);
                with_thread_pool(threads, || {
                    build_parallel_with_callback(env, inputs, whnf_cache, callback)
                })
            } else {
                build_parallel_with_callback(env, inputs, whnf_cache, callback)
            }
        },
        compute_build_stats,
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::{Declaration, Environment};
    use crate::expr::{BinderInfo, ExprKind};
    use crate::name::Name;

    fn cached_app_fixture() -> (Environment, Name) {
        let mut env = Environment::new();
        let fun_ty_name = Name::from_string("batch.cachedFunTy");
        let fun_name = Name::from_string("batch.cachedFun");
        let fun_ty_value = Expr::pi(
            BinderInfo::Default,
            Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero()))),
            Expr::from_kind(ExprKind::Sort(Level::zero())),
        );

        env.add_decl(Declaration::Definition {
            name: fun_ty_name.clone(),
            level_params: vec![],
            type_: Expr::from_kind(ExprKind::Sort(Level::succ(Level::succ(Level::zero())))),
            value: fun_ty_value,
            is_reducible: true,
        })
        .expect("fixture definition should register");
        env.add_decl(Declaration::Axiom {
            name: fun_name.clone(),
            level_params: vec![],
            type_: Expr::const_(fun_ty_name, vec![]),
        })
        .expect("fixture axiom should register");

        (env, fun_name)
    }

    #[test]
    fn test_batch_build_sequential_reuses_shared_whnf_cache() {
        let (env, fun_name) = cached_app_fixture();
        let cache = Arc::new(WhnfCache::new());
        let inputs = vec![
            BatchBuildInput::new("first", {
                let fun_name = fun_name.clone();
                move |builder| {
                    let fun = builder.const_(fun_name.clone(), vec![])?;
                    let arg = builder.sort(Level::zero())?;
                    builder.app(fun, arg)
                }
            }),
            BatchBuildInput::new("second", move |builder| {
                let fun = builder.const_(fun_name.clone(), vec![])?;
                let arg = builder.sort(Level::zero())?;
                builder.app(fun, arg)
            }),
        ];

        let results = build_sequential(&env, inputs, Arc::clone(&cache));

        assert_eq!(results.len(), 2);
        assert!(results.iter().all(|result| result.success));
        assert_eq!(cache.len(), 1, "shared batch cache should store one WHNF");
        assert_eq!(cache.misses(), 1, "first builder should miss once");
        assert_eq!(cache.hits(), 1, "second builder should reuse cached WHNF");
    }
}
