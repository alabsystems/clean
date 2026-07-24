// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Scoped resource accounting for recursive kernel serde decoding.
//!
//! Serde's data model does not expose a general recursion limit.  Carrier
//! decoders can install this thread-local scope so the custom `Expr`, `Level`,
//! and `Name` deserializers reject excessive recursion *while decoding*, before
//! a huge successfully-built recursive value has to be dropped on the native
//! thread stack.  No scope means existing trusted deserialization behavior is
//! unchanged.

use serde::de::Error as _;
use std::cell::RefCell;

/// Limits installed around one untrusted kernel-value decode.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct DecodeResourceLimits {
    /// Aggregate number of recursive `Expr`, `Level`, and `Name` nodes.
    pub max_nodes: usize,
    /// Maximum active recursive depth across those node types.
    pub max_depth: usize,
}

#[derive(Clone, Copy, Debug)]
struct DecodeBudget {
    limits: DecodeResourceLimits,
    nodes: usize,
    depth: usize,
}

thread_local! {
    static DECODE_BUDGETS: RefCell<Vec<DecodeBudget>> = const { RefCell::new(Vec::new()) };
}

/// Run `decode` with fail-closed recursive node/depth accounting.
///
/// Scopes are thread-local and nest safely.  Each nested scope owns an
/// independent budget, and RAII removes it on normal return or unwinding.
pub fn with_decode_resource_limits<R>(
    limits: DecodeResourceLimits,
    decode: impl FnOnce() -> R,
) -> R {
    DECODE_BUDGETS.with(|budgets| {
        budgets.borrow_mut().push(DecodeBudget {
            limits,
            nodes: 0,
            depth: 0,
        });
    });
    let _scope = DecodeScope;
    decode()
}

struct DecodeScope;

impl Drop for DecodeScope {
    fn drop(&mut self) {
        DECODE_BUDGETS.with(|budgets| {
            let popped = budgets.borrow_mut().pop();
            debug_assert!(popped.is_some(), "decode-resource scope stack underflow");
        });
    }
}

pub(crate) struct DecodeNodeGuard {
    active: bool,
}

impl Drop for DecodeNodeGuard {
    fn drop(&mut self) {
        if !self.active {
            return;
        }
        DECODE_BUDGETS.with(|budgets| {
            let mut budgets = budgets.borrow_mut();
            let budget = budgets
                .last_mut()
                .expect("active decode node must have an enclosing scope");
            debug_assert!(budget.depth > 0, "decode-resource depth underflow");
            budget.depth -= 1;
        });
    }
}

pub(crate) fn enter_decode_node<E>(kind: &str) -> Result<DecodeNodeGuard, E>
where
    E: serde::de::Error,
{
    let outcome = DECODE_BUDGETS.with(|budgets| {
        let mut budgets = budgets.borrow_mut();
        let Some(budget) = budgets.last_mut() else {
            return Ok(false);
        };

        let next_nodes = budget.nodes.checked_add(1).ok_or_else(|| {
            format!("{kind} structural node count overflow during deserialization")
        })?;
        if next_nodes > budget.limits.max_nodes {
            return Err(format!(
                "{kind} structural node count {next_nodes} exceeds deserialization limit {}",
                budget.limits.max_nodes
            ));
        }
        let next_depth = budget
            .depth
            .checked_add(1)
            .ok_or_else(|| format!("{kind} structural depth overflow during deserialization"))?;
        if next_depth > budget.limits.max_depth {
            return Err(format!(
                "{kind} structural depth {next_depth} exceeds deserialization limit {}",
                budget.limits.max_depth
            ));
        }

        budget.nodes = next_nodes;
        budget.depth = next_depth;
        Ok(true)
    });

    match outcome {
        Ok(active) => Ok(DecodeNodeGuard { active }),
        Err(message) => Err(E::custom(message)),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Expr, Level, Name};

    #[test]
    fn nested_scopes_restore_outer_budget() {
        with_decode_resource_limits(
            DecodeResourceLimits {
                max_nodes: 2,
                max_depth: 2,
            },
            || {
                let outer = enter_decode_node::<serde::de::value::Error>("outer").unwrap();
                with_decode_resource_limits(
                    DecodeResourceLimits {
                        max_nodes: 1,
                        max_depth: 1,
                    },
                    || {
                        let _inner = enter_decode_node::<serde::de::value::Error>("inner").unwrap();
                    },
                );
                drop(outer);
                let _second = enter_decode_node::<serde::de::value::Error>("outer").unwrap();
            },
        );
    }

    #[test]
    fn deep_name_and_level_are_rejected_during_decode() {
        let mut name = Name::anon();
        let mut level = Level::zero();
        for _ in 0..64 {
            name = name.str("x");
            level = Level::succ(level);
        }
        let name_bytes = bincode::serde::encode_to_vec(&name, bincode::config::standard()).unwrap();
        let level_bytes =
            bincode::serde::encode_to_vec(&level, bincode::config::standard()).unwrap();
        let limits = DecodeResourceLimits {
            max_nodes: 1_000,
            max_depth: 32,
        };

        let name_error = with_decode_resource_limits(limits, || {
            bincode::serde::decode_from_slice::<Name, _>(&name_bytes, bincode::config::standard())
        })
        .expect_err("deep name must fail inside the scoped decoder");
        assert!(name_error.to_string().contains("structural depth"));

        let level_error = with_decode_resource_limits(limits, || {
            bincode::serde::decode_from_slice::<Level, _>(&level_bytes, bincode::config::standard())
        })
        .expect_err("deep level must fail inside the scoped decoder");
        assert!(level_error.to_string().contains("structural depth"));
    }

    #[test]
    fn expression_node_limit_is_enforced_during_decode() {
        let expr = Expr::app(Expr::const_str("f"), Expr::nat_lit(0));
        let bytes = bincode::serde::encode_to_vec(&expr, bincode::config::standard()).unwrap();
        let error = with_decode_resource_limits(
            DecodeResourceLimits {
                max_nodes: 1,
                max_depth: 100,
            },
            || bincode::serde::decode_from_slice::<Expr, _>(&bytes, bincode::config::standard()),
        )
        .expect_err("an App's child must exceed the one-node budget");
        assert!(error.to_string().contains("structural node count"));
    }
}
