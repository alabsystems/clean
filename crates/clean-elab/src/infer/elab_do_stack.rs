// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! ControlStack for do-notation transformer wrapping (#1818 Phase 4B).
//!
//! Based on ControlInfo (Phase 3), wraps the base monad in a transformer stack:
//! - `EarlyReturnT ρ` = `ExceptT ρ` for non-terminal `return`
//! - `StateT σ` for mutable variable reassignment (`let mut`)
//! - `BreakT` = `OptionT` for `break` in loops
//! - `ContinueT` = `OptionT` for `continue` in loops
//!
//! Wrapping order (innermost→outermost): Base → EarlyReturn → State → Break → Continue
//! This matches Lean 4 Control.lean:202-239.
//!
//! Reference: ~/lean4-ref/src/Lean/Elab/Do/Control.lean

use super::elab_do::DoMonadInfo;
use super::elab_do_control::ControlInfo;
#[cfg(test)]
pub(crate) use super::elab_do_prod::{build_sigma_type, build_sigma_value, destructure_sigma};
use super::ElabError;
use clean_kernel::name::Name;
use clean_kernel::Expr;
#[cfg(test)]
use clean_kernel::Level;

/// A single layer in the monad transformer stack.
///
/// Each layer wraps the inner monad (the layer below it) with a transformer.
/// The base layer is the user's monad from DoMonadInfo.
#[derive(Debug, Clone)]
pub(crate) enum ControlStackLayer {
    /// The user's base monad `m : Type u → Type v`.
    Base,
    /// `EarlyReturnT ρ m` = `ExceptT ρ m` for non-terminal `return e`.
    /// `return_type` is ρ (the type of the returned value).
    EarlyReturn { return_type: Expr },
    /// `StateT σ m` for mutable variables.
    /// `sigma` is the product type of all reassigned mutable variable types.
    State { sigma: Expr },
    /// `BreakT m` = `OptionT m` for `break` in for/while/repeat.
    Break,
    /// `ContinueT m` = `OptionT m` for `continue` in for/while/repeat.
    Continue,
}

/// The complete control stack with layer ordering and saved base indices.
///
/// Layers are stored innermost-first: layers[0] is always Base, layers[last]
/// is the outermost. The *_layer_idx fields store the index of the transformer
/// layer (NOT the base below it — subtract 1 to get the layer that receives
/// control flow expressions).
///
/// This supports the `*Base?` pattern from Lean 4 Control.lean:189-239:
/// break/continue/return generate expressions at the layer BELOW their
/// transformer, then `run_in_base` chains through outer layers.
pub(crate) struct ControlStack {
    /// Ordered layers: [Base, EarlyReturn?, State?, Break?, Continue?]
    pub(crate) layers: Vec<ControlStackLayer>,
    /// Index of the EarlyReturn layer in `layers` (if present).
    pub(crate) return_layer_idx: Option<usize>,
    /// Index of the State layer in `layers` (if present).
    pub(crate) state_layer_idx: Option<usize>,
    /// Index of the Break layer in `layers` (if present).
    pub(crate) break_layer_idx: Option<usize>,
    /// Index of the Continue layer in `layers` (if present).
    pub(crate) continue_layer_idx: Option<usize>,
}

impl ControlStack {
    /// Build a control stack from ControlInfo and DoMonadInfo.
    ///
    /// Wrapping order (innermost→outermost): Base → EarlyReturn → State → Break → Continue
    /// This matches Lean 4 Control.lean:202-239 (`ControlLifter.ofCont`).
    ///
    /// `mut_var_types` provides the types for mutable variables named in
    /// `control_info.reassigns`. The caller must resolve these from the
    /// local context before calling.
    pub(crate) fn build(
        control_info: &ControlInfo,
        return_type: Option<Expr>,
        state_sigma: Option<Expr>,
    ) -> Result<Self, ElabError> {
        let mut layers = vec![ControlStackLayer::Base];
        let mut return_layer_idx = None;
        let mut state_layer_idx = None;
        let mut break_layer_idx = None;
        let mut continue_layer_idx = None;

        // Layer 1: EarlyReturn (ExceptT ρ)
        if control_info.returns_early {
            let rho = return_type.ok_or_else(|| {
                ElabError::InternalInvariant(
                    "control stack requires the elaborated early-return type".to_string(),
                )
            })?;
            return_layer_idx = Some(layers.len());
            layers.push(ControlStackLayer::EarlyReturn { return_type: rho });
        }

        // Layer 2: State (StateT σ)
        if !control_info.reassigns.is_empty() {
            let sigma = state_sigma.ok_or_else(|| {
                ElabError::InternalInvariant(
                    "control stack requires the validated mutable-state product type".to_string(),
                )
            })?;
            state_layer_idx = Some(layers.len());
            layers.push(ControlStackLayer::State { sigma });
        }

        // Layer 3: Break (OptionT)
        if control_info.breaks {
            break_layer_idx = Some(layers.len());
            layers.push(ControlStackLayer::Break);
        }

        // Layer 4: Continue (OptionT)
        if control_info.continues {
            continue_layer_idx = Some(layers.len());
            layers.push(ControlStackLayer::Continue);
        }

        Ok(ControlStack {
            layers,
            return_layer_idx,
            state_layer_idx,
            break_layer_idx,
            continue_layer_idx,
        })
    }

    /// Returns true if the stack has any transformer layers beyond Base.
    pub(crate) fn has_transformers(&self) -> bool {
        self.layers.len() > 1
    }

    /// Compute the wrapped monad expression at the top of the stack.
    ///
    /// Starting from the base monad `m`, applies each transformer:
    /// - EarlyReturn(ρ): `ExceptT ρ inner_m`
    /// - State(σ): `StateT σ inner_m`
    /// - Break: `OptionT inner_m`
    /// - Continue: `OptionT inner_m`
    ///
    /// Returns the monad expression `m' : Type u → Type v'` at the outermost layer.
    pub(crate) fn compute_wrapped_monad(&self, monad_info: &DoMonadInfo) -> Expr {
        let mut current = monad_info.m.clone();

        for layer in &self.layers[1..] {
            current = match layer {
                ControlStackLayer::Base => unreachable!("Base cannot appear after index 0"),
                ControlStackLayer::EarlyReturn { return_type } => {
                    // ExceptT ρ m : Type u → Type v
                    let except_t = Expr::const_(
                        Name::from_string("ExceptT"),
                        vec![monad_info.u.clone(), monad_info.v.clone()],
                    );
                    Expr::app(Expr::app(except_t, return_type.clone()), current)
                }
                ControlStackLayer::State { sigma, .. } => {
                    // StateT σ m : Type u → Type v
                    let state_t = Expr::const_(
                        Name::from_string("StateT"),
                        vec![monad_info.u.clone(), monad_info.v.clone()],
                    );
                    Expr::app(Expr::app(state_t, sigma.clone()), current)
                }
                ControlStackLayer::Break | ControlStackLayer::Continue => {
                    // OptionT m : Type u → Type v
                    let option_t = Expr::const_(
                        Name::from_string("OptionT"),
                        vec![monad_info.u.clone(), monad_info.v.clone()],
                    );
                    Expr::app(option_t, current)
                }
            };
        }

        current
    }

    /// Compute the wrapped monad at a specific layer index.
    ///
    /// Used for the `*Base?` pattern: generate control flow expressions at the
    /// layer BELOW the transformer, using that layer's monad.
    pub(crate) fn compute_monad_at(&self, up_to_layer: usize, monad_info: &DoMonadInfo) -> Expr {
        let mut current = monad_info.m.clone();

        for layer in &self.layers[1..=up_to_layer] {
            current = match layer {
                ControlStackLayer::Base => unreachable!(
                    "compute_monad_at should never encounter ControlStackLayer::Base past layer 0"
                ),
                ControlStackLayer::EarlyReturn { return_type } => {
                    let except_t = Expr::const_(
                        Name::from_string("ExceptT"),
                        vec![monad_info.u.clone(), monad_info.v.clone()],
                    );
                    Expr::app(Expr::app(except_t, return_type.clone()), current)
                }
                ControlStackLayer::State { sigma, .. } => {
                    let state_t = Expr::const_(
                        Name::from_string("StateT"),
                        vec![monad_info.u.clone(), monad_info.v.clone()],
                    );
                    Expr::app(Expr::app(state_t, sigma.clone()), current)
                }
                ControlStackLayer::Break | ControlStackLayer::Continue => {
                    let option_t = Expr::const_(
                        Name::from_string("OptionT"),
                        vec![monad_info.u.clone(), monad_info.v.clone()],
                    );
                    Expr::app(option_t, current)
                }
            };
        }

        current
    }

    /// Generate `OptionT.fail` (break/continue) at a specific layer.
    ///
    /// The expression targets the monad at the layer BELOW the given index.
    /// Used to implement `break` and `continue` in do-notation loops.
    pub(crate) fn mk_option_t_fail(
        &self,
        layer_idx: usize,
        alpha: Expr,
        monad_info: &DoMonadInfo,
    ) -> Expr {
        let inner_monad = if layer_idx > 0 {
            self.compute_monad_at(layer_idx - 1, monad_info)
        } else {
            monad_info.m.clone()
        };

        // OptionT.fail : {m} → {α} → OptionT m α
        let fail = Expr::const_(
            Name::from_string("OptionT.fail"),
            vec![monad_info.u.clone(), monad_info.v.clone()],
        );
        // @OptionT.fail m α
        Expr::app(Expr::app(fail, inner_monad), alpha)
    }

    /// Generate `ExceptT.mk (Pure.pure (Except.error e))` (early return).
    ///
    /// Early return throws the return value as an exception at the EarlyReturn layer.
    pub(crate) fn mk_early_return(
        &self,
        return_expr: Expr,
        alpha: Expr,
        monad_info: &DoMonadInfo,
    ) -> Option<Expr> {
        let idx = self.return_layer_idx?;
        let return_type = match &self.layers[idx] {
            ControlStackLayer::EarlyReturn { return_type } => return_type.clone(),
            _ => return None,
        };

        let inner_monad = if idx > 0 {
            self.compute_monad_at(idx - 1, monad_info)
        } else {
            monad_info.m.clone()
        };

        // MonadExcept.throw : {ε} → {m} → {α} → ε → m α
        let throw = Expr::const_(
            Name::from_string("MonadExcept.throw"),
            vec![
                monad_info.u.clone(),
                monad_info.v.clone(),
                monad_info.v.clone(),
            ],
        );
        // @MonadExcept.throw ρ (ExceptT ρ inner_m) α return_expr
        let except_t = Expr::const_(
            Name::from_string("ExceptT"),
            vec![monad_info.u.clone(), monad_info.v.clone()],
        );
        let except_t_m = Expr::app(Expr::app(except_t, return_type.clone()), inner_monad);
        let e = Expr::app(throw, return_type);
        let e = Expr::app(e, except_t_m);
        let e = Expr::app(e, alpha);
        Some(Expr::app(e, return_expr))
    }

    /// Generate the unwrapping chain after the do-block body.
    ///
    /// Applied from outermost to innermost:
    /// - Continue: `OptionT.run` → case split Some/None
    /// - Break: `OptionT.run` → case split Some/None
    /// - State: `StateT.run` → extract (result, final_state)
    /// - EarlyReturn: `ExceptT.run` → case split Except.ok/Except.error
    ///
    /// Returns a list of (layer, run_const, layer_idx) for the caller to apply.
    pub(crate) fn unwrap_sequence(&self, monad_info: &DoMonadInfo) -> Vec<UnwrapStep> {
        let mut steps = Vec::new();

        // Unwrap from outermost to innermost (reverse of build order)
        for (idx, layer) in self.layers.iter().enumerate().rev() {
            let step = match layer {
                ControlStackLayer::Base => continue,
                ControlStackLayer::EarlyReturn { return_type } => {
                    let run = Expr::const_(
                        Name::from_string("ExceptT.run"),
                        vec![monad_info.u.clone(), monad_info.v.clone()],
                    );
                    UnwrapStep {
                        layer_idx: idx,
                        run_const: run,
                        kind: UnwrapKind::EarlyReturn {
                            return_type: return_type.clone(),
                        },
                    }
                }
                ControlStackLayer::State { sigma, .. } => {
                    let run = Expr::const_(
                        Name::from_string("StateT.run"),
                        vec![monad_info.u.clone(), monad_info.v.clone()],
                    );
                    UnwrapStep {
                        layer_idx: idx,
                        run_const: run,
                        kind: UnwrapKind::State {
                            sigma: sigma.clone(),
                        },
                    }
                }
                ControlStackLayer::Break => {
                    let run = Expr::const_(
                        Name::from_string("OptionT.run"),
                        vec![monad_info.u.clone(), monad_info.v.clone()],
                    );
                    UnwrapStep {
                        layer_idx: idx,
                        run_const: run,
                        kind: UnwrapKind::Break,
                    }
                }
                ControlStackLayer::Continue => {
                    let run = Expr::const_(
                        Name::from_string("OptionT.run"),
                        vec![monad_info.u.clone(), monad_info.v.clone()],
                    );
                    UnwrapStep {
                        layer_idx: idx,
                        run_const: run,
                        kind: UnwrapKind::Continue,
                    }
                }
            };
            steps.push(step);
        }

        steps
    }
}

/// A step in the unwrapping sequence after a do-block.
pub(crate) struct UnwrapStep {
    pub(crate) layer_idx: usize,
    pub(crate) run_const: Expr,
    pub(crate) kind: UnwrapKind,
}

/// What kind of unwrapping to perform.
pub(crate) enum UnwrapKind {
    /// `ExceptT.run` → match on `Except.ok a | Except.error r`
    EarlyReturn { return_type: Expr },
    /// `StateT.run initial_state` → extract `(result, final_state)`
    State { sigma: Expr },
    /// `OptionT.run` → match on `Option.some a | Option.none` (break = none)
    Break,
    /// `OptionT.run` → match on `Option.some a | Option.none` (continue = none)
    Continue,
}

#[cfg(test)]
#[path = "elab_do_stack_tests.rs"]
mod tests;
