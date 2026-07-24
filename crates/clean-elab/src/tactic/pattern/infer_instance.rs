// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! infer_instance tactic: search for a type class instance.

use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Expr, ExprKind, Level};

use super::super::{exact, ProofState, TacticError, TacticResult};
use super::util::{extract_class_name, is_false_prop, is_true_prop};

/// Configuration for infer_instance tactic
#[derive(Debug, Clone, Default)]
pub struct InferInstanceConfig {
    /// Maximum search depth for instance resolution
    pub max_depth: usize,
    /// Whether to show the resolved instance
    pub verbose: bool,
}

impl InferInstanceConfig {
    pub fn new() -> Self {
        Self {
            max_depth: 32,
            verbose: false,
        }
    }

    #[must_use]
    pub fn with_max_depth(mut self, depth: usize) -> Self {
        self.max_depth = depth;
        self
    }

    #[must_use]
    pub fn verbose(mut self, v: bool) -> Self {
        self.verbose = v;
        self
    }
}

/// infer_instance tactic: search for a type class instance
///
/// This tactic tries to synthesize a type class instance for the goal.
/// It's useful when the goal is a type class constraint like `Decidable P`.
///
/// # Example
/// ```text
/// -- Goal: Decidable (1 = 1)
/// infer_instance
/// -- Solved by finding decidable equality instance
/// ```
///
/// # Contract
///
/// REQUIRES: `state.goals` is non-empty
/// REQUIRES: The current goal target is a type class application (e.g. `Decidable P`, `Inhabited A`)
/// ENSURES: On Ok, the goal is closed via `exact` with a synthesized instance expression
/// ENSURES: On Err(GoalMismatch), the target was not a recognized type class constraint
/// ENSURES: On Err(InstanceSynthesisFailed), no instance could be synthesized for the class and type
pub fn infer_instance(state: &mut ProofState) -> TacticResult {
    let mut config = InferInstanceConfig::new();
    if let Some(max_depth) = state.options().max_depth_override() {
        config.max_depth = max_depth;
    }
    if let Some(verbose) = state.options().verbose_override() {
        config.verbose = verbose;
    }
    infer_instance_with_config(state, config)
}

/// infer_instance with configuration
///
/// # Contract
///
/// REQUIRES: `state.goals` is non-empty
/// ENSURES: On Ok, the goal is closed via `exact` with a synthesized instance; search depth bounded by `config.max_depth`
/// ENSURES: Dispatches to class-specific synthesis (Decidable, Inhabited, Nonempty, BEq, Hashable, ToString/Repr) then falls back to environment lookup
pub fn infer_instance_with_config(
    state: &mut ProofState,
    config: InferInstanceConfig,
) -> TacticResult {
    if state.goals.is_empty() {
        return Err(TacticError::NoGoals);
    }

    let goal = state.current_goal().ok_or(TacticError::NoGoals)?;
    let target = goal.target.clone();

    // Try to find an instance by examining the target type
    // The target should be a type class application like `Decidable P`, `Inhabited A`, etc.

    // Extract the class name from the target
    let class_name = extract_class_name(&target)
        .ok_or_else(|| TacticError::GoalMismatch("goal is not a type class constraint".into()))?;

    // Try to synthesize an instance based on the class
    let instance = try_synthesize_instance(state, &class_name, &target, config.max_depth)?;

    // Apply the instance using exact
    exact(state, instance)
}

/// Try to synthesize a type class instance
fn try_synthesize_instance(
    state: &ProofState,
    class_name: &str,
    target: &Expr,
    max_depth: usize,
) -> Result<Expr, TacticError> {
    // Handle common decidable instances
    if class_name == "Decidable" || class_name.ends_with(".Decidable") {
        return synthesize_decidable_instance(state, target, max_depth);
    }

    // Handle Inhabited
    if class_name == "Inhabited" || class_name.ends_with(".Inhabited") {
        return synthesize_inhabited_instance(state, target);
    }

    // Handle Nonempty
    if class_name == "Nonempty" || class_name.ends_with(".Nonempty") {
        return synthesize_nonempty_instance(state, target);
    }

    // Handle BEq (Boolean equality)
    if class_name == "BEq" || class_name.ends_with(".BEq") {
        return synthesize_beq_instance(state, target);
    }

    // Handle Hashable
    if class_name == "Hashable" || class_name.ends_with(".Hashable") {
        return synthesize_hashable_instance(state, target);
    }

    // Handle ToString/Repr
    if class_name == "ToString" || class_name == "Repr" {
        return synthesize_repr_instance(state, target, class_name);
    }

    // Try to find a matching instance in the environment
    try_find_instance_in_env(state, class_name, target)
}

/// Synthesize a Decidable instance
fn synthesize_decidable_instance(
    state: &ProofState,
    target: &Expr,
    _max_depth: usize,
) -> Result<Expr, TacticError> {
    // Extract the proposition from Decidable P
    let prop = match target.kind() {
        ExprKind::App(_, p) => p.as_ref().clone(),
        _ => {
            return Err(TacticError::GoalMismatch(
                "infer_instance: expected Decidable application".into(),
            ));
        }
    };

    // Check for simple cases
    // True is decidable: @Decidable.isTrue True True.intro
    // Lean 4 kernel requires explicit {p : Prop} implicit arg (#2461)
    if is_true_prop(&prop) {
        return Ok(Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Decidable.isTrue"), vec![]),
                prop.clone(), // implicit {p} = True
            ),
            Expr::const_(Name::from_string("True.intro"), vec![]), // proof of True
        ));
    }

    // False is decidable: @Decidable.isFalse False (fun (h : False) => h)
    // ¬False = False → False, proof is the identity on False (#2461)
    if is_false_prop(&prop) {
        return Ok(Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Decidable.isFalse"), vec![]),
                prop.clone(), // implicit {p} = False
            ),
            // proof of ¬False: fun (h : False) => h
            Expr::lam(
                BinderInfo::Default,
                Expr::const_(Name::from_string("False"), vec![]),
                Expr::bvar(0),
            ),
        ));
    }

    // Equality `a = b`: do NOT hand-synthesize `instDecidableEq` — that constant
    // is registered nowhere, so the kernel rejected it with
    // `UnknownConst(instDecidableEq)` → `TypeCheckFailed`. Fall through to proper
    // environment-table resolution, which discharges `DecidableEq α` (and its
    // `decEq` bridge) recursively (#decide-instance).
    //
    // Try to look up instance in environment
    try_find_instance_in_env(state, "Decidable", target)
}

/// Synthesize an Inhabited instance
fn synthesize_inhabited_instance(_state: &ProofState, target: &Expr) -> Result<Expr, TacticError> {
    let ty = match target.kind() {
        ExprKind::App(_, t) => t.as_ref().clone(),
        _ => {
            return Err(TacticError::GoalMismatch(
                "infer_instance: expected Inhabited application".into(),
            ));
        }
    };

    // Common inhabited types
    if let ExprKind::Const(name, _) = ty.kind() {
        let s = name.to_string();
        match s.as_str() {
            // Universe succ(zero) correct: Inhabited.mk.{u} with Nat/UInt/Bool/String/Unit : Type 0 = Sort 1, so u = 1
            "Nat" | "UInt8" | "UInt16" | "UInt32" | "UInt64" => {
                return Ok(Expr::app(
                    Expr::const_(
                        Name::from_string("Inhabited.mk"),
                        vec![Level::succ(Level::zero())],
                    ),
                    Expr::nat_lit(0),
                ));
            }
            "Bool" => {
                return Ok(Expr::app(
                    Expr::const_(
                        Name::from_string("Inhabited.mk"),
                        vec![Level::succ(Level::zero())],
                    ),
                    Expr::const_(Name::from_string("false"), vec![]),
                ));
            }
            "String" => {
                return Ok(Expr::app(
                    Expr::const_(
                        Name::from_string("Inhabited.mk"),
                        vec![Level::succ(Level::zero())],
                    ),
                    Expr::str_lit(""),
                ));
            }
            "Unit" => {
                return Ok(Expr::app(
                    Expr::const_(
                        Name::from_string("Inhabited.mk"),
                        vec![Level::succ(Level::zero())],
                    ),
                    Expr::const_(Name::from_string("Unit.unit"), vec![]),
                ));
            }
            _ => {}
        }
    }

    Err(TacticError::InstanceSynthesisFailed {
        class: "Inhabited".into(),
        ty: format!("{ty:?}"),
    })
}

/// Synthesize a Nonempty instance
fn synthesize_nonempty_instance(state: &ProofState, target: &Expr) -> Result<Expr, TacticError> {
    // Nonempty follows from Inhabited
    let ty = match target.kind() {
        ExprKind::App(_, t) => t.as_ref().clone(),
        _ => {
            return Err(TacticError::GoalMismatch(
                "infer_instance: expected Nonempty application".into(),
            ));
        }
    };

    // Try to get Inhabited instance first
    // Inhabited : Sort u -> Type. For Type 0 types, u = Sort 1.
    let type_level = vec![Level::succ(Level::zero())];
    let inhabited_target = Expr::app(
        Expr::const_(Name::from_string("Inhabited"), type_level.clone()),
        ty.clone(),
    );

    if synthesize_inhabited_instance(state, &inhabited_target).is_ok() {
        return Ok(Expr::app(
            Expr::const_(Name::from_string("Nonempty.intro"), type_level.clone()),
            Expr::const_(Name::from_string("default"), type_level),
        ));
    }

    Err(TacticError::InstanceSynthesisFailed {
        class: "Nonempty".into(),
        ty: format!("{ty:?}"),
    })
}

/// Synthesize a BEq instance
fn synthesize_beq_instance(_state: &ProofState, target: &Expr) -> Result<Expr, TacticError> {
    let ty = match target.kind() {
        ExprKind::App(_, t) => t.as_ref().clone(),
        _ => {
            return Err(TacticError::GoalMismatch(
                "infer_instance: expected BEq application".into(),
            ));
        }
    };

    // Common types with BEq
    if let ExprKind::Const(name, _) = ty.kind() {
        let s = name.to_string();
        match s.as_str() {
            "Nat" => {
                return Ok(Expr::const_(Name::from_string("instBEqNat"), vec![]));
            }
            "Bool" => {
                return Ok(Expr::const_(Name::from_string("instBEqBool"), vec![]));
            }
            "String" => {
                return Ok(Expr::const_(Name::from_string("instBEqString"), vec![]));
            }
            "Int" => {
                return Ok(Expr::const_(Name::from_string("instBEqInt"), vec![]));
            }
            _ => {}
        }
    }

    Err(TacticError::InstanceSynthesisFailed {
        class: "BEq".into(),
        ty: format!("{ty:?}"),
    })
}

/// Synthesize a Hashable instance
fn synthesize_hashable_instance(_state: &ProofState, target: &Expr) -> Result<Expr, TacticError> {
    let ty = match target.kind() {
        ExprKind::App(_, t) => t.as_ref().clone(),
        _ => {
            return Err(TacticError::GoalMismatch(
                "infer_instance: expected Hashable application".into(),
            ));
        }
    };

    if let ExprKind::Const(name, _) = ty.kind() {
        let s = name.to_string();
        match s.as_str() {
            "Nat" => {
                return Ok(Expr::const_(Name::from_string("instHashableNat"), vec![]));
            }
            "String" => {
                return Ok(Expr::const_(
                    Name::from_string("instHashableString"),
                    vec![],
                ));
            }
            "Bool" => {
                return Ok(Expr::const_(Name::from_string("instHashableBool"), vec![]));
            }
            _ => {}
        }
    }

    Err(TacticError::InstanceSynthesisFailed {
        class: "Hashable".into(),
        ty: format!("{ty:?}"),
    })
}

/// Synthesize a ToString/Repr instance
fn synthesize_repr_instance(
    _state: &ProofState,
    target: &Expr,
    class: &str,
) -> Result<Expr, TacticError> {
    let ty = match target.kind() {
        ExprKind::App(_, t) => t.as_ref().clone(),
        _ => {
            return Err(TacticError::GoalMismatch(format!(
                "infer_instance: expected {class} application"
            )));
        }
    };

    if let ExprKind::Const(name, _) = ty.kind() {
        let s = name.to_string();
        let prefix = if class == "ToString" {
            "instToString"
        } else {
            "instRepr"
        };
        match s.as_str() {
            "Nat" => {
                return Ok(Expr::const_(
                    Name::from_string(&format!("{prefix}Nat")),
                    vec![],
                ));
            }
            "Bool" => {
                return Ok(Expr::const_(
                    Name::from_string(&format!("{prefix}Bool")),
                    vec![],
                ));
            }
            "String" => {
                return Ok(Expr::const_(
                    Name::from_string(&format!("{prefix}String")),
                    vec![],
                ));
            }
            "Int" => {
                return Ok(Expr::const_(
                    Name::from_string(&format!("{prefix}Int")),
                    vec![],
                ));
            }
            _ => {}
        }
    }

    Err(TacticError::InstanceSynthesisFailed {
        class: class.into(),
        ty: format!("{ty:?}"),
    })
}

/// Try to find an instance in the environment
fn try_find_instance_in_env(
    state: &ProofState,
    class_name: &str,
    target: &Expr,
) -> Result<Expr, TacticError> {
    // First, try proper instance resolution using the instance table
    if let Some(instances) = state.instances.as_ref() {
        use crate::instances::extract_class_app;

        if let Some(goal) = state.goals.front() {
            // Try to find a matching instance with type checking
            if let Some((_name, goal_args)) = extract_class_app(target) {
                let registered = instances.get_instances(&Name::from_string(class_name));
                for inst in registered {
                    // Extract instance type args
                    if let Some((_, inst_args)) = extract_class_app(&inst.type_) {
                        if inst_args.len() == goal_args.len() {
                            // Check if instance arguments match goal arguments
                            let mut matches = true;
                            for (inst_arg, goal_arg) in inst_args.iter().zip(goal_args.iter()) {
                                if !state.is_def_eq(goal, inst_arg, goal_arg) {
                                    matches = false;
                                    break;
                                }
                            }
                            if matches {
                                // Return instance expression directly (already fully applied)
                                return Ok(inst.expr.clone());
                            }
                        }
                    }
                }
            }
        }
    }

    // Fall back to name pattern matching
    // Instance names typically follow patterns like:
    // instClassName, inst_class_name, ClassName.instName
    let patterns = [
        format!("inst{class_name}"),
        format!("inst_{}", class_name.to_lowercase()),
        format!("{class_name}.inst"),
    ];

    for pattern in &patterns {
        if state.env.get_const(&Name::from_string(pattern)).is_some() {
            return Ok(Expr::const_(Name::from_string(pattern), vec![]));
        }
    }

    Err(TacticError::InstanceSynthesisFailed {
        class: class_name.into(),
        ty: format!("{target:?}"),
    })
}
