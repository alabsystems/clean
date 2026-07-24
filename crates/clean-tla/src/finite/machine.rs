// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Machine extraction + exhaustive exploration for the S4 finite fragment.
//!
//! [`FiniteMachine::from_cert`] re-encodes a multi-variable machine FROM the
//! certificate's own `spec_src` (source fidelity): state = the ordered
//! `var_sorts` manifest (scalars, plus `[lo..hi -> BOOLEAN]` function
//! variables flattened to one Bool slot per index — the Tier-0 `evict_full`
//! shape); `Init` = a conjunction of equalities pinning every variable;
//! `Next` = a disjunction of guarded assignments with explicit or implicit
//! `UNCHANGED`; invariants = quantifier-free arith/bool plus `∀` over finite
//! domains.
//!
//! [`FiniteMachine::explore`] runs an exhaustive BFS over the reachable state
//! space under DUAL semantics: every guard verdict, update value, and
//! invariant verdict is evaluated both with exact `Int` arithmetic (the TLA+
//! meaning) and with `Nat`-truncating subtraction (the kernel encoding's
//! meaning). Any divergence FAILS CLOSED (`TruncationDivergence`), so the
//! kernel theorem's `Nat` semantics provably agrees with the spec's `Int`
//! semantics on every state the proof touches. An invariant violation fails
//! closed as [`FiniteError::Falsified`] with a step-replayed counterexample
//! trace (the in-process ratchet — no stdout parsing anywhere).

use std::collections::BTreeMap;

use super::{FiniteError, TraceStep, MAX_ENUM_STATES};
use crate::finite::parse::{operator_table, parse_fragment, Tx};
use crate::ty_cert::TyCert;

/// One declared state variable.
#[derive(Debug, Clone)]
pub struct VarSpec {
    /// Variable name as declared in `var_sorts`.
    pub name: String,
    /// Scalar (`Int`/`Nat`) or Tier-0 function shape.
    pub kind: VarKind,
}

/// The kind of a state variable.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VarKind {
    /// A machine int, modelled as a cfg-bounded `Nat`.
    Scalar,
    /// `[lo..hi -> BOOLEAN]` — flattened to `hi-lo+1` Bool slots.
    FnBool {
        /// Domain lower bound (inclusive).
        lo: i64,
        /// Domain upper bound (inclusive).
        hi: i64,
    },
}

/// One packed-state slot (a scalar variable, or one index of a function
/// variable).
#[derive(Debug, Clone)]
pub struct SlotInfo {
    /// Human-readable name (`seq`, or `live[3]`).
    pub display: String,
    /// Index into [`FiniteMachine::vars`].
    pub var: usize,
    /// For function-variable slots: the domain key of this slot.
    pub key: Option<i64>,
}

/// A guarded-assignment action: prime-free guard conjuncts plus one update
/// per variable (explicit, or implicit `UNCHANGED`).
#[derive(Debug, Clone)]
pub struct ActionSpec {
    /// Action name (the referenced operator name, or a positional label).
    pub name: String,
    /// Prime-free guard conjuncts (empty = always enabled).
    pub guard: Vec<Tx>,
    /// Per-variable update expressions, aligned with `vars`; `None` =
    /// UNCHANGED.
    pub updates: Vec<Option<Tx>>,
}

/// The extracted finite machine.
#[derive(Debug, Clone)]
pub struct FiniteMachine {
    /// Module/machine name (from the cert's `spec_src` MODULE line if present).
    pub name: String,
    /// Ordered variable manifest (replaces `sole_var`).
    pub vars: Vec<VarSpec>,
    /// Flattened packed-state slot manifest.
    pub slots: Vec<SlotInfo>,
    /// `CONSTANT` values the enumeration is keyed on.
    pub consts: BTreeMap<String, i64>,
    /// The unique initial state (slot values).
    pub init_slots: Vec<i64>,
    /// The guarded-assignment actions (the `Next` disjunction).
    pub actions: Vec<ActionSpec>,
    /// Named invariants (all conjoined into `Safety`).
    pub invariants: Vec<(String, Tx)>,
}

/// Arithmetic mode for the dual evaluator.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EvalMode {
    /// Exact `Int` arithmetic — the TLA+ semantics.
    IntExact,
    /// `Nat`-truncating subtraction — the kernel encoding's semantics.
    NatTrunc,
}

/// A runtime value in the evaluator.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Val {
    /// Integer.
    I(i64),
    /// Boolean.
    B(bool),
    /// Function value: per-key bits over the variable's declared domain.
    F(Vec<bool>),
}

/// Exhaustive-exploration result: the reachable set (BFS order, init first)
/// plus the per-state action edges the encoder needs.
///
/// `reachable` is deliberately a PUBLIC, tamperable field: the mutation
/// battery perturbs it (drop a successor / inject an unsafe state / reorder)
/// and asserts the KERNEL — not this crate's Rust — rejects the resulting
/// product. Untampered flows always pass a BFS-closed set.
#[derive(Debug, Clone)]
pub struct Explored {
    /// Reachable states in BFS order; `reachable[0]` is the initial state.
    pub reachable: Vec<Vec<i64>>,
    /// Per state, per action: `Some(successor-state-index)` iff the guard is
    /// true there.
    pub edges: Vec<Vec<Option<usize>>>,
}

impl FiniteMachine {
    /// Extract the machine from a certificate, entirely from `spec_src` +
    /// `var_sorts` + `constants`. Fails closed on anything outside the
    /// fragment.
    pub fn from_cert(cert: &TyCert) -> Result<Self, FiniteError> {
        let consts: BTreeMap<String, i64> = cert.constants.iter().cloned().collect();

        if cert.var_sorts.is_empty() {
            return Err(FiniteError::Fragment(
                "certificate has an empty var_sorts manifest".into(),
            ));
        }
        let mut vars = Vec::new();
        for (v, sort) in &cert.var_sorts {
            let kind = parse_sort(sort, &consts).ok_or_else(|| FiniteError::UnsupportedSort {
                var: v.clone(),
                sort: sort.clone(),
            })?;
            vars.push(VarSpec {
                name: v.clone(),
                kind,
            });
        }
        let mut slots = Vec::new();
        for (vi, v) in vars.iter().enumerate() {
            match v.kind {
                VarKind::Scalar => slots.push(SlotInfo {
                    display: v.name.clone(),
                    var: vi,
                    key: None,
                }),
                VarKind::FnBool { lo, hi } => {
                    if lo > hi {
                        return Err(FiniteError::Fragment(format!(
                            "function variable {} has empty domain {lo}..{hi}",
                            v.name
                        )));
                    }
                    for k in lo..=hi {
                        slots.push(SlotInfo {
                            display: format!("{}[{k}]", v.name),
                            var: vi,
                            key: Some(k),
                        });
                    }
                }
            }
        }

        let name = cert
            .spec_src
            .lines()
            .find_map(|l| {
                let l = l.trim().trim_matches('-');
                l.trim()
                    .strip_prefix("MODULE")
                    .map(|m| m.trim().to_string())
            })
            .unwrap_or_else(|| "Machine".to_string());

        // `operator_table` fails closed on duplicate definitions and on
        // ambiguous bullet shapes, so collecting into a map is collision-free.
        let ops: BTreeMap<String, String> = operator_table(&cert.spec_src)
            .map_err(FiniteError::Parse)?
            .into_iter()
            .collect();
        let get_op = |op: &str| -> Result<Tx, FiniteError> {
            let body = ops
                .get(op)
                .ok_or_else(|| FiniteError::OperatorNotFound(op.to_string()))?;
            parse_fragment(body).map_err(FiniteError::Parse)
        };

        let init_name = cert
            .init
            .as_deref()
            .ok_or_else(|| FiniteError::Fragment("certificate has no INIT operator".into()))?;
        let next_name = cert
            .next
            .as_deref()
            .ok_or_else(|| FiniteError::Fragment("certificate has no NEXT operator".into()))?;
        if cert.invariants.is_empty() {
            return Err(FiniteError::Fragment(
                "certificate lists no INVARIANT operators".into(),
            ));
        }

        let mut m = FiniteMachine {
            name,
            vars,
            slots,
            consts,
            init_slots: Vec::new(),
            actions: Vec::new(),
            invariants: Vec::new(),
        };

        // Expand operator references so downstream sees pure fragment ASTs.
        let expand = |m: &FiniteMachine, t: &Tx| -> Result<Tx, FiniteError> {
            m.expand(t, &ops, &mut Vec::new(), 0)
        };

        // ── Init: conjunction of equalities pinning EVERY variable once. ──
        let init_tx = expand(&m, &get_op(init_name)?)?;
        let mut init_vals: Vec<Option<Val>> = vec![None; m.vars.len()];
        for conj in init_tx.split_and() {
            let Tx::Eq(lhs, rhs) = conj else {
                return Err(FiniteError::Fragment(format!(
                    "Init conjunct is not an equality: {conj:?}"
                )));
            };
            let Tx::Ident(vname) = &**lhs else {
                return Err(FiniteError::Fragment(format!(
                    "Init equality does not pin a variable: {lhs:?}"
                )));
            };
            let vi = m
                .var_index(vname)
                .ok_or_else(|| FiniteError::Fragment(format!("Init pins unknown var {vname}")))?;
            let val = m.eval_closed(rhs, vi)?;
            if init_vals[vi].replace(val).is_some() {
                return Err(FiniteError::Fragment(format!(
                    "Init pins variable {vname} twice"
                )));
            }
        }
        let mut init_slots = Vec::with_capacity(m.slots.len());
        for (vi, v) in m.vars.iter().enumerate() {
            let val = init_vals[vi].as_ref().ok_or_else(|| {
                FiniteError::Fragment(format!("Init does not pin variable {}", v.name))
            })?;
            match (&v.kind, val) {
                (VarKind::Scalar, Val::I(n)) => {
                    if *n < 0 {
                        return Err(FiniteError::NegativeValue {
                            context: format!("Init value of {} is {n}", v.name),
                        });
                    }
                    init_slots.push(*n);
                }
                (VarKind::FnBool { lo, hi }, Val::F(bits)) => {
                    // The comprehension's domain must match the DECLARED sort
                    // domain, or the flattened slot vector would misalign
                    // (typed refusal, not a downstream index panic).
                    if bits.len() != (hi - lo + 1) as usize {
                        return Err(FiniteError::Fragment(format!(
                            "Init value of {} has domain size {} but the \
                             declared sort [{lo}..{hi} -> BOOLEAN] expects {}",
                            v.name,
                            bits.len(),
                            hi - lo + 1
                        )));
                    }
                    init_slots.extend(bits.iter().map(|b| i64::from(*b)));
                }
                (_, got) => {
                    return Err(FiniteError::Fragment(format!(
                        "Init value of {} has the wrong shape: {got:?}",
                        v.name
                    )))
                }
            }
        }
        m.init_slots = init_slots;

        // ── Next: disjunction of guarded assignments. ──
        let next_raw = get_op(next_name)?;
        let mut actions = Vec::new();
        for (k, leaf) in next_raw.split_or().into_iter().enumerate() {
            let (aname, body) = match leaf {
                Tx::Ident(op) if ops.contains_key(op) => (op.clone(), expand(&m, leaf)?),
                other => (format!("Action{k}"), expand(&m, other)?),
            };
            for (j, sub) in body.split_or().into_iter().enumerate() {
                let name = if body.split_or().len() == 1 {
                    aname.clone()
                } else {
                    format!("{aname}_{j}")
                };
                actions.push(m.action_from_conjunction(name, sub)?);
            }
        }
        m.actions = actions;

        // ── Invariants: each prime-free; all conjoined into Safety. ──
        for inv in &cert.invariants {
            let t = expand(&m, &get_op(inv)?)?;
            if t.has_prime() {
                return Err(FiniteError::Fragment(format!(
                    "invariant {inv} mentions primed state"
                )));
            }
            m.invariants.push((inv.clone(), t));
        }
        Ok(m)
    }

    /// Index of a variable by name.
    pub fn var_index(&self, name: &str) -> Option<usize> {
        self.vars.iter().position(|v| v.name == name)
    }

    /// Slot index of a scalar variable / function-variable key.
    pub(crate) fn slot_index(&self, var: usize, key: Option<i64>) -> Option<usize> {
        self.slots.iter().position(|s| s.var == var && s.key == key)
    }

    fn action_from_conjunction(&self, name: String, body: &Tx) -> Result<ActionSpec, FiniteError> {
        let mut guard = Vec::new();
        let mut updates: Vec<Option<Tx>> = vec![None; self.vars.len()];
        for conj in body.split_and() {
            match conj {
                Tx::Eq(lhs, rhs) if matches!(**lhs, Tx::Prime(_)) => {
                    let Tx::Prime(vname) = &**lhs else {
                        unreachable!()
                    };
                    let vi = self.var_index(vname).ok_or_else(|| {
                        FiniteError::Fragment(format!("action {name} primes unknown var {vname}"))
                    })?;
                    if rhs.has_prime() {
                        return Err(FiniteError::Fragment(format!(
                            "action {name}: update of {vname} reads primed state (out of fragment)"
                        )));
                    }
                    if updates[vi].replace((**rhs).clone()).is_some() {
                        return Err(FiniteError::Fragment(format!(
                            "action {name} updates {vname} twice"
                        )));
                    }
                }
                Tx::Unchanged(vs) => {
                    for vname in vs {
                        let vi = self.var_index(vname).ok_or_else(|| {
                            FiniteError::Fragment(format!(
                                "action {name}: UNCHANGED unknown var {vname}"
                            ))
                        })?;
                        if updates[vi].replace(Tx::Ident(vname.clone())).is_some() {
                            return Err(FiniteError::Fragment(format!(
                                "action {name}: {vname} both updated and UNCHANGED"
                            )));
                        }
                    }
                }
                other if !other.has_prime() => guard.push(other.clone()),
                other => {
                    return Err(FiniteError::Fragment(format!(
                    "action {name}: conjunct with primes in a non-assignment position: {other:?}"
                )))
                }
            }
        }
        // Implicit UNCHANGED for unmentioned variables (the trust_model! shape).
        for (vi, u) in updates.iter_mut().enumerate() {
            if u.is_none() {
                *u = Some(Tx::Ident(self.vars[vi].name.clone()));
            }
        }
        Ok(ActionSpec {
            name,
            guard,
            updates,
        })
    }

    /// Substitute operator references (identifiers naming other operators) by
    /// their parsed bodies, respecting binder shadowing. Depth-capped.
    fn expand(
        &self,
        t: &Tx,
        ops: &BTreeMap<String, String>,
        shadow: &mut Vec<String>,
        depth: usize,
    ) -> Result<Tx, FiniteError> {
        if depth > 64 {
            return Err(FiniteError::Fragment(
                "operator expansion exceeded depth 64 (cyclic definitions?)".into(),
            ));
        }
        let rec = |slf: &Self, x: &Tx, sh: &mut Vec<String>| -> Result<Box<Tx>, FiniteError> {
            Ok(Box::new(slf.expand(x, ops, sh, depth + 1)?))
        };
        Ok(match t {
            Tx::Ident(id) => {
                let is_shadowed = shadow.contains(id);
                let is_var = self.var_index(id).is_some();
                let is_const = self.consts.contains_key(id);
                if !is_shadowed && !is_var && !is_const {
                    if let Some(body) = ops.get(id) {
                        let parsed = parse_fragment(body).map_err(FiniteError::Parse)?;
                        return self.expand(&parsed, ops, shadow, depth + 1);
                    }
                }
                t.clone()
            }
            Tx::Num(_) | Tx::BoolLit(_) | Tx::Prime(_) | Tx::Unchanged(_) => t.clone(),
            Tx::Add(a, b) => Tx::Add(rec(self, a, shadow)?, rec(self, b, shadow)?),
            Tx::Sub(a, b) => Tx::Sub(rec(self, a, shadow)?, rec(self, b, shadow)?),
            Tx::Eq(a, b) => Tx::Eq(rec(self, a, shadow)?, rec(self, b, shadow)?),
            Tx::Neq(a, b) => Tx::Neq(rec(self, a, shadow)?, rec(self, b, shadow)?),
            Tx::Le(a, b) => Tx::Le(rec(self, a, shadow)?, rec(self, b, shadow)?),
            Tx::Lt(a, b) => Tx::Lt(rec(self, a, shadow)?, rec(self, b, shadow)?),
            Tx::Ge(a, b) => Tx::Ge(rec(self, a, shadow)?, rec(self, b, shadow)?),
            Tx::Gt(a, b) => Tx::Gt(rec(self, a, shadow)?, rec(self, b, shadow)?),
            Tx::And(a, b) => Tx::And(rec(self, a, shadow)?, rec(self, b, shadow)?),
            Tx::Or(a, b) => Tx::Or(rec(self, a, shadow)?, rec(self, b, shadow)?),
            Tx::Iff(a, b) => Tx::Iff(rec(self, a, shadow)?, rec(self, b, shadow)?),
            Tx::Not(a) => Tx::Not(rec(self, a, shadow)?),
            Tx::Ite(c, x, y) => Tx::Ite(
                rec(self, c, shadow)?,
                rec(self, x, shadow)?,
                rec(self, y, shadow)?,
            ),
            Tx::FnAccess(f, i) => Tx::FnAccess(f.clone(), rec(self, i, shadow)?),
            Tx::Except { base, index, value } => Tx::Except {
                base: base.clone(),
                index: rec(self, index, shadow)?,
                value: rec(self, value, shadow)?,
            },
            Tx::Comprehension {
                binder,
                lo,
                hi,
                body,
            } => {
                let lo = rec(self, lo, shadow)?;
                let hi = rec(self, hi, shadow)?;
                shadow.push(binder.clone());
                let body = rec(self, body, shadow);
                shadow.pop();
                Tx::Comprehension {
                    binder: binder.clone(),
                    lo,
                    hi,
                    body: body?,
                }
            }
            Tx::Forall {
                binder,
                lo,
                hi,
                body,
            } => {
                let lo = rec(self, lo, shadow)?;
                let hi = rec(self, hi, shadow)?;
                shadow.push(binder.clone());
                let body = rec(self, body, shadow);
                shadow.pop();
                Tx::Forall {
                    binder: binder.clone(),
                    lo,
                    hi,
                    body: body?,
                }
            }
        })
    }

    /// Evaluate a state-variable-free expression (Init values, domain bounds).
    fn eval_closed(&self, t: &Tx, target_var: usize) -> Result<Val, FiniteError> {
        let mut names = Vec::new();
        collect_state_idents(t, self, &mut names);
        if !names.is_empty() {
            return Err(FiniteError::Fragment(format!(
                "Init value for {} reads state variables {names:?} (must be constant)",
                self.vars[target_var].name
            )));
        }
        let zero = vec![0i64; self.slots.len()];
        self.eval(t, &zero, &mut Vec::new(), EvalMode::IntExact)
    }

    /// Evaluate a constant expression to an integer (domain bounds).
    fn eval_const_i64(&self, t: &Tx, binders: &mut Vec<(String, i64)>) -> Result<i64, FiniteError> {
        let zero = vec![0i64; self.slots.len()];
        match self.eval(t, &zero, binders, EvalMode::IntExact)? {
            Val::I(n) => Ok(n),
            other => Err(FiniteError::Fragment(format!(
                "expected an integer domain bound, got {other:?}"
            ))),
        }
    }

    /// The dual-mode evaluator. Lazy exactly where the kernel's iota/`Bool.rec`
    /// reduction is lazy (`/\`, `\/`, `IF`, `\A`), so the Rust verdicts match
    /// what the kernel will compute on literals.
    pub(crate) fn eval(
        &self,
        t: &Tx,
        st: &[i64],
        binders: &mut Vec<(String, i64)>,
        mode: EvalMode,
    ) -> Result<Val, FiniteError> {
        let as_i = |v: Val| -> Result<i64, FiniteError> {
            match v {
                Val::I(n) => Ok(n),
                other => Err(FiniteError::Fragment(format!(
                    "expected an integer, got {other:?}"
                ))),
            }
        };
        let as_b = |v: Val| -> Result<bool, FiniteError> {
            match v {
                Val::B(b) => Ok(b),
                other => Err(FiniteError::Fragment(format!(
                    "expected a boolean, got {other:?}"
                ))),
            }
        };
        match t {
            Tx::Num(n) => Ok(Val::I(*n)),
            Tx::BoolLit(b) => Ok(Val::B(*b)),
            Tx::Prime(v) => Err(FiniteError::Fragment(format!(
                "primed read {v}' in an evaluation position"
            ))),
            Tx::Unchanged(_) => Err(FiniteError::Fragment(
                "UNCHANGED in an evaluation position".into(),
            )),
            Tx::Ident(id) => {
                if let Some((_, v)) = binders.iter().rev().find(|(n, _)| n == id) {
                    return Ok(Val::I(*v));
                }
                if let Some(c) = self.consts.get(id) {
                    return Ok(Val::I(*c));
                }
                match self.var_index(id) {
                    Some(vi) => match self.vars[vi].kind {
                        VarKind::Scalar => {
                            let si = self.slot_index(vi, None).ok_or_else(|| {
                                FiniteError::Internal(format!("no slot for scalar {id}"))
                            })?;
                            Ok(Val::I(st[si]))
                        }
                        VarKind::FnBool { lo, hi } => {
                            let mut bits = Vec::with_capacity((hi - lo + 1) as usize);
                            for k in lo..=hi {
                                let si = self.slot_index(vi, Some(k)).ok_or_else(|| {
                                    FiniteError::Internal(format!("no slot for {id}[{k}]"))
                                })?;
                                bits.push(st[si] != 0);
                            }
                            Ok(Val::F(bits))
                        }
                    },
                    None => Err(FiniteError::Fragment(format!("unknown identifier {id}"))),
                }
            }
            Tx::Add(a, b) => {
                let x = as_i(self.eval(a, st, binders, mode)?)?;
                let y = as_i(self.eval(b, st, binders, mode)?)?;
                Ok(Val::I(x.checked_add(y).ok_or_else(|| {
                    FiniteError::Fragment("integer overflow in +".into())
                })?))
            }
            Tx::Sub(a, b) => {
                let x = as_i(self.eval(a, st, binders, mode)?)?;
                let y = as_i(self.eval(b, st, binders, mode)?)?;
                let d = x
                    .checked_sub(y)
                    .ok_or_else(|| FiniteError::Fragment("integer overflow in -".into()))?;
                Ok(Val::I(match mode {
                    EvalMode::IntExact => d,
                    EvalMode::NatTrunc => d.max(0),
                }))
            }
            Tx::Eq(a, b) => {
                let x = as_i(self.eval(a, st, binders, mode)?)?;
                let y = as_i(self.eval(b, st, binders, mode)?)?;
                Ok(Val::B(x == y))
            }
            Tx::Neq(a, b) => {
                let x = as_i(self.eval(a, st, binders, mode)?)?;
                let y = as_i(self.eval(b, st, binders, mode)?)?;
                Ok(Val::B(x != y))
            }
            Tx::Le(a, b) => {
                let x = as_i(self.eval(a, st, binders, mode)?)?;
                let y = as_i(self.eval(b, st, binders, mode)?)?;
                Ok(Val::B(x <= y))
            }
            Tx::Lt(a, b) => {
                let x = as_i(self.eval(a, st, binders, mode)?)?;
                let y = as_i(self.eval(b, st, binders, mode)?)?;
                Ok(Val::B(x < y))
            }
            Tx::Ge(a, b) => {
                let x = as_i(self.eval(a, st, binders, mode)?)?;
                let y = as_i(self.eval(b, st, binders, mode)?)?;
                Ok(Val::B(x >= y))
            }
            Tx::Gt(a, b) => {
                let x = as_i(self.eval(a, st, binders, mode)?)?;
                let y = as_i(self.eval(b, st, binders, mode)?)?;
                Ok(Val::B(x > y))
            }
            Tx::And(a, b) => {
                if !as_b(self.eval(a, st, binders, mode)?)? {
                    return Ok(Val::B(false));
                }
                self.eval(b, st, binders, mode)
            }
            Tx::Or(a, b) => {
                if as_b(self.eval(a, st, binders, mode)?)? {
                    return Ok(Val::B(true));
                }
                self.eval(b, st, binders, mode)
            }
            Tx::Not(a) => Ok(Val::B(!as_b(self.eval(a, st, binders, mode)?)?)),
            Tx::Iff(a, b) => {
                let x = as_b(self.eval(a, st, binders, mode)?)?;
                let y = as_b(self.eval(b, st, binders, mode)?)?;
                Ok(Val::B(x == y))
            }
            Tx::Ite(c, x, y) => {
                if as_b(self.eval(c, st, binders, mode)?)? {
                    self.eval(x, st, binders, mode)
                } else {
                    self.eval(y, st, binders, mode)
                }
            }
            Tx::FnAccess(f, idx) => {
                let vi = self
                    .var_index(f)
                    .ok_or_else(|| FiniteError::Fragment(format!("unknown function var {f}")))?;
                let VarKind::FnBool { lo, hi } = self.vars[vi].kind else {
                    return Err(FiniteError::Fragment(format!(
                        "{f} is not a function variable"
                    )));
                };
                let k = as_i(self.eval(idx, st, binders, mode)?)?;
                if k < lo || k > hi {
                    return Err(FiniteError::OutOfDomain {
                        fn_var: f.clone(),
                        index: k,
                    });
                }
                let si = self
                    .slot_index(vi, Some(k))
                    .ok_or_else(|| FiniteError::Internal(format!("no slot for {f}[{k}]")))?;
                Ok(Val::B(st[si] != 0))
            }
            Tx::Comprehension {
                binder,
                lo,
                hi,
                body,
            } => {
                let l = self.eval_const_i64(lo, binders)?;
                let h = self.eval_const_i64(hi, binders)?;
                let mut bits = Vec::new();
                for k in l..=h {
                    binders.push((binder.clone(), k));
                    let r = self.eval(body, st, binders, mode);
                    binders.pop();
                    bits.push(as_b(r?)?);
                }
                Ok(Val::F(bits))
            }
            Tx::Except { base, index, value } => {
                let vi = self.var_index(base).ok_or_else(|| {
                    FiniteError::Fragment(format!("EXCEPT on unknown function var {base}"))
                })?;
                let VarKind::FnBool { lo, hi } = self.vars[vi].kind else {
                    return Err(FiniteError::Fragment(format!(
                        "EXCEPT on non-function var {base}"
                    )));
                };
                let cur = self.eval(&Tx::Ident(base.clone()), st, binders, mode)?;
                let Val::F(mut bits) = cur else {
                    return Err(FiniteError::Internal("fn var read is not F".into()));
                };
                let k = as_i(self.eval(index, st, binders, mode)?)?;
                if k < lo || k > hi {
                    return Err(FiniteError::OutOfDomain {
                        fn_var: base.clone(),
                        index: k,
                    });
                }
                let v = as_b(self.eval(value, st, binders, mode)?)?;
                bits[(k - lo) as usize] = v;
                Ok(Val::F(bits))
            }
            Tx::Forall {
                binder,
                lo,
                hi,
                body,
            } => {
                let l = self.eval_const_i64(lo, binders)?;
                let h = self.eval_const_i64(hi, binders)?;
                for k in l..=h {
                    binders.push((binder.clone(), k));
                    let r = self.eval(body, st, binders, mode);
                    binders.pop();
                    if !as_b(r?)? {
                        return Ok(Val::B(false));
                    }
                }
                Ok(Val::B(true))
            }
        }
    }

    /// Evaluate an expression under BOTH semantics; fail closed on divergence.
    fn eval_dual(&self, t: &Tx, st: &[i64], context: &str) -> Result<Val, FiniteError> {
        let exact = self.eval(t, st, &mut Vec::new(), EvalMode::IntExact)?;
        let trunc = self.eval(t, st, &mut Vec::new(), EvalMode::NatTrunc)?;
        if exact != trunc {
            return Err(FiniteError::TruncationDivergence {
                context: format!(
                    "{context}: Int semantics gives {exact:?} but Nat-truncating \
                     subtraction gives {trunc:?} at state {}",
                    self.display_state(st)
                ),
            });
        }
        Ok(exact)
    }

    /// Human-readable `var=value` rendering of a state.
    pub fn display_state(&self, st: &[i64]) -> String {
        self.slots
            .iter()
            .zip(st.iter())
            .map(|(s, v)| {
                if s.key.is_some() {
                    format!("{}={}", s.display, if *v != 0 { "TRUE" } else { "FALSE" })
                } else {
                    format!("{}={v}", s.display)
                }
            })
            .collect::<Vec<_>>()
            .join(", ")
    }

    /// Whether the guard of `action` holds at `st` (dual-checked).
    fn guard_holds(&self, action: &ActionSpec, st: &[i64]) -> Result<bool, FiniteError> {
        for g in &action.guard {
            let v = self.eval_dual(g, st, &format!("guard of {}", action.name))?;
            match v {
                Val::B(true) => {}
                Val::B(false) => return Ok(false),
                other => {
                    return Err(FiniteError::Fragment(format!(
                        "guard of {} is not boolean: {other:?}",
                        action.name
                    )))
                }
            }
        }
        Ok(true)
    }

    /// Fire `action` at `st` (guard assumed true): compute the successor
    /// (dual-checked, negativity-checked).
    fn fire(&self, action: &ActionSpec, st: &[i64]) -> Result<Vec<i64>, FiniteError> {
        let mut next = vec![0i64; self.slots.len()];
        for (vi, v) in self.vars.iter().enumerate() {
            let upd = action.updates[vi].as_ref().ok_or_else(|| {
                FiniteError::Internal(format!(
                    "action {} missing update for {}",
                    action.name, v.name
                ))
            })?;
            let val =
                self.eval_dual(upd, st, &format!("update of {} in {}", v.name, action.name))?;
            match (&v.kind, val) {
                (VarKind::Scalar, Val::I(n)) => {
                    if n < 0 {
                        return Err(FiniteError::NegativeValue {
                            context: format!(
                                "action {} assigns {} = {n} at state {}",
                                action.name,
                                v.name,
                                self.display_state(st)
                            ),
                        });
                    }
                    let si = self
                        .slot_index(vi, None)
                        .ok_or_else(|| FiniteError::Internal("missing scalar slot".into()))?;
                    next[si] = n;
                }
                (VarKind::FnBool { lo, hi }, Val::F(bits)) => {
                    if bits.len() != (hi - lo + 1) as usize {
                        return Err(FiniteError::Fragment(format!(
                            "action {}: function update of {} has domain size {} (expected {})",
                            action.name,
                            v.name,
                            bits.len(),
                            hi - lo + 1
                        )));
                    }
                    for (off, bit) in bits.iter().enumerate() {
                        let k = lo + off as i64;
                        let si = self
                            .slot_index(vi, Some(k))
                            .ok_or_else(|| FiniteError::Internal("missing fn slot".into()))?;
                        next[si] = i64::from(*bit);
                    }
                }
                (_, got) => {
                    return Err(FiniteError::Fragment(format!(
                        "action {}: update of {} has the wrong shape: {got:?}",
                        action.name, v.name
                    )))
                }
            }
        }
        Ok(next)
    }

    /// Check every invariant at `st` (dual-checked); `Err(name)` on the first
    /// violated invariant.
    fn invariants_hold(&self, st: &[i64]) -> Result<Result<(), String>, FiniteError> {
        for (name, inv) in &self.invariants {
            match self.eval_dual(inv, st, &format!("invariant {name}"))? {
                Val::B(true) => {}
                Val::B(false) => return Ok(Err(name.clone())),
                other => {
                    return Err(FiniteError::Fragment(format!(
                        "invariant {name} is not boolean: {other:?}"
                    )))
                }
            }
        }
        Ok(Ok(()))
    }

    /// Exhaustive BFS over the reachable states, dual-checked throughout.
    ///
    /// Fails closed with [`FiniteError::Falsified`] (step-replayed trace) on a
    /// reachable invariant violation, and with
    /// [`FiniteError::StateSpaceBoundExceeded`] past [`MAX_ENUM_STATES`].
    pub fn explore(&self) -> Result<Explored, FiniteError> {
        let mut index: BTreeMap<Vec<i64>, usize> = BTreeMap::new();
        let mut reachable: Vec<Vec<i64>> = vec![self.init_slots.clone()];
        let mut parent: Vec<Option<(usize, usize)>> = vec![None];
        let mut edges: Vec<Vec<Option<usize>>> = Vec::new();
        index.insert(self.init_slots.clone(), 0);

        let mut cursor = 0usize;
        while cursor < reachable.len() {
            let st = reachable[cursor].clone();
            if let Err(inv) = self.invariants_hold(&st)? {
                return Err(self.falsified(inv, cursor, &reachable, &parent));
            }
            let mut row = Vec::with_capacity(self.actions.len());
            for (ai, action) in self.actions.iter().enumerate() {
                if !self.guard_holds(action, &st)? {
                    row.push(None);
                    continue;
                }
                let succ = self.fire(action, &st)?;
                let si = match index.get(&succ) {
                    Some(&i) => i,
                    None => {
                        let i = reachable.len();
                        if i >= MAX_ENUM_STATES {
                            return Err(FiniteError::StateSpaceBoundExceeded {
                                visited: i + 1,
                                cap: MAX_ENUM_STATES,
                            });
                        }
                        index.insert(succ.clone(), i);
                        reachable.push(succ);
                        parent.push(Some((cursor, ai)));
                        i
                    }
                };
                row.push(Some(si));
            }
            edges.push(row);
            cursor += 1;
        }
        Ok(Explored { reachable, edges })
    }

    /// Build the [`FiniteError::Falsified`] report: reconstruct the BFS path
    /// to the violating state and REPLAY it step-by-step through the
    /// transition relation (validate-before-publish, in-process).
    fn falsified(
        &self,
        invariant: String,
        bad: usize,
        reachable: &[Vec<i64>],
        parent: &[Option<(usize, usize)>],
    ) -> FiniteError {
        let mut chain = Vec::new();
        let mut cur = bad;
        while let Some((p, a)) = parent[cur] {
            chain.push((p, a, cur));
            cur = p;
        }
        chain.reverse();

        let mut trace = vec![TraceStep {
            action: "<init>".into(),
            state: self.display_state(&reachable[0]),
        }];
        let mut replay_state = reachable[0].clone();
        let mut replay_validated = true;
        for (p, ai, next_idx) in &chain {
            let action = &self.actions[*ai];
            let ok = replay_state == reachable[*p]
                && matches!(self.guard_holds(action, &replay_state), Ok(true))
                && match self.fire(action, &replay_state) {
                    Ok(s) => {
                        let matches_recorded = s == reachable[*next_idx];
                        replay_state = s;
                        matches_recorded
                    }
                    Err(_) => false,
                };
            if !ok {
                replay_validated = false;
                break;
            }
            trace.push(TraceStep {
                action: action.name.clone(),
                state: self.display_state(&replay_state),
            });
        }
        // The violation itself must replay too.
        let violates =
            matches!(self.invariants_hold(&replay_state), Ok(Err(ref i)) if *i == invariant);
        FiniteError::Falsified {
            invariant,
            trace,
            replay_validated: replay_validated && violates,
        }
    }
}

pub(crate) fn collect_state_idents(t: &Tx, m: &FiniteMachine, out: &mut Vec<String>) {
    match t {
        Tx::Ident(id) => {
            if m.var_index(id).is_some() {
                out.push(id.clone());
            }
        }
        Tx::FnAccess(f, i) => {
            if m.var_index(f).is_some() {
                out.push(f.clone());
            }
            collect_state_idents(i, m, out);
        }
        Tx::Except { base, index, value } => {
            out.push(base.clone());
            collect_state_idents(index, m, out);
            collect_state_idents(value, m, out);
        }
        Tx::Num(_) | Tx::BoolLit(_) | Tx::Prime(_) | Tx::Unchanged(_) => {}
        Tx::Add(a, b)
        | Tx::Sub(a, b)
        | Tx::Eq(a, b)
        | Tx::Neq(a, b)
        | Tx::Le(a, b)
        | Tx::Lt(a, b)
        | Tx::Ge(a, b)
        | Tx::Gt(a, b)
        | Tx::And(a, b)
        | Tx::Or(a, b)
        | Tx::Iff(a, b) => {
            collect_state_idents(a, m, out);
            collect_state_idents(b, m, out);
        }
        Tx::Not(a) => collect_state_idents(a, m, out),
        Tx::Ite(c, x, y) => {
            collect_state_idents(c, m, out);
            collect_state_idents(x, m, out);
            collect_state_idents(y, m, out);
        }
        Tx::Comprehension { lo, hi, body, .. } | Tx::Forall { lo, hi, body, .. } => {
            collect_state_idents(lo, m, out);
            collect_state_idents(hi, m, out);
            collect_state_idents(body, m, out);
        }
    }
}

/// Parse a variable sort: `Int` / `Nat` (scalar) or `[lo..hi -> BOOLEAN]`
/// (Tier-0 function shape), with `CONSTANT` names allowed as bounds.
fn parse_sort(sort: &str, consts: &BTreeMap<String, i64>) -> Option<VarKind> {
    let s = sort.trim();
    if s == "Int" || s == "Nat" {
        return Some(VarKind::Scalar);
    }
    let inner = s.strip_prefix('[')?.strip_suffix(']')?;
    let (dom, range) = inner.split_once("->")?;
    if range.trim() != "BOOLEAN" {
        return None;
    }
    let (lo, hi) = dom.trim().split_once("..")?;
    let resolve = |x: &str| -> Option<i64> {
        let x = x.trim();
        x.parse::<i64>().ok().or_else(|| consts.get(x).copied())
    };
    let (lo, hi) = (resolve(lo)?, resolve(hi)?);
    // Domain keys become Nat literals in the encoding; negative keys are
    // outside the fragment.
    if lo < 0 {
        return None;
    }
    Some(VarKind::FnBool { lo, hi })
}
