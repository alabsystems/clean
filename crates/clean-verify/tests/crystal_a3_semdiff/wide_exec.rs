// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **E2 for the W1 wide chains** — trust-ir's reference interpreter over the
//! committed emitted bodies, generalized past the single-enum-argument shape
//! `trust_exec.rs` was built for.
//!
//! Three generalizations, each forced by a specific fixture:
//!
//! * **Multi-fixture modules.** `has_loose_bvars` calls `@func.3657` — its
//!   callee is a SEPARATE committed fixture (`loose_bvar_range_callee`), so the
//!   composed module carries both bodies. trust-ir's parser assigns function
//!   ids SEQUENTIALLY (`parse_module`, `func_idx`), so the callee's id is
//!   reassigned to the id the call names after parsing — the call operand is
//!   the fixture's text, never rewritten.
//! * **Direct argument passing.** `execute_function` accepts constructed
//!   `InterpretValue`s, so bodies that take their arguments BY VALUE (ints,
//!   one-field structs, unit) need no harness at all — the reported step count
//!   is the subject's own with nothing subtracted. Only the two
//!   pointer-receiving bodies (`strict_monads`, `simp_priority_value`) get a
//!   per-input TEXT harness that allocas, stores, and calls, with the
//!   harness's own straight-line instruction count subtracted.
//! * **Reconstructed signatures.** The crate-level dumps name signatures by
//!   assembled index (`functy.467`) but carry no functy table; it is
//!   reconstituted here per chain, exactly as `trust_exec::build_module` does
//!   for its one subject.
//!
//! A fault anywhere — parse, layout, execution — is a first-class
//! `RunResult::Fault` (or a build error the caller records), never a panic in
//! a lane the chain has declared MAY REFUSE: the interpreter is a bounded
//! subset, and "trust-ir refused where Clean answered" is a finding to print,
//! not a crash.

use clean_verify::ir_semdiff::RunResult;
use trust_ir::interpret::{InterpretValue, InterpretValueKind, Interpreter};
use trust_ir::ty::{FuncTy, Ty};
use trust_ir::value::{FuncId, StructId};
use trust_ir::{Function, Module};

/// One function signature to reconstitute: `(functy index, params, returns)`.
pub type SigSpec = (u32, Vec<Ty>, Vec<Ty>);

/// The name every subject is renamed to (trust-ir's parser cannot read `::`
/// or `{…}` suffixes in a function name — the defect `trust_exec.rs` found).
pub const SUBJECT: &str = "g2_wide_subject";

/// The name a companion (callee) fixture is renamed to.
pub const COMPANION: &str = "g2_wide_companion";

/// The name of the per-input text harness, when one exists.
pub const HARNESS: &str = "g2_wide_harness";

/// Compose and parse the module for one wide chain (plus an optional per-input
/// harness), reconstitute its functy table, and reassign function ids.
///
/// `fixtures` are `(fixture text, original printed name)` pairs, subject
/// first. `func_ids[i]` is the id fixture `i`'s function must carry so that
/// call operands in the committed text resolve to it.
pub fn build_wide_module(
    fixtures: &[(String, &str)],
    type_decls: &str,
    func_ids: &[u32],
    sigs: &[SigSpec],
    harness_text: Option<&str>,
) -> Result<Module, String> {
    let mut bodies = Vec::new();
    for (i, (text, original)) in fixtures.iter().enumerate() {
        let fresh = if i == 0 {
            format!("@{SUBJECT}")
        } else {
            format!("@{COMPANION}{i}")
        };
        if !text.contains(original) {
            return Err(format!("fixture {i} does not contain `{original}`"));
        }
        bodies.push(text.replace(original, &fresh));
    }
    let mut text =
        format!("; TrustIr text format v1\nmodule \"crystal_a3_wide\"\n\n{type_decls}\n");
    for body in &bodies {
        text.push_str("\n\n");
        text.push_str(body);
    }
    if let Some(h) = harness_text {
        text.push_str("\n\n");
        text.push_str(h);
    }
    let mut module = trust_ir::parser::parse_module(&text)
        .map_err(|e| format!("trust-ir parser rejected the composed module: {e}"))?;
    let expected = fixtures.len() + usize::from(harness_text.is_some());
    if module.functions.len() != expected {
        return Err(format!(
            "expected {expected} functions in the composed module, got {}",
            module.functions.len()
        ));
    }
    // The parser assigned ids sequentially; give each fixture's function the id
    // the committed call operands name. The harness (last, when present) keeps
    // an id far above anything a single-body fixture uses.
    for (i, id) in func_ids.iter().enumerate() {
        module.functions[i].id = FuncId::new(*id);
    }
    if harness_text.is_some() {
        module.functions[fixtures.len()].id = FuncId::new(0x000f_fffe);
    }
    // Reconstitute the functy table at the declared indices.
    let max_slot = sigs.iter().map(|(i, _, _)| *i).max().unwrap_or(0) as usize;
    let placeholder = FuncTy {
        params: Vec::new(),
        returns: Vec::new(),
        is_vararg: false,
    };
    module.func_types = vec![placeholder; max_slot + 1];
    for (idx, params, returns) in sigs {
        module.func_types[*idx as usize] = FuncTy {
            params: params.clone(),
            returns: returns.clone(),
            is_vararg: false,
        };
    }
    Ok(module)
}

/// The function E2 executes for a given run: the harness when one was
/// composed, the subject otherwise.
pub fn wide_target(module: &Module, harness: bool) -> Result<&Function, String> {
    let name = if harness { HARNESS } else { SUBJECT };
    module
        .functions
        .iter()
        .find(|f| f.name == name)
        .ok_or_else(|| format!("no `{name}` in the composed module"))
}

/// Run one input and map the outcome into the differential's vocabulary.
///
/// `overhead` is the harness's own straight-line instruction count (0 for
/// direct-argument runs), subtracted so the reported step count is the SUBJECT
/// body's alone — counted from the harness text, never tuned.
pub fn run_wide(
    module: &Module,
    target: &Function,
    args: Vec<InterpretValue>,
    overhead: u64,
) -> (RunResult, Option<u32>) {
    let interp = Interpreter::with_module(module);
    match interp.execute_function(target, args) {
        Ok(outcome) => {
            let steps = u32::try_from(outcome.steps.saturating_sub(overhead)).ok();
            (map_returns(&outcome.returns), steps)
        }
        Err(e) => (RunResult::Fault(e.code.as_str().to_owned()), None),
    }
}

/// Map an interpreter return list to a [`RunResult`].
///
/// A void return is [`RunResult::Unit`] — a first-class answer, because
/// `strict_monads` genuinely returns nothing. A one-field aggregate is
/// projected to its field, mirroring how the Clean side declares the
/// `AggInt` encoding per chain rather than guessing. A MULTI-VALUE return is
/// [`RunResult::Many`] of the elements in order — the W3 overflow lane's
/// six-value `ret` — unless any element fails to map, in which case the whole
/// list is a fault (a partially-mapped return compared element-wise would be
/// a vocabulary lie).
fn map_returns(returns: &[InterpretValue]) -> RunResult {
    match returns {
        [] => RunResult::Unit,
        [v] => map_value(v),
        _ => {
            let mapped: Vec<RunResult> = returns.iter().map(map_value).collect();
            if let Some(bad) = mapped.iter().find(|r| matches!(r, RunResult::Fault(_))) {
                return RunResult::Fault(format!("multi_return_element:{bad}"));
            }
            RunResult::Many(mapped)
        }
    }
}

fn map_value(v: &InterpretValue) -> RunResult {
    match &v.kind {
        InterpretValueKind::Bool(b) => RunResult::Bool(*b),
        InterpretValueKind::Int(i) => match u64::try_from(i.as_unsigned()) {
            Ok(n) => RunResult::Int(n),
            Err(_) => RunResult::Fault("int_too_wide".to_owned()),
        },
        InterpretValueKind::Aggregate(fields) => match &fields[..] {
            [field] => map_value(field),
            _ => RunResult::Fault(format!("aggregate_arity:{}", fields.len())),
        },
        InterpretValueKind::Unit => RunResult::Unit,
        // A float travels as its BIT PATTERN on both sides (the float-residue
        // lane): no host round-trip, so NaN payloads and signed zeros compare
        // exactly.
        InterpretValueKind::FloatBits(bits) => RunResult::Float(*bits),
        other => RunResult::Fault(format!("unmapped_value:{other:?}")),
    }
}

// ── argument constructors ─────────────────────────────────────────────────

/// A `u32` argument value.
pub fn iv_u32(n: u32) -> InterpretValue {
    InterpretValue::int(Ty::U32, i128::from(n)).expect("u32 is an integer type")
}

/// A `u64` argument value.
pub fn iv_u64(n: u64) -> InterpretValue {
    InterpretValue::int(Ty::U64, i128::from(n)).expect("u64 is an integer type")
}

/// The unit argument value (`()` — the discarded closure environment of
/// `get_char_val::{closure#0}`).
pub fn iv_unit() -> InterpretValue {
    InterpretValue {
        ty: Ty::Unit,
        kind: InterpretValueKind::Unit,
    }
}

/// A by-value ONE-FIELD struct argument (`FlatFlags`, `ExprMeta`, `NodeId`).
pub fn iv_struct1(struct_id: u32, field: InterpretValue) -> InterpretValue {
    InterpretValue {
        ty: Ty::Struct(StructId::new(struct_id)),
        kind: InterpretValueKind::Aggregate(vec![field]),
    }
}
