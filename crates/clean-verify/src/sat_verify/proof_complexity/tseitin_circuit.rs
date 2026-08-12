// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tseitin Circuit-to-CNF Transformation
//!
//! Convert Boolean circuits (DAGs of AND/OR/NOT/XOR/IMPLIES gates) to
//! equisatisfiable CNF via the Tseitin (1968) transformation. Introduces
//! one auxiliary variable per gate and O(1) clauses per gate.

use crate::sat_verify::cdcl::Clause;

// ---------------------------------------------------------------------------
// Circuit types
// ---------------------------------------------------------------------------

/// Boolean gate types for circuit representation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum GateType {
    AndType,
    Or,
    Not,
    Xor,
    Implies,
}

/// A gate in a Boolean circuit.
#[derive(Debug, Clone)]
pub struct Gate {
    pub gate_type: GateType,
    /// Input wire indices. For binary gates: 2 inputs. For NOT: 1 input.
    /// Wire 1..=num_inputs are circuit inputs; higher indices are gate outputs.
    pub inputs: Vec<u32>,
    /// Output variable index (assigned during Tseitin transform).
    pub output: Option<u32>,
}

/// A Boolean circuit as a DAG of gates.
#[derive(Debug, Clone)]
pub struct Circuit {
    /// Number of input variables.
    pub num_inputs: u32,
    /// Gates in topological order.
    pub gates: Vec<Gate>,
}

/// Result of Tseitin transformation.
#[derive(Debug, Clone)]
pub struct TseitinResult {
    /// CNF clauses (equisatisfiable with original circuit).
    pub clauses: Vec<Clause>,
    /// Total number of variables (inputs + auxiliary).
    pub num_vars: u32,
    /// Output variable index (the circuit's output gate).
    pub output_var: u32,
}

// ---------------------------------------------------------------------------
// Tseitin transform
// ---------------------------------------------------------------------------

/// Perform Tseitin transformation on a circuit.
///
/// Introduces a fresh variable for each gate output and adds clauses
/// enforcing gate semantics. The output variable of the last gate
/// is asserted true (unit clause).
///
/// Gate encodings (z = gate output, x/y = inputs):
/// - AND(x,y)=z: (NOT z OR x), (NOT z OR y), (NOT x OR NOT y OR z)
/// - OR(x,y)=z:  (NOT x OR z), (NOT y OR z), (NOT z OR x OR y)
/// - NOT(x)=z:   (NOT x OR NOT z), (x OR z)
/// - XOR(x,y)=z: 4 clauses encoding parity
/// - IMPLIES(x,y)=z: equivalent to OR(NOT x, y)=z
#[must_use]
pub fn tseitin_transform(circuit: &Circuit) -> TseitinResult {
    let mut next_var = circuit.num_inputs + 1;
    let mut clauses = Vec::new();
    let mut gate_outputs = Vec::with_capacity(circuit.gates.len());

    for gate in &circuit.gates {
        let z = next_var as i32;
        gate_outputs.push(next_var);
        next_var += 1;

        let inputs: Vec<i32> = gate.inputs.iter().map(|&w| w as i32).collect();

        match gate.gate_type {
            GateType::AndType => {
                let x = inputs[0];
                let y = inputs[1];
                clauses.push(vec![-z, x]);
                clauses.push(vec![-z, y]);
                clauses.push(vec![-x, -y, z]);
            }
            GateType::Or => {
                let x = inputs[0];
                let y = inputs[1];
                clauses.push(vec![-x, z]);
                clauses.push(vec![-y, z]);
                clauses.push(vec![-z, x, y]);
            }
            GateType::Not => {
                let x = inputs[0];
                clauses.push(vec![-x, -z]);
                clauses.push(vec![x, z]);
            }
            GateType::Xor => {
                let x = inputs[0];
                let y = inputs[1];
                clauses.push(vec![-x, -y, -z]);
                clauses.push(vec![x, y, -z]);
                clauses.push(vec![x, -y, z]);
                clauses.push(vec![-x, y, z]);
            }
            GateType::Implies => {
                let x = inputs[0];
                let y = inputs[1];
                clauses.push(vec![x, z]);
                clauses.push(vec![-y, z]);
                clauses.push(vec![-z, -x, y]);
            }
        }
    }

    let output_var = *gate_outputs.last().unwrap_or(&1);
    clauses.push(vec![output_var as i32]);

    TseitinResult {
        clauses,
        num_vars: next_var - 1,
        output_var,
    }
}

/// Evaluate a circuit under a given input assignment.
#[must_use]
pub fn evaluate_circuit(circuit: &Circuit, input_assignment: &[bool]) -> Option<bool> {
    if circuit.gates.is_empty() {
        return None;
    }

    let total_wires = circuit.num_inputs as usize + circuit.gates.len();
    let mut wire_val = vec![false; total_wires + 1];

    for (i, &val) in input_assignment.iter().enumerate() {
        if i < circuit.num_inputs as usize {
            wire_val[i + 1] = val;
        }
    }

    for (g_idx, gate) in circuit.gates.iter().enumerate() {
        let out_idx = circuit.num_inputs as usize + 1 + g_idx;
        let get_wire = |w: u32| -> bool { wire_val[w as usize] };

        let result = match gate.gate_type {
            GateType::AndType => get_wire(gate.inputs[0]) && get_wire(gate.inputs[1]),
            GateType::Or => get_wire(gate.inputs[0]) || get_wire(gate.inputs[1]),
            GateType::Not => !get_wire(gate.inputs[0]),
            GateType::Xor => get_wire(gate.inputs[0]) ^ get_wire(gate.inputs[1]),
            GateType::Implies => !get_wire(gate.inputs[0]) || get_wire(gate.inputs[1]),
        };
        wire_val[out_idx] = result;
    }

    let last_idx = circuit.num_inputs as usize + circuit.gates.len();
    Some(wire_val[last_idx])
}

/// Verify Tseitin equisatisfiability for a given input assignment.
#[must_use]
pub fn verify_tseitin_equisat(
    circuit: &Circuit,
    tseitin: &TseitinResult,
    input_assignment: &[bool],
) -> bool {
    let total_wires = circuit.num_inputs as usize + circuit.gates.len();
    let mut wire_val = vec![false; total_wires + 1];

    for (i, &val) in input_assignment.iter().enumerate() {
        if i < circuit.num_inputs as usize {
            wire_val[i + 1] = val;
        }
    }

    for (g_idx, gate) in circuit.gates.iter().enumerate() {
        let out_idx = circuit.num_inputs as usize + 1 + g_idx;
        let get_wire = |w: u32| -> bool { wire_val[w as usize] };

        let result = match gate.gate_type {
            GateType::AndType => get_wire(gate.inputs[0]) && get_wire(gate.inputs[1]),
            GateType::Or => get_wire(gate.inputs[0]) || get_wire(gate.inputs[1]),
            GateType::Not => !get_wire(gate.inputs[0]),
            GateType::Xor => get_wire(gate.inputs[0]) ^ get_wire(gate.inputs[1]),
            GateType::Implies => !get_wire(gate.inputs[0]) || get_wire(gate.inputs[1]),
        };
        wire_val[out_idx] = result;
    }

    let assignment: Vec<bool> = (1..=tseitin.num_vars as usize)
        .map(|i| if i <= total_wires { wire_val[i] } else { false })
        .collect();

    for clause in &tseitin.clauses {
        let satisfied = clause.iter().any(|&lit| {
            let var_idx = lit.unsigned_abs() as usize;
            let val = assignment.get(var_idx - 1).copied().unwrap_or(false);
            if lit > 0 {
                val
            } else {
                !val
            }
        });
        if !satisfied {
            return false;
        }
    }

    true
}
