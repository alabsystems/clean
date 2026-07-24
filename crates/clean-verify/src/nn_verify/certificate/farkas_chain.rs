// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Certificate chaining for Farkas certificates (T70 at the Farkas level).
//!
//! If cert1 proves A => B and cert2 proves B => C, `chain_farkas_certs`
//! produces a certificate proving A => C by composing the multiplier
//! blocks through the intermediate constraint layer.

use super::farkas_bridge::{
    verify_farkas_certificate, ExternalFarkasCert, FarkasBridgeError, FarkasVerifyResult,
};

/// Tolerance for floating-point comparisons.
const EPSILON: f64 = 1e-9;

/// Chain Farkas certificates: if cert1 proves A => B and cert2 proves B => C,
/// produce a certificate proving A => C (implements T70).
///
/// The chained certificate uses cert1's input constraints and cert2's output
/// constraints. The multipliers are composed through the intermediate layer.
///
/// # Errors
///
/// Returns `FarkasBridgeError::InterfaceMismatch` if cert1's output constraints
/// do not match cert2's input constraints (structurally and dimensionally).
pub fn chain_farkas_certs(
    cert1: &ExternalFarkasCert,
    cert2: &ExternalFarkasCert,
) -> Result<ExternalFarkasCert, FarkasBridgeError> {
    // Verify both certificates first.
    let r1 = verify_farkas_certificate(cert1);
    if r1 != FarkasVerifyResult::Valid {
        return Err(FarkasBridgeError::InvalidCertificate(format!(
            "cert1 verification failed: {r1:?}"
        )));
    }
    let r2 = verify_farkas_certificate(cert2);
    if r2 != FarkasVerifyResult::Valid {
        return Err(FarkasBridgeError::InvalidCertificate(format!(
            "cert2 verification failed: {r2:?}"
        )));
    }

    // Check interface compatibility: cert1.output must match cert2.input.
    if cert1.output_dim != cert2.input_dim {
        return Err(FarkasBridgeError::DimensionMismatch {
            expected: cert1.output_dim,
            got: cert2.input_dim,
        });
    }
    if cert1.output_matrix.len() != cert2.input_matrix.len() {
        return Err(FarkasBridgeError::InterfaceMismatch);
    }
    if cert1.output_bounds.len() != cert2.input_bounds.len() {
        return Err(FarkasBridgeError::InterfaceMismatch);
    }

    verify_interface_match(cert1, cert2)?;
    let composed_multipliers = compose_multipliers(cert1, cert2);

    Ok(ExternalFarkasCert {
        multipliers: composed_multipliers,
        input_matrix: cert1.input_matrix.clone(),
        input_bounds: cert1.input_bounds.clone(),
        output_matrix: cert2.output_matrix.clone(),
        output_bounds: cert2.output_bounds.clone(),
        input_dim: cert1.input_dim,
        output_dim: cert2.output_dim,
    })
}

/// Verify that cert1's output constraints structurally match cert2's input.
fn verify_interface_match(
    cert1: &ExternalFarkasCert,
    cert2: &ExternalFarkasCert,
) -> Result<(), FarkasBridgeError> {
    for (i, (out_row, in_row)) in cert1
        .output_matrix
        .iter()
        .zip(cert2.input_matrix.iter())
        .enumerate()
    {
        if out_row.len() != in_row.len() {
            return Err(FarkasBridgeError::InterfaceMismatch);
        }
        for (&o, &inp) in out_row.iter().zip(in_row.iter()) {
            if (o - inp).abs() > EPSILON {
                return Err(FarkasBridgeError::InterfaceMismatch);
            }
        }
        if (cert1.output_bounds[i] - cert2.input_bounds[i]).abs() > EPSILON {
            return Err(FarkasBridgeError::InterfaceMismatch);
        }
    }
    Ok(())
}

/// Compose multipliers through the intermediate constraint layer.
///
/// Both certs have block structure: block_size = num_input_rows / num_output_rows.
/// For cert1: block j weights cert1 input rows to produce cert1 output row j.
/// For cert2: block k weights intermediate rows to produce cert2 output row k.
/// The composed multipliers weight cert1 input rows to produce cert2 output rows.
fn compose_multipliers(cert1: &ExternalFarkasCert, cert2: &ExternalFarkasCert) -> Vec<f64> {
    let cert1_num_out = cert1.output_matrix.len();
    let cert2_num_out = cert2.output_matrix.len();

    // Guard: empty output constraints means no intermediate layer to compose
    // through. The composed cert's output is cert2's output and input is cert1's
    // input. For the result to pass verification:
    //   - If cert2 has no output rows, multipliers must be empty.
    //   - If cert1 has no output rows (empty intermediate), cert2's input is also
    //     empty (checked above), so there is nothing to compose through. Return
    //     zero-filled multipliers sized to cert1's input if cert2 has output, or
    //     empty if cert2 also has no output.
    if cert1_num_out == 0 || cert2_num_out == 0 {
        // Result output is cert2's output. If empty, verification requires
        // empty multipliers. If non-empty, we need cert1.input_matrix.len()
        // multipliers but they are all zero (no intermediate contribution).
        return if cert2_num_out == 0 {
            vec![]
        } else {
            vec![0.0_f64; cert1.input_matrix.len()]
        };
    }

    let cert1_block_size = cert1.input_matrix.len() / cert1_num_out;
    let cert2_block_size = cert2.input_matrix.len() / cert2_num_out;

    let mut composed = vec![0.0_f64; cert1.input_matrix.len()];

    for k in 0..cert2_num_out {
        for local_j in 0..cert2_block_size {
            let j = k * cert2_block_size + local_j;
            let cert2_w = cert2.multipliers[j];

            // Intermediate row j comes from cert1 block j.
            // cert1 block j spans input rows [j*cert1_block_size .. (j+1)*cert1_block_size).
            for local_i in 0..cert1_block_size {
                let i = j * cert1_block_size + local_i;
                if i < composed.len() {
                    composed[i] += cert2_w * cert1.multipliers[i];
                }
            }
        }
    }

    composed
}
