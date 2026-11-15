// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
pub(super) fn observed_write_func_ty<O: ExecutionObserver>(
    buf: &mut Output<'_, '_, O>,
    pool: &SealedPool,
    signature: usize,
    ft: &FuncTyG<NoExt>,
) -> R {
    observed_write_count(buf, "FuncTy.params", ft.params.len())?;
    for ty in &ft.params {
        buf.poll()?;
        observed_write_ty(buf, pool, ty)?;
    }
    observed_write_count(buf, "FuncTy.returns", ft.returns.len())?;
    for ty in &ft.returns {
        buf.poll()?;
        observed_write_ty(buf, pool, ty)?;
    }
    observed_write_bool(buf, ft.is_vararg)?;
    if pool.minimum_version() >= SIGNATURE_ABI_FORMAT_VERSION {
        observed_write_bool(buf, ft.abi.is_some())?;
        if let Some(abi) = &ft.abi {
            match buf.abi_result(abi)? {
                Ok(text) => {
                    let written = observed_write_raw_str(buf, &text);
                    buf.retire(text);
                    written?;
                    buf.poll()?;
                }
                Err(detail) => {
                    buf.refuse_owned(WireRefusal::SignatureAbi { signature, detail })?;
                }
            }
        }
    }
    Ok(())
}

pub(super) fn observed_write_proof_annotation_list<O: ExecutionObserver>(
    buf: &mut Output<'_, '_, O>,
    pool: &SealedPool,
    proofs: &[ProofAnnotation],
) -> R {
    let mut retained = 0usize;
    for proof in proofs {
        buf.poll()?;
        #[cfg(feature = "clean-expr")]
        if matches!(proof, ProofAnnotation::Goal(_)) {
            continue;
        }
        let _ = proof;
        retained = retained
            .checked_add(1)
            .ok_or(ObservedValueError::CapacityOverflow)?;
    }
    observed_write_count(buf, "proof annotation list", retained)?;
    for proof in proofs {
        buf.poll()?;
        #[cfg(feature = "clean-expr")]
        if matches!(proof, ProofAnnotation::Goal(_)) {
            continue;
        }
        observed_write_proof_annotation(buf, pool, proof)?;
    }
    Ok(())
}
