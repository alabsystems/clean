// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
impl State<'_> {
    pub(super) fn roots<O: ExecutionObserver>(
        &mut self,
        b: &NativeVerificationBundle,
        id: NativeRequestId,
        roots: &[ProofLineageId],
        w: &mut Work<'_, '_, O>,
    ) -> R {
        let mut at = 0;
        while let Some(root) = w.at(roots, at)? {
            if Self::prior(roots, at, root, w)? {
                self.fixed(
                    || E::DuplicateRequestLineageRoot {
                        request: id,
                        root: *root,
                    },
                    w,
                )?;
            }
            if !Self::member(&b.lineage.roots, root, w)? {
                self.fixed(
                    || E::UnknownLineageRoot {
                        request: id,
                        root: *root,
                    },
                    w,
                )?;
            }
            if let Some(node) = Self::last(&b.lineage.nodes, root, w)? {
                w.admit(34, 2 * size_of::<ProofDigest>() + size_of::<bool>())?;
                if node.target_module != b.trust_ir_module_digest {
                    self.fixed(
                        || E::RequestLineageRootTargetMismatch {
                            request: id,
                            root: *root,
                            expected: b.trust_ir_module_digest,
                            actual: node.target_module,
                        },
                        w,
                    )?;
                }
            }
            w.next(&mut at)?;
        }
        Ok(())
    }
    fn prior<O: ExecutionObserver>(
        rows: &[ProofLineageId],
        end: usize,
        id: &ProofLineageId,
        w: &mut Work<'_, '_, O>,
    ) -> R<bool> {
        let mut at = 0;
        loop {
            w.admit(1, size_of::<bool>())?;
            if at == end {
                return Ok(false);
            }
            let row = w.at(rows, at)?.ok_or(ObservedValueError::InvalidRange)?;
            w.admit(1, 2 * size_of::<ProofLineageId>() + size_of::<bool>())?;
            if row == id {
                return Ok(true);
            }
            w.next(&mut at)?;
        }
    }
    fn member<O: ExecutionObserver>(
        rows: &[ProofLineageId],
        id: &ProofLineageId,
        w: &mut Work<'_, '_, O>,
    ) -> R<bool> {
        let mut at = 0;
        while let Some(row) = w.at(rows, at)? {
            w.admit(1, 2 * size_of::<ProofLineageId>() + size_of::<bool>())?;
            if row == id {
                return Ok(true);
            }
            w.next(&mut at)?;
        }
        Ok(false)
    }
    fn last<'a, O: ExecutionObserver>(
        rows: &'a [ProofLineageNode],
        id: &ProofLineageId,
        w: &mut Work<'_, '_, O>,
    ) -> R<Option<&'a ProofLineageNode>> {
        w.admit(1, size_of::<usize>())?;
        let mut at = rows.len();
        loop {
            w.admit(1, size_of::<bool>())?;
            if at == 0 {
                return Ok(None);
            }
            w.admit(1, size_of::<usize>())?;
            at -= 1;
            let row = w.at(rows, at)?.ok_or(ObservedValueError::InvalidRange)?;
            w.admit(1, 2 * size_of::<ProofLineageId>() + size_of::<bool>())?;
            if row.id == *id {
                return Ok(Some(row));
            }
        }
    }
}
