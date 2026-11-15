// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
impl State {
    pub(super) fn references<O: ExecutionObserver>(
        &mut self,
        bundle: &NativeVerificationBundle,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        let mut at = 0;
        while let Some(function) = w.at(&bundle.module.functions, at)? {
            w.admit(1, size_of::<bool>())?;
            if matches!(&function.producer, Some(Producer::TRust)) {
                self.blocks(function, w)?;
            }
            w.next(&mut at)?;
        }
        Ok(())
    }
    fn blocks<O: ExecutionObserver>(&mut self, function: &Function, w: &mut Work<'_, '_, O>) -> R {
        let mut at = 0;
        while let Some(block) = w.at(&function.blocks, at)? {
            self.nodes(function, block, w)?;
            w.next(&mut at)?;
        }
        Ok(())
    }
    fn nodes<O: ExecutionObserver>(
        &mut self,
        function: &Function,
        block: &Block,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        let mut index = 0;
        while let Some(node) = w.at(&block.body, index)? {
            // Inst::shape/InstShape::uses_borrow_permissions are exhaustive
            // fixed discriminant matches, with no operand/type traversal.
            w.admit(2, size_of::<bool>())?;
            if node.inst.uses_borrow_permissions() {
                self.location(function, block, index, w)?;
            }
            w.next(&mut index)?;
        }
        Ok(())
    }
    pub(super) fn location<O: ExecutionObserver>(
        &mut self,
        function: &Function,
        block: &Block,
        index: usize,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        w.text("function '", &mut self.text)?;
        w.text(&function.name, &mut self.text)?;
        w.text("' bb", &mut self.text)?;
        w.decimal(u128::from(block.id.index()), &mut self.text)?;
        w.text(" #", &mut self.text)?;
        w.decimal(index as u128, &mut self.text)?;
        w.admit(
            1,
            size_of::<E>() + size_of::<Option<E>>() + size_of::<String>(),
        )?;
        self.pending = Some(E::RustReferenceAsPermissionBorrow {
            location: take(&mut self.text),
        });
        self.emit(w)
    }
    pub(super) fn lineage<O: ExecutionObserver>(
        &mut self,
        bundle: &NativeVerificationBundle,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        w.admit(1, size_of::<Option<ProofDigest>>())?;
        // The original source_digest reads only the fixed adapter-input enum,
        // not provenance.source_digest. Preserve that exact distinction.
        if let Some(source) = bundle.source_digest()
            && !self.contains(bundle, source, Field::Source, w)?
        {
            w.admit(1, size_of::<E>() + size_of::<Option<E>>())?;
            self.pending = Some(E::SourceDigestNotInLineage(source));
            self.emit(w)?;
        }
        w.admit(1, size_of::<ProofDigest>())?;
        if !self.contains(bundle, bundle.trust_ir_module_digest, Field::Target, w)? {
            w.admit(1, size_of::<E>() + size_of::<Option<E>>())?;
            self.pending = Some(E::TrustIrDigestNotInLineage(bundle.trust_ir_module_digest));
            self.emit(w)?;
        }
        Ok(())
    }
    fn contains<O: ExecutionObserver>(
        &mut self,
        bundle: &NativeVerificationBundle,
        digest: ProofDigest,
        field: Field,
        w: &mut Work<'_, '_, O>,
    ) -> R<bool> {
        let mut at = 0;
        while let Some(node) = w.at(&bundle.lineage.nodes, at)? {
            w.admit(
                size_of::<ProofDigest>(),
                size_of::<ProofDigest>() + size_of::<bool>(),
            )?;
            let actual = match field {
                Field::Source => node.source_module,
                Field::Target => node.target_module,
            };
            if actual == digest {
                return Ok(true);
            }
            w.next(&mut at)?;
        }
        Ok(false)
    }
}
#[derive(Clone, Copy)]
enum Field {
    Source,
    Target,
}
