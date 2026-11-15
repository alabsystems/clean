// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT
use super::*;
impl State {
    pub(super) fn binding<O: ExecutionObserver>(
        &mut self,
        value: &CertificateBinding,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        w.admit(8, size_of::<&CertificateBinding>())?;
        self.digest_bytes(&value.environment_digest, w)?;
        self.digest_bytes(&value.statement_digest, w)?;
        self.u8(u8::from(value.origin_module.is_some()), w)?;
        if let Some(digest) = &value.origin_module {
            self.digest_bytes(digest, w)?;
        }
        self.u8(u8::from(value.source.is_some()), w)?;
        if let Some(source) = &value.source {
            self.blob(source.decl.as_bytes(), w)?;
            self.digest_bytes(&source.closure_digest, w)?;
        }
        self.strings(&value.callees, w)?;
        // Historical island-free bindings have NO trailing absence byte.
        if let Some(island) = &value.environment {
            self.u8(1, w)?;
            self.blob(&island.declarations, w)?;
            self.digest_bytes(&island.digest, w)?;
        }
        Ok(())
    }
}
