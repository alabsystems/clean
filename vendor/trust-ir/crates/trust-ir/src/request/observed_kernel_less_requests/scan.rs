// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
#[derive(Clone, Copy)]
pub(super) enum Group {
    Metadata,
    Source,
    Certificates,
    VcShape,
    Mode,
    Collisions,
}
impl State {
    pub(super) fn run<O: ExecutionObserver>(
        &mut self,
        b: &NativeVerificationBundle,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        self.setup(b, w)?;
        let mut index = 0;
        while let Some(request) = w.at(&b.requests, index)? {
            self.child(b, index, Group::Metadata, w)?;
            self.child(b, index, Group::Source, w)?;
            self.child(b, index, Group::Certificates, w)?;
            w.admit(1, size_of::<Option<&TrustVcNativeRequest>>())?;
            match request {
                NativeVerificationRequest::TrustVc(r) => {
                    self.child(b, index, Group::VcShape, w)?;
                    self.vc(b, r, w)?;
                }
                NativeVerificationRequest::TrustMc(_) | NativeVerificationRequest::TrustWp(_) => {
                    self.child(b, index, Group::Mode, w)?;
                }
            }
            w.next(&mut index)?;
        }
        self.child(b, index, Group::Collisions, w)
    }
    pub(super) fn child<O: ExecutionObserver>(
        &mut self,
        b: &NativeVerificationBundle,
        index: usize,
        group: Group,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        self.prepare(w)?;
        w.admit(8, size_of::<Group>() + size_of::<usize>())?;
        let rows = match group {
            Group::Metadata => b.request_metadata_errors_observed(index, w.session, w.site)?,
            Group::Source => {
                let request = w
                    .at(&b.requests, index)?
                    .ok_or(ObservedValueError::InvalidRange)?;
                b.request_source_errors_observed(request, w.session, w.site)?
            }
            Group::Certificates => {
                b.request_certificate_errors_observed(index, w.session, w.site)?
            }
            Group::VcShape => b.request_vc_shape_errors_observed(index, w.session, w.site)?,
            Group::Mode => match w
                .at(&b.requests, index)?
                .ok_or(ObservedValueError::InvalidRange)?
            {
                NativeVerificationRequest::TrustMc(r) => {
                    r.mode_errors_observed(w.session, w.site)?
                }
                NativeVerificationRequest::TrustWp(r) => {
                    r.mode_errors_observed(w.session, w.site)?
                }
                NativeVerificationRequest::TrustVc(_) => {
                    return Err(ObservedValueError::InvalidRange);
                }
            },
            Group::Collisions => b.trust_vc_mode_collision_errors_observed(w.session, w.site)?,
        };
        self.capture(rows);
        self.flush(w)
    }
}
