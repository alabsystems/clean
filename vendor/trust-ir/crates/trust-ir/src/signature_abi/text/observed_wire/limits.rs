// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Ordinary encoding-limit Result data under the original observed writer.
use super::*;
use core::mem::{size_of, take};
mod budget;
#[cfg(test)]
mod tests;
type Reply = Result<String, String>;
impl SignatureAbi {
    /// Consume either complete returned DATA payload even after a sticky stop.
    /// The same original session records all headers/capacity; no new grant.
    pub fn retire_encoding_result_observed<O: ExecutionObserver>(
        value: Result<String, String>,
        s: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R {
        s.retirement_record(site, 1, size_of::<Reply>());
        let text = match value {
            Ok(text) | Err(text) => text,
        };
        s.retirement_record(site, 1, size_of::<String>());
        s.retirement_record(site, 1, text.capacity());
        drop(text);
        s.retirement_poll(site);
        s.admit(ExecutionProgress {
            phase: ExecutionPhase::Publication,
            site,
            work: 0,
            copy_bytes: 0,
        })
        .map_err(Into::into)
    }

    /// Exact ordinary encoding-limit diagnostics or the canonical wire text.
    /// Cancellation, allocation/arithmetic failures and unexpected codec/typed
    /// reader inconsistencies remain OUTER operational refusal, never a limit
    /// diagnostic or accepting fallback. This is DATA only, not ABI truth.
    pub fn canonical_text_encoding_result_observed<O: ExecutionObserver>(
        &self,
        s: &mut ObservedSession<'_, O>,
        site: ExecutionSite,
    ) -> R<Reply> {
        let mut out = Writer::new(s, site)?;
        out.admit(1, size_of::<Option<Reply>>() + size_of::<Reply>())?;
        let mut pending = None;
        let result = produce(self, &mut pending, &mut out);
        finish(&mut pending, result, &mut out)
    }
}
fn finish<O: ExecutionObserver>(
    pending: &mut Option<Reply>,
    result: R,
    out: &mut Writer<'_, '_, O>,
) -> R<Reply> {
    retire_text(take(&mut out.text), out);
    let result = result.and_then(|()| {
        out.admit(1, size_of::<Option<Reply>>() + size_of::<Reply>())?;
        if pending.is_none() {
            return Err(ObservedValueError::InvalidRange);
        }
        out.publication()
    });
    match result {
        Ok(()) => pending.take().ok_or(ObservedValueError::InvalidRange),
        Err(error) => {
            retire_pending(pending, out);
            Err(error)
        }
    }
}

fn produce<O: ExecutionObserver>(
    a: &SignatureAbi,
    pending: &mut Option<Reply>,
    out: &mut Writer<'_, '_, O>,
) -> R {
    if let Some(message) = budget::identity(a, out)? {
        return diagnostic(message, pending, out);
    }
    if let Some(message) = budget::nodes(a, out)? {
        return diagnostic(message, pending, out);
    }
    match encode::signature(a, out) {
        Ok(()) => {}
        // encode::signature only uses Writer's safe fixed formatting/append
        // operations. Their ONLY UnsupportedValue arm is the actual checked
        // canonical text byte limit in append_to; admission, allocation,
        // arithmetic and impossible UTF8 errors retain their distinct types.
        Err(ObservedValueError::UnsupportedValue) => {
            retire_text(take(&mut out.text), out);
            return diagnostic("ABI text exceeds byte limit", pending, out);
        }
        Err(error) => return Err(error),
    }
    // This is the existing complete bounded parser, typed-shape validator and
    // canonical reencoder. Never reinterpret any error from this phase as
    // a known size diagnosis or trust a failed round trip.
    let text = round_trip(out)?;
    *pending = Some(Ok(text));
    Ok(())
}
fn diagnostic<O: ExecutionObserver>(
    message: &'static str,
    pending: &mut Option<Reply>,
    out: &mut Writer<'_, '_, O>,
) -> R {
    let text = out.copy(message)?;
    *pending = Some(Err(text));
    Ok(())
}
fn retire_text<O: ExecutionObserver>(text: String, out: &mut Writer<'_, '_, O>) {
    out.session
        .retirement_record(out.site, 1, size_of::<String>());
    out.session.retirement_record(out.site, 1, text.capacity());
    drop(text);
    out.session.retirement_poll(out.site);
}
fn retire_pending<O: ExecutionObserver>(pending: &mut Option<Reply>, out: &mut Writer<'_, '_, O>) {
    out.session
        .retirement_record(out.site, 1, size_of::<Option<Reply>>());
    if let Some(Ok(text) | Err(text)) = pending.take() {
        retire_text(text, out);
    }
    out.session.retirement_poll(out.site);
}
