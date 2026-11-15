// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
use crate::inst::Inst;
use core::mem::size_of;

#[derive(Clone, Copy)]
pub(super) enum CountPolicy {
    IdentityTotal,
    RequireWireImage,
}

/// Fixed original source-provenance projection, never an admissibility flag.
#[derive(Clone, Copy)]
pub(super) enum FunctionSelection {
    Whole,
    SourceBody(usize),
}

enum State<'s> {
    Check(&'s mut Refusals),
    Count(usize),
    Hash {
        hasher: Sha256,
        expected: usize,
        written: usize,
    },
}

/// A sink, never an execution owner. Both wire passes borrow the SAME session.
pub(super) struct Output<'s, 'o, O: ExecutionObserver> {
    session: &'s mut ObservedSession<'o, O>,
    site: ExecutionSite,
    state: State<'s>,
    counts: CountPolicy,
    functions: FunctionSelection,
}

impl<'s, 'o, O: ExecutionObserver> Output<'s, 'o, O> {
    pub(super) fn counter(session: &'s mut ObservedSession<'o, O>, site: ExecutionSite) -> R<Self> {
        session.admit(ExecutionProgress {
            phase: ExecutionPhase::CanonicalSerialization,
            site,
            work: 1,
            copy_bytes: size_of::<Self>(),
        })?;
        Ok(Self {
            session,
            site,
            state: State::Count(0),
            counts: CountPolicy::IdentityTotal,
            functions: FunctionSelection::Whole,
        })
    }

    pub(super) fn checker(
        session: &'s mut ObservedSession<'o, O>,
        site: ExecutionSite,
        held: &'s mut Refusals,
    ) -> R<Self> {
        session.admit(ExecutionProgress {
            phase: ExecutionPhase::CanonicalSerialization,
            site,
            work: 1,
            copy_bytes: size_of::<Self>(),
        })?;
        Ok(Self {
            session,
            site,
            state: State::Check(held),
            counts: CountPolicy::IdentityTotal,
            functions: FunctionSelection::Whole,
        })
    }
    fn with_check<T>(&mut self, f: impl FnOnce(&mut Refusals, &mut Self) -> R<T>) -> R<T> {
        self.admit(1, size_of::<State<'s>>())?;
        let old = core::mem::replace(&mut self.state, State::Count(0));
        let State::Check(held) = old else {
            self.state = old;
            return Err(ObservedValueError::InvalidRange);
        };
        let result = f(held, self);
        self.state = State::Check(held);
        result
    }
    pub(super) fn take_refusals(&mut self) -> R<Vec<BinaryProjectionError>> {
        self.with_check(|held, out| held.transfer(out))
    }
    pub(super) fn record_retirement(&mut self, work: usize, bytes: usize) {
        self.session.retirement_record(self.site, work, bytes);
    }
    pub(super) fn request_site(&self) -> ExecutionSite {
        self.site
    }
    pub(super) fn session_mut(&mut self) -> &mut ObservedSession<'o, O> {
        self.session
    }
    pub(super) fn abi_result(
        &mut self,
        abi: &crate::signature_abi::SignatureAbi,
    ) -> R<Result<String, String>> {
        self.admit(
            1,
            size_of::<Result<String, String>>()
                + size_of::<WireRefusal>()
                + size_of::<Option<WireRefusal>>(),
        )?;
        if matches!(&self.state, State::Check(_)) {
            abi.canonical_text_encoding_result_observed(self.session, self.site)
        } else {
            self.abi_text(abi).map(Ok)
        }
    }

    pub(super) fn select_functions(&mut self, selection: FunctionSelection) -> R {
        self.admit(1, size_of::<FunctionSelection>())?;
        self.functions = selection;
        Ok(())
    }
    /// The returned slice borrows ONLY the immutable module, not this sink.
    /// Every lookup is admitted before reading the selected range.
    pub(super) fn functions<'m>(&mut self, module: &'m Module) -> R<&'m [FunctionG<NoExt>]> {
        self.admit(1, size_of::<&[FunctionG<NoExt>]>())?;
        match self.functions {
            FunctionSelection::Whole => Ok(&module.functions),
            FunctionSelection::SourceBody(index) => {
                let end = index
                    .checked_add(1)
                    .ok_or(ObservedValueError::CapacityOverflow)?;
                module
                    .functions
                    .get(index..end)
                    .ok_or(ObservedValueError::InvalidRange)
            }
        }
    }
    /// One common decision for collector AND writer, just like the ordinary
    /// clone/retain/clear source-provenance preimage. Whole keeps exact behavior.
    pub(super) fn provenance<'f>(
        &mut self,
        function: &'f FunctionG<NoExt>,
        canonical: Option<Canonical<'_>>,
        retain: bool,
    ) -> R<Option<&'f SourceProvenance>> {
        self.admit(3, size_of::<Option<&SourceProvenance>>())?;
        Ok(match self.functions {
            FunctionSelection::Whole => match canonical {
                None => function.source_provenance.as_ref(),
                Some(Canonical::Ordinary(plan)) => {
                    projected_source_provenance(function, Some(plan), retain)
                }
                Some(Canonical::Body(_)) if retain => function.source_provenance.as_ref(),
                // The body-only plan intentionally does not compute ordinary
                // non-reflexive provenance removal: executable v1 retains it.
                Some(Canonical::Body(_)) => return Err(ObservedValueError::UnsupportedValue),
            },
            FunctionSelection::SourceBody(_) => None,
        })
    }

    pub(super) fn require_wire_image(&mut self) {
        self.counts = CountPolicy::RequireWireImage;
    }

    pub(super) fn start_hash(&mut self, domain: &str, length: usize) -> R {
        self.admit(1, 0)?;
        let expected = b"trust-ir.sha256-domain.v1\0"
            .len()
            .checked_add(16)
            .and_then(|n| n.checked_add(domain.len()))
            .and_then(|n| n.checked_add(length))
            .ok_or(ObservedValueError::CapacityOverflow)?;
        self.state = State::Hash {
            hasher: Sha256::new(),
            expected,
            written: 0,
        };
        let domain_len =
            u64::try_from(domain.len()).map_err(|_| ObservedValueError::CapacityOverflow)?;
        let length = u64::try_from(length).map_err(|_| ObservedValueError::CapacityOverflow)?;
        self.extend_from_slice(b"trust-ir.sha256-domain.v1\0")?;
        self.extend_from_slice(&domain_len.to_be_bytes())?;
        self.extend_from_slice(domain.as_bytes())?;
        self.extend_from_slice(&length.to_be_bytes())
    }

    pub(super) fn admit(&mut self, work: usize, copy_bytes: usize) -> R {
        self.session
            .admit(ExecutionProgress {
                phase: ExecutionPhase::CanonicalSerialization,
                site: self.site,
                work,
                copy_bytes,
            })
            .map_err(Into::into)
    }
    pub(super) fn poll(&mut self) -> R {
        self.admit(1, 0)
    }
    /// Reborrow the caller's original session, never a replacement owner.
    pub(super) fn abi_text(&mut self, abi: &crate::signature_abi::SignatureAbi) -> R<String> {
        abi.canonical_text_for_wire_observed(self.session, self.site)
    }

    pub(super) fn retirement_poll(&mut self) {
        self.session.retirement_poll(self.site);
    }

    pub(super) fn extend_from_slice(&mut self, bytes: &[u8]) -> R {
        self.poll()?;
        if let State::Check(held) = &mut self.state {
            held.len = held.len.saturating_add(bytes.len());
            return Ok(());
        }
        if let State::Count(count) = &mut self.state {
            *count = count
                .checked_add(bytes.len())
                .ok_or(ObservedValueError::CapacityOverflow)?;
            return Ok(());
        }
        for chunk in bytes.chunks(1024) {
            self.session.admit(ExecutionProgress {
                phase: ExecutionPhase::CanonicalDigest,
                site: self.site,
                work: chunk.len(),
                copy_bytes: 0,
            })?;
            if let State::Hash {
                hasher,
                expected,
                written,
            } = &mut self.state
            {
                let next = written
                    .checked_add(chunk.len())
                    .ok_or(ObservedValueError::CapacityOverflow)?;
                if next > *expected {
                    return Err(ObservedValueError::InvalidRange);
                }
                hasher.update(chunk);
                *written = next;
            }
        }
        Ok(())
    }
    pub(super) fn push(&mut self, value: u8) -> R {
        self.extend_from_slice(&[value])
    }
    pub(super) fn refuse(&mut self, make: impl FnOnce() -> WireRefusal + Copy) -> R {
        self.admit(
            1,
            size_of::<WireRefusal>() + size_of::<Option<WireRefusal>>(),
        )?;
        self.refuse_owned(make())
    }
    pub(super) fn refuse_owned(&mut self, refusal: WireRefusal) -> R {
        if let State::Check(held) = &mut self.state {
            held.capture(refusal);
            return self.with_check(|held, out| held.accept(out));
        }
        self.poll()?;
        Err(ObservedValueError::UnsupportedValue)
    }
    pub(super) fn note_over_limit(&mut self, what: &'static str, count: u64) -> R {
        // Preserve the original total identity API, while the checked entry
        // refuses exactly the writer's existing count boundary before spelling.
        self.poll()?;
        if matches!(&self.state, State::Check(_)) {
            return self.with_check(|held, out| held.count(what, count, out));
        }
        match self.counts {
            CountPolicy::IdentityTotal => Ok(()),
            CountPolicy::RequireWireImage => Err(ObservedValueError::UnsupportedValue),
        }
    }
    pub(super) fn count(&mut self) -> R<usize> {
        self.poll()?;
        match &self.state {
            State::Count(count) => Ok(*count),
            State::Check(held) => Ok(held.len),
            State::Hash { .. } => Err(ObservedValueError::UnsupportedValue),
        }
    }
    pub(super) fn finish_hash(&mut self) -> R<ProofDigest> {
        self.session.admit(ExecutionProgress {
            phase: ExecutionPhase::CanonicalDigest,
            site: self.site,
            work: 128,
            copy_bytes: 0,
        })?;
        let State::Hash {
            hasher,
            expected,
            written,
        } = core::mem::replace(&mut self.state, State::Count(0))
        else {
            return Err(ObservedValueError::UnsupportedValue);
        };
        if written != expected {
            return Err(ObservedValueError::InvalidRange);
        }
        Ok(ProofDigest::sha256(hasher.finalize().into()))
    }
    pub(super) fn publication(&mut self) -> R {
        self.session
            .admit(ExecutionProgress {
                phase: ExecutionPhase::Publication,
                site: self.site,
                work: 0,
                copy_bytes: 0,
            })
            .map_err(Into::into)
    }

    pub(super) fn body_prepare<T>(&mut self) -> R {
        let copy = size_of::<T>()
            .checked_mul(2)
            .and_then(|n| {
                size_of::<Option<T>>()
                    .checked_mul(2)
                    .and_then(|r| n.checked_add(r))
            })
            .ok_or(ObservedValueError::CapacityOverflow)?;
        self.admit(
            copy.checked_add(3)
                .ok_or(ObservedValueError::CapacityOverflow)?,
            copy,
        )
    }
    pub(super) fn body_push<T: Copy>(&mut self, rows: &mut Vec<T>, value: T) -> R {
        self.body_prepare::<T>()?;
        self.push_value(rows, value)
    }
    pub(super) fn body_retirement(&mut self, work: usize, copies: usize) {
        self.session.retirement_record(self.site, work, copies);
    }
    pub(super) fn body_retire<T>(&mut self, value: T) {
        let bytes = size_of::<T>();
        self.body_retirement(bytes.saturating_add(1), bytes);
        drop(value);
    }
    pub(super) fn body_retire_text(&mut self, text: String) {
        self.body_retirement(
            size_of::<String>() + size_of::<Vec<u8>>() + 1,
            size_of::<String>() + size_of::<Vec<u8>>(),
        );
        let mut bytes = text.into_bytes();
        while !bytes.is_empty() {
            let chunk = bytes.len().min(1024);
            self.body_retirement(chunk.saturating_add(1), chunk);
            bytes.truncate(bytes.len() - chunk);
        }
        self.body_retire(bytes);
    }
    pub(super) fn body_type_eq(&mut self, a: &Ty, b: &Ty) -> R<bool> {
        a.structural_eq_observed(b, self.session, self.site)
    }
    pub(super) fn body_type_text(&mut self, ty: &Ty) -> R<String> {
        ty.display_observed(self.session, self.site)
    }
    pub(super) fn body_inline_types<'i>(&mut self, inst: &'i Inst) -> R<Vec<&'i Ty>> {
        inst.inline_types_observed(self.session, self.site)
    }
    pub(super) fn body_domain(&mut self, bytes: &[u8]) -> R<ProofDigest> {
        ProofDigest::sha256_domain_observed(
            crate::FUNCTION_BODY_DIGEST_V1_DOMAIN,
            bytes,
            self.session,
            self.site,
        )
    }
    pub(super) fn reserve<T>(&mut self, rows: &mut Vec<T>, additional: usize) -> R {
        self.poll()?;
        let needed = rows
            .len()
            .checked_add(additional)
            .ok_or(ObservedValueError::CapacityOverflow)?;
        if needed > rows.capacity() {
            let requested = rows
                .len()
                .checked_mul(2)
                .and_then(|n| n.checked_add(additional))
                .ok_or(ObservedValueError::CapacityOverflow)?;
            let work = requested
                .checked_add(rows.len())
                .ok_or(ObservedValueError::CapacityOverflow)?;
            let bytes = work
                .checked_mul(size_of::<T>())
                .ok_or(ObservedValueError::CapacityOverflow)?;
            self.admit(work, bytes)?;
            rows.try_reserve_exact(requested - rows.len())
                .map_err(|_| ObservedValueError::AllocationFailed)?;
        }
        Ok(())
    }
    pub(super) fn push_value<T>(&mut self, rows: &mut Vec<T>, value: T) -> R {
        self.reserve(rows, 1)?;
        self.admit(1, size_of::<T>())?;
        rows.push(value);
        Ok(())
    }
    /// Consume the actual child scratch before the original final poll. A
    /// later cleanup refusal withholds healthy output but cannot replace an
    /// error already returned by the child; session first cause is separate.
    pub(super) fn finish_child<T, S>(&mut self, result: R<T>, scratch: S) -> R<T> {
        self.retire(scratch);
        let terminal = self.poll();
        result.and_then(|value| terminal.map(|()| value))
    }
    pub(super) fn retire<T>(&mut self, value: T) {
        self.retirement_poll();
        drop(value);
        self.retirement_poll();
    }
}
