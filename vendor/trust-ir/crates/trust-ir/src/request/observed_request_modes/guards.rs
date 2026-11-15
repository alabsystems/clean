// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
#[derive(Clone, Copy)]
enum Find {
    Assumption,
    SitedAssertion,
}
impl State {
    pub(super) fn mc<O: ExecutionObserver>(
        &mut self,
        r: &TrustMcNativeRequest,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        w.admit(2, size_of::<McMode>() + size_of::<NativeRequestId>())?;
        match r.mode {
            McMode::BoundedModelCheck => {
                w.admit(2, size_of::<u32>() + size_of::<bool>())?;
                if r.options.bmc.unwind_limit == 0 {
                    self.fixed(
                        || E::InvalidTrustMcBmcOptions {
                            request: r.id,
                            field: "bmc.unwind_limit",
                        },
                        w,
                    )?;
                }
            }
            McMode::Chc => self.chc(r, w)?,
            McMode::Pdr => {
                w.admit(1, size_of::<bool>())?;
                if !r.options.chc.pdr.enabled {
                    self.fixed(
                        || E::InvalidTrustMcChcOptions {
                            request: r.id,
                            field: "chc.pdr.enabled",
                        },
                        w,
                    )?;
                }
                self.chc(r, w)?;
            }
        }
        Ok(())
    }
    fn chc<O: ExecutionObserver>(
        &mut self,
        r: &TrustMcNativeRequest,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        w.admit(1, size_of::<bool>())?;
        if !r.options.chc.emit_horn_clauses {
            self.fixed(
                || E::InvalidTrustMcChcOptions {
                    request: r.id,
                    field: "chc.emit_horn_clauses",
                },
                w,
            )?;
        }
        w.admit(2, size_of::<Option<u32>>() + size_of::<bool>())?;
        if r.options.chc.pdr.max_frames == Some(0) {
            self.fixed(
                || E::InvalidTrustMcChcOptions {
                    request: r.id,
                    field: "chc.pdr.max_frames",
                },
                w,
            )?;
        }
        Ok(())
    }
    pub(super) fn wp<O: ExecutionObserver>(
        &mut self,
        r: &TrustWpNativeRequest,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        w.admit(2, size_of::<WpMode>() + size_of::<NativeRequestId>())?;
        if r.mode == WpMode::StrongestPostcondition {
            w.admit(1, size_of::<&[NativeReplayAtom]>())?;
            let atoms = &r.provenance.replay_context().atoms;
            // Both independent original any searches run even if the first
            // is false; neither one validates formula/status/identity fields.
            let has_assumption = self.any(atoms, Find::Assumption, w)?;
            let has_assertion = self.any(atoms, Find::SitedAssertion, w)?;
            w.admit(2, 2 * size_of::<bool>())?;
            if !has_assumption || !has_assertion {
                self.fixed(|| E::MissingTrustWpStrongestPostconditionContext(r.id), w)?;
            }
        }
        w.admit(1, size_of::<bool>())?;
        if !r.options.emit_verification_conditions {
            self.fixed(
                || E::InvalidTrustWpOptions {
                    request: r.id,
                    field: "emit_verification_conditions",
                },
                w,
            )?;
        }
        w.admit(2, size_of::<u32>() + 2 * size_of::<bool>())?;
        if r.mode == WpMode::Abduction && r.options.max_abduced_preconditions == 0 {
            self.fixed(
                || E::InvalidTrustWpOptions {
                    request: r.id,
                    field: "max_abduced_preconditions",
                },
                w,
            )?;
        }
        Ok(())
    }
    fn any<O: ExecutionObserver>(
        &self,
        atoms: &[NativeReplayAtom],
        find: Find,
        w: &mut Work<'_, '_, O>,
    ) -> R<bool> {
        let mut at = 0;
        while let Some(a) = w.at(atoms, at)? {
            w.admit(
                3,
                size_of::<NativeReplayAtomKind>()
                    + size_of::<Option<super::super::NativeAssertionId>>()
                    + size_of::<bool>(),
            )?;
            let found = match find {
                Find::Assumption => a.kind == NativeReplayAtomKind::Assumption,
                Find::SitedAssertion => {
                    a.kind == NativeReplayAtomKind::Assertion && a.assertion_id.is_some()
                }
            };
            if found {
                return Ok(true);
            }
            w.next(&mut at)?;
        }
        Ok(false)
    }
    pub(super) fn diagnostics<O: ExecutionObserver>(
        &mut self,
        id: NativeRequestId,
        p: &NativeDiagnosticsPolicy,
        w: &mut Work<'_, '_, O>,
    ) -> R {
        w.admit(1, size_of::<bool>())?;
        if !p.include_source_spans {
            self.fixed(
                || E::InvalidDiagnosticsPolicy {
                    request: id,
                    field: "include_source_spans",
                },
                w,
            )?;
        }
        w.admit(1, size_of::<bool>())?;
        if !p.include_lineage {
            self.fixed(
                || E::InvalidDiagnosticsPolicy {
                    request: id,
                    field: "include_lineage",
                },
                w,
            )?;
        }
        w.admit(2, size_of::<u32>() + 2 * size_of::<bool>())?;
        if p.emit_counterexamples && p.max_counterexamples == 0 {
            self.fixed(
                || E::InvalidDiagnosticsPolicy {
                    request: id,
                    field: "max_counterexamples",
                },
                w,
            )?;
        }
        Ok(())
    }
}
