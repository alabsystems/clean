// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Explicit subset observation. This never claims a complete global delta.

use super::source::{bounded_hash, snapshot_names};
use super::{
    RuntimeEnvironmentRow, RuntimeEnvironmentRowFailure, RuntimeSourceCaptureLimits,
    RuntimeSourceRecord,
};
use crate::runtime_binding::RuntimeBindingPlan;
use clean_kernel::{Environment, Name};
use std::collections::BTreeSet;

/// Bounded observation of the exact runtime dependency plan, including its
/// actual compiler attributes. This is an observation, not frontend custody,
/// a native capability, a complete global snapshot or a certificate.
#[derive(Clone, Debug)]
pub struct RuntimeScopedEnvironmentCapture {
    roots: BTreeSet<Name>,
    members: BTreeSet<Name>,
    sources: Vec<RuntimeSourceRecord>,
    before: Vec<RuntimeEnvironmentRow>,
    after: Vec<RuntimeEnvironmentRow>,
    row_failures: Vec<RuntimeEnvironmentRowFailure>,
    errors: Vec<String>,
    snapshot_blake3: Option<[u8; 32]>,
}

impl RuntimeScopedEnvironmentCapture {
    pub fn capture(
        before: &Environment,
        after: &Environment,
        sources: Vec<RuntimeSourceRecord>,
        plan: &RuntimeBindingPlan,
    ) -> Self {
        Self::capture_with_limits(
            before,
            after,
            sources,
            plan,
            RuntimeSourceCaptureLimits::default(),
        )
    }

    /// Explicit limits only reduce observation authority when a row cannot fit;
    /// the source-owned native frontend uses the unchanged default limits.
    pub fn capture_with_limits(
        before: &Environment,
        after: &Environment,
        sources: Vec<RuntimeSourceRecord>,
        plan: &RuntimeBindingPlan,
        limits: RuntimeSourceCaptureLimits,
    ) -> Self {
        let roots: BTreeSet<_> = plan.roots().cloned().collect();
        let members: BTreeSet<_> = plan.members().cloned().collect();
        let mut capture = Self {
            roots,
            members,
            sources,
            before: Vec::new(),
            after: Vec::new(),
            row_failures: Vec::new(),
            errors: Vec::new(),
            snapshot_blake3: None,
        };
        if let Err(error) = plan.recheck_discovery(after) {
            capture.errors.push(format!(
                "scoped runtime binding plan does not match environment: {error}"
            ));
            return capture;
        }
        let source_bytes = capture.sources.iter().try_fold(0usize, |sum, source| {
            sum.checked_add(source.module.len())?
                .checked_add(source.path.len())?
                .checked_add(source.source.len())
        });
        if capture.sources.is_empty()
            || capture.sources.len() > limits.declarations
            || source_bytes.is_none_or(|n| n > limits.source_bytes)
        {
            capture.errors.push(
                "scoped source snapshot population/byte bound exceeded or no supplied sources"
                    .into(),
            );
        }
        if capture.roots.is_empty() || capture.members.len() > limits.declarations {
            capture
                .errors
                .push("scoped declaration population bound exceeded or no roots".into());
            return capture;
        }
        // Only names actually present in the baseline are compared. Absence of
        // newly elaborated/imported members from the baseline is expected.
        let baseline: BTreeSet<_> = before
            .constants()
            .map(|r| &r.name)
            .chain(before.inductives().map(|r| &r.name))
            .chain(before.constructors().map(|r| &r.name))
            .chain(before.recursors().map(|r| &r.name))
            .chain(before.quotients().map(|r| &r.name))
            .filter(|n| capture.members.contains(*n))
            .cloned()
            .collect();
        let mut remaining = limits.total_bytes;
        let (rows, old) = snapshot_names(
            before,
            baseline,
            limits,
            "scoped before",
            &mut remaining,
            &mut capture.errors,
            &mut capture.row_failures,
        );
        capture.before = rows;
        let (rows, current) = snapshot_names(
            after,
            capture.members.clone(),
            limits,
            "scoped after",
            &mut remaining,
            &mut capture.errors,
            &mut capture.row_failures,
        );
        capture.after = rows;
        if old
            .iter()
            .any(|(name, hash)| current.get(name) != Some(hash))
        {
            capture.errors.push(
                "scoped source check changed or removed baseline declaration payloads/provenance"
                    .into(),
            );
        }
        // A row includes its runtime attributes for the same 16 MiB per-row
        // bound. The final digest also accounts for every attribute under the
        // same 64 MiB total bound, including roots/member identities and source.
        // Fixed-width bincode adds no framing between tuple fields. The row was
        // already streamed by snapshot_names. Only the following attribute field
        // needs to be encoded against the remainder of the row budget.
        for (name, binding) in &current {
            let attribute_budget = limits.row_bytes - binding.encoded_bytes;
            if let Err(reason) = bounded_hash(&plan.attribute_rows().get(name), attribute_budget) {
                capture.errors.push(
                    "cannot bind scoped row with runtime attributes; typed row failure retained"
                        .into(),
                );
                capture.row_failures.push(RuntimeEnvironmentRowFailure {
                    phase: "scoped runtime attributes",
                    name: name.clone(),
                    reason: format!(
                        "{reason} (row_limit={}, encoded_row={})",
                        limits.row_bytes, binding.encoded_bytes
                    ),
                });
            }
        }
        if capture.errors.is_empty() && capture.after.len() == capture.members.len() {
            match bounded_hash(
                &(
                    "clean.runtime-scoped-environment-observation/v1-fixed-le",
                    &capture.sources,
                    plan,
                    &capture.before,
                    &capture.after,
                ),
                limits.total_bytes,
            ) {
                Ok((digest, _)) => capture.snapshot_blake3 = Some(digest),
                Err(reason) => capture.errors.push(format!(
                    "cannot bind scoped environment observation: {reason}"
                )),
            }
        }
        capture
    }

    pub fn roots(&self) -> &BTreeSet<Name> {
        &self.roots
    }
    pub fn members(&self) -> &BTreeSet<Name> {
        &self.members
    }
    pub fn sources(&self) -> &[RuntimeSourceRecord] {
        &self.sources
    }
    pub fn before(&self) -> &[RuntimeEnvironmentRow] {
        &self.before
    }
    pub fn after(&self) -> &[RuntimeEnvironmentRow] {
        &self.after
    }
    pub fn row_failures(&self) -> &[RuntimeEnvironmentRowFailure] {
        &self.row_failures
    }
    pub fn errors(&self) -> &[String] {
        &self.errors
    }
    pub fn snapshot_blake3(&self) -> Option<[u8; 32]> {
        self.snapshot_blake3
    }
    pub fn is_complete(&self) -> bool {
        self.errors.is_empty()
            && self.row_failures.is_empty()
            && self.snapshot_blake3.is_some()
            && self.after.len() == self.members.len()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::{BinderInfo, Declaration, Expr};
    fn n(value: &str) -> Name {
        Name::from_string(value)
    }
    fn source() -> Vec<RuntimeSourceRecord> {
        vec![RuntimeSourceRecord {
            module: "Ordinary".into(),
            path: "Ordinary.lean".into(),
            source: "def query (x : Nat) : Nat := x".into(),
        }]
    }
    fn fixture() -> (Environment, Environment, RuntimeBindingPlan) {
        let before = Environment::with_prelude();
        let mut after = before.clone();
        for name in ["query", "unselected"] {
            after
                .add_decl(Declaration::Definition {
                    name: n(name),
                    level_params: vec![],
                    type_: Expr::arrow(Expr::const_str("Nat"), Expr::const_str("Nat")),
                    value: Expr::lam(BinderInfo::Default, Expr::const_str("Nat"), Expr::bvar(0)),
                    is_reducible: false,
                })
                .unwrap();
        }
        let plan = RuntimeBindingPlan::discover(&after, &[n("query")], 100).unwrap();
        (before, after, plan)
    }
    #[test]
    fn scoped_capture_binds_exact_rows_attributes_sources_and_domain() {
        let (before, after, plan) = fixture();
        let capture = RuntimeScopedEnvironmentCapture::capture(&before, &after, source(), &plan);
        assert!(capture.is_complete(), "{:?}", capture.errors());
        assert!(capture.members().contains(&n("query")));
        assert!(!capture.members().contains(&n("unselected")));
        assert_eq!(capture.after().len(), plan.members().len());
        let mut changed_source = source();
        changed_source[0].source.push(' ');
        let changed =
            RuntimeScopedEnvironmentCapture::capture(&before, &after, changed_source, &plan);
        assert_ne!(capture.snapshot_blake3(), changed.snapshot_blake3());
        let mut changed_env = after;
        changed_env.register_extern(n("query"), "different_runtime_symbol".into());
        let stale =
            RuntimeScopedEnvironmentCapture::capture(&before, &changed_env, source(), &plan);
        assert!(!stale.is_complete());
        assert!(stale.snapshot_blake3().is_none());
        let changed_plan = RuntimeBindingPlan::discover(&changed_env, &[n("query")], 100).unwrap();
        let changed = RuntimeScopedEnvironmentCapture::capture(
            &before,
            &changed_env,
            source(),
            &changed_plan,
        );
        assert!(changed.is_complete());
        assert_ne!(capture.snapshot_blake3(), changed.snapshot_blake3());
    }
    #[test]
    fn scoped_capture_all_limits_refuse_without_digest() {
        let (before, after, plan) = fixture();
        let d = RuntimeSourceCaptureLimits::default();
        for limits in [
            RuntimeSourceCaptureLimits { row_bytes: 1, ..d },
            RuntimeSourceCaptureLimits {
                total_bytes: 1,
                ..d
            },
            RuntimeSourceCaptureLimits {
                source_bytes: 1,
                ..d
            },
            RuntimeSourceCaptureLimits {
                declarations: 0,
                ..d
            },
        ] {
            let capture = RuntimeScopedEnvironmentCapture::capture_with_limits(
                &before,
                &after,
                source(),
                &plan,
                limits,
            );
            assert!(!capture.is_complete());
            assert!(capture.snapshot_blake3().is_none());
            assert!(!capture.errors().is_empty());
        }
        let capture = RuntimeScopedEnvironmentCapture::capture(&before, &after, vec![], &plan);
        assert!(!capture.is_complete());
    }
    #[test]
    fn scoped_capture_runtime_attribute_bytes_share_row_and_total_bounds() {
        let (before, mut after, _) = fixture();
        after.register_extern(n("query"), "x".repeat(32768));
        let plan = RuntimeBindingPlan::discover(&after, &[n("query")], 100).unwrap();
        let d = RuntimeSourceCaptureLimits::default();
        for limits in [
            RuntimeSourceCaptureLimits {
                row_bytes: 16384,
                ..d
            },
            RuntimeSourceCaptureLimits {
                total_bytes: 16384,
                ..d
            },
        ] {
            let capture = RuntimeScopedEnvironmentCapture::capture_with_limits(
                &before,
                &after,
                source(),
                &plan,
                limits,
            );
            assert!(!capture.is_complete());
            assert!(capture.snapshot_blake3().is_none());
            assert!(!capture.errors().is_empty());
        }
    }
    #[test]
    fn scoped_attribute_budget_matches_the_complete_original_row_encoding() {
        let (before, mut after, _) = fixture();
        let query = n("query");
        after.register_extern(query.clone(), "x".repeat(4096));
        let plan = RuntimeBindingPlan::discover(&after, std::slice::from_ref(&query), 100).unwrap();
        let full = RuntimeScopedEnvironmentCapture::capture(&before, &after, source(), &plan);
        assert!(full.is_complete());
        let row = full.after().iter().find(|row| row.name == query).unwrap();
        let limits = RuntimeSourceCaptureLimits::default();
        let (_, row_bytes) = bounded_hash(row, limits.row_bytes).unwrap();
        let (_, required) =
            bounded_hash(&(row, plan.attribute_rows().get(&query)), limits.row_bytes).unwrap();
        let check = |row_bytes| {
            RuntimeScopedEnvironmentCapture::capture_with_limits(
                &before,
                &after,
                source(),
                &plan,
                RuntimeSourceCaptureLimits {
                    row_bytes,
                    ..limits
                },
            )
        };
        let exact = check(required);
        assert!(exact.is_complete(), "{:?}", exact.errors());
        assert_eq!(exact.snapshot_blake3(), full.snapshot_blake3());
        let short = check(required - 1);
        assert!(!short.is_complete());
        assert!(short.snapshot_blake3().is_none());
        let failure = short
            .row_failures()
            .iter()
            .find(|failure| failure.name == query)
            .unwrap();
        assert_eq!(failure.phase, "scoped runtime attributes");
        assert!(failure.reason.contains(&format!("encoded_row={row_bytes}")));
        assert!(failure
            .reason
            .contains(&format!("limit={}", required - row_bytes - 1)));
    }
    #[test]
    fn scoped_capture_missing_member_and_changed_baseline_are_not_complete() {
        let (before, after, plan) = fixture();
        let capture = RuntimeScopedEnvironmentCapture::capture(&before, &before, source(), &plan);
        assert!(!capture.is_complete());
        assert!(capture.snapshot_blake3().is_none());
        assert!(capture
            .errors()
            .iter()
            .any(|e| e.contains("plan does not match environment")));
        assert!(
            capture.row_failures().is_empty(),
            "discovery refused before row capture"
        );
        let mut changed = after.clone();
        changed.register_extern(n("query"), "same_logical_body_different_runtime".into());
        // Baseline payload/provenance changes are still checked independently
        // of the plan's runtime metadata (which is included in the digest).
        changed.mark_unsafe(n("query"));
        let plan = RuntimeBindingPlan::discover(&changed, &[n("query")], 100).unwrap();
        let capture = RuntimeScopedEnvironmentCapture::capture(&after, &changed, source(), &plan);
        assert!(!capture.is_complete());
        assert!(capture
            .errors()
            .iter()
            .any(|e| e.contains("changed or removed baseline")));
    }
}
