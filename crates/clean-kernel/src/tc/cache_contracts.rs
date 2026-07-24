// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Verification-oriented stubs for the 25 documented `TypeCheckCache` contracts.
//! The concrete cache lives in `crate::cache`; this module snapshots public
//! behavior for tests and future Kani harnesses.

use crate::{cache::TypeCheckCache, expr::Expr};

const INSERT_LEN_BOUND: usize = 100_001;

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub(crate) struct CacheSnapshot {
    pub env_hash: u64,
    pub mode_hash: u64,
    pub len: usize,
    pub is_empty: bool,
    pub hits: u64,
    pub misses: u64,
    pub entries: usize,
}

impl CacheSnapshot {
    pub(crate) fn capture(cache: &TypeCheckCache) -> Self {
        let s = cache.stats();
        Self {
            env_hash: cache.env_hash(),
            mode_hash: cache.mode_hash(),
            len: cache.len(),
            is_empty: cache.is_empty(),
            hits: s.hits,
            misses: s.misses,
            entries: s.entries,
        }
    }
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub(crate) enum CacheOperation {
    #[default]
    Snapshot,
    New,
    WithHashes,
    SetEnvHash,
    SetModeHash,
    Get,
    Insert,
    Stats,
    Clear,
    Len,
    IsEmpty,
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum CacheInvariant {
    StatsReferenceIsCurrent,
    ClearEmptiesCache,
    ClearResetsHits,
    ClearResetsMisses,
    LenZeroIffEmpty,
    IsEmptyIffLenZero,
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum CachePrecondition {
    SetEnvHashPreservesContentsWhenSame,
    SetModeHashPreservesContentsWhenSame,
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum CachePostcondition {
    NewStartsEmpty,
    NewLenZero,
    WithHashesStartsEmpty,
    GetReturnsInsertedValue,
    InsertMakesLookupSucceed,
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum MonotonicGrowth {
    GetHitIncrementsHits,
    GetMissIncrementsMisses,
    InsertEntriesMatchLen,
    InsertLenBounded,
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum HashConsistency {
    WithHashesSetsEnvHash,
    WithHashesSetsModeHash,
    SetEnvHashUpdatesHash,
    SetEnvHashChangeClears,
    SetModeHashUpdatesHash,
    SetModeHashChangeClears,
    ClearPreservesEnvHash,
    ClearPreservesModeHash,
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum ContractSpec {
    Invariant(CacheInvariant),
    Precondition(CachePrecondition),
    Postcondition(CachePostcondition),
    MonotonicGrowth(MonotonicGrowth),
    HashConsistency(HashConsistency),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) struct CacheContract {
    pub spec: ContractSpec,
    pub label: &'static str,
    pub assertion: &'static str,
}
const fn c(spec: ContractSpec, label: &'static str, assertion: &'static str) -> CacheContract {
    CacheContract {
        spec,
        label,
        assertion,
    }
}

#[rustfmt::skip]
pub(crate) const CACHE_CONTRACTS: [CacheContract; 25] = [
    c(ContractSpec::Postcondition(CachePostcondition::NewStartsEmpty), "new.starts_empty", "after.is_empty"),
    c(ContractSpec::Postcondition(CachePostcondition::NewLenZero), "new.len_zero", "after.len == 0"),
    c(ContractSpec::Postcondition(CachePostcondition::WithHashesStartsEmpty), "with_hashes.starts_empty", "after.is_empty"),
    c(ContractSpec::HashConsistency(HashConsistency::WithHashesSetsEnvHash), "with_hashes.env_hash", "after.env_hash == requested_env_hash"),
    c(ContractSpec::HashConsistency(HashConsistency::WithHashesSetsModeHash), "with_hashes.mode_hash", "after.mode_hash == requested_mode_hash"),
    c(ContractSpec::HashConsistency(HashConsistency::SetEnvHashUpdatesHash), "set_env_hash.updates_hash", "after.env_hash == requested_env_hash"),
    c(ContractSpec::HashConsistency(HashConsistency::SetEnvHashChangeClears), "set_env_hash.clears_on_change", "requested_env_hash != before.env_hash => after.is_empty && after.entries == 0"),
    c(ContractSpec::Precondition(CachePrecondition::SetEnvHashPreservesContentsWhenSame), "set_env_hash.preserves_on_same", "requested_env_hash == before.env_hash => content(before) == content(after)"),
    c(ContractSpec::HashConsistency(HashConsistency::SetModeHashUpdatesHash), "set_mode_hash.updates_hash", "after.mode_hash == requested_mode_hash"),
    c(ContractSpec::HashConsistency(HashConsistency::SetModeHashChangeClears), "set_mode_hash.clears_on_change", "requested_mode_hash != before.mode_hash => after.is_empty && after.entries == 0"),
    c(ContractSpec::Precondition(CachePrecondition::SetModeHashPreservesContentsWhenSame), "set_mode_hash.preserves_on_same", "requested_mode_hash == before.mode_hash => content(before) == content(after)"),
    c(ContractSpec::Postcondition(CachePostcondition::GetReturnsInsertedValue), "get.returns_inserted_value", "expected_lookup.is_some() => lookup_result == expected_lookup"),
    c(ContractSpec::MonotonicGrowth(MonotonicGrowth::GetHitIncrementsHits), "get.hit_increments_hits", "lookup_result.is_some() => after.hits == before.hits + 1 && after.misses == before.misses"),
    c(ContractSpec::MonotonicGrowth(MonotonicGrowth::GetMissIncrementsMisses), "get.miss_increments_misses", "lookup_result.is_none() => after.misses == before.misses + 1 && after.hits == before.hits"),
    c(ContractSpec::Postcondition(CachePostcondition::InsertMakesLookupSucceed), "insert.enables_lookup", "expected_lookup.is_some() => lookup_result == expected_lookup"),
    c(ContractSpec::MonotonicGrowth(MonotonicGrowth::InsertEntriesMatchLen), "insert.entries_match_len", "after.entries == after.len"),
    c(ContractSpec::MonotonicGrowth(MonotonicGrowth::InsertLenBounded), "insert.len_bounded", "after.len <= len_bound"),
    c(ContractSpec::Invariant(CacheInvariant::StatsReferenceIsCurrent), "stats.reference_is_current", "stats_observed && after.entries == after.len"),
    c(ContractSpec::Invariant(CacheInvariant::ClearEmptiesCache), "clear.empties_cache", "after.is_empty"),
    c(ContractSpec::Invariant(CacheInvariant::ClearResetsHits), "clear.resets_hits", "after.hits == 0"),
    c(ContractSpec::Invariant(CacheInvariant::ClearResetsMisses), "clear.resets_misses", "after.misses == 0"),
    c(ContractSpec::HashConsistency(HashConsistency::ClearPreservesEnvHash), "clear.preserves_env_hash", "after.env_hash == before.env_hash"),
    c(ContractSpec::HashConsistency(HashConsistency::ClearPreservesModeHash), "clear.preserves_mode_hash", "after.mode_hash == before.mode_hash"),
    c(ContractSpec::Invariant(CacheInvariant::LenZeroIffEmpty), "len.zero_iff_empty", "(after.len == 0) == after.is_empty"),
    c(ContractSpec::Invariant(CacheInvariant::IsEmptyIffLenZero), "is_empty.iff_len_zero", "after.is_empty == (after.len == 0)"),
];

#[derive(Clone, Debug, Default)]
pub(crate) struct CacheState {
    pub operation: CacheOperation,
    pub before: Option<CacheSnapshot>,
    pub after: CacheSnapshot,
    pub requested_env_hash: Option<u64>,
    pub requested_mode_hash: Option<u64>,
    pub expected_lookup: Option<Expr>,
    pub lookup_result: Option<Expr>,
    pub stats_observed: bool,
    pub len_bound: usize,
}

impl CacheState {
    pub(crate) fn after(operation: CacheOperation, cache: &TypeCheckCache) -> Self {
        Self {
            operation,
            before: None,
            after: CacheSnapshot::capture(cache),
            requested_env_hash: None,
            requested_mode_hash: None,
            expected_lookup: None,
            lookup_result: None,
            stats_observed: true,
            len_bound: INSERT_LEN_BOUND,
        }
    }

    pub(crate) fn transition(
        operation: CacheOperation,
        before: CacheSnapshot,
        cache: &TypeCheckCache,
    ) -> Self {
        Self {
            before: Some(before),
            ..Self::after(operation, cache)
        }
    }

    pub(crate) fn with_lookup(mut self, got: Option<Expr>, expected: Option<Expr>) -> Self {
        self.lookup_result = got;
        self.expected_lookup = expected;
        self
    }
    pub(crate) fn with_requested_env_hash(mut self, env_hash: u64) -> Self {
        self.requested_env_hash = Some(env_hash);
        self
    }
    pub(crate) fn with_requested_mode_hash(mut self, mode_hash: u64) -> Self {
        self.requested_mode_hash = Some(mode_hash);
        self
    }
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub(crate) struct ContractVerdict {
    pub applicable: bool,
    pub holds: bool,
}
fn ok(holds: bool) -> ContractVerdict {
    ContractVerdict {
        applicable: true,
        holds,
    }
}
fn skip() -> ContractVerdict {
    ContractVerdict::default()
}
fn probe_matches(state: &CacheState) -> bool {
    state.lookup_result.as_ref() == state.expected_lookup.as_ref()
}
fn content_unchanged(before: &CacheSnapshot, after: &CacheSnapshot) -> bool {
    before.env_hash == after.env_hash
        && before.mode_hash == after.mode_hash
        && before.len == after.len
        && before.is_empty == after.is_empty
        && before.entries == after.entries
}

pub(crate) fn verify_cache_contract(spec: ContractSpec, state: &CacheState) -> ContractVerdict {
    use self::CacheInvariant::*;
    use self::CacheOperation::*;
    use self::CachePostcondition::*;
    use self::CachePrecondition::*;
    use self::HashConsistency::*;
    use self::MonotonicGrowth::*;

    match spec {
        ContractSpec::Postcondition(NewStartsEmpty) if state.operation == New => {
            ok(state.after.is_empty)
        }
        ContractSpec::Postcondition(NewLenZero) if state.operation == New => {
            ok(state.after.len == 0)
        }
        ContractSpec::Postcondition(WithHashesStartsEmpty) if state.operation == WithHashes => {
            ok(state.after.is_empty)
        }
        ContractSpec::HashConsistency(WithHashesSetsEnvHash) if state.operation == WithHashes => {
            ok(state.requested_env_hash == Some(state.after.env_hash))
        }
        ContractSpec::HashConsistency(WithHashesSetsModeHash) if state.operation == WithHashes => {
            ok(state.requested_mode_hash == Some(state.after.mode_hash))
        }
        ContractSpec::HashConsistency(SetEnvHashUpdatesHash)
            if state.operation == SetEnvHash && state.requested_env_hash.is_some() =>
        {
            ok(state.requested_env_hash == Some(state.after.env_hash))
        }
        ContractSpec::HashConsistency(SetEnvHashChangeClears) if state.operation == SetEnvHash => {
            match (state.before.as_ref(), state.requested_env_hash) {
                (Some(before), Some(requested)) if before.env_hash != requested => {
                    ok(state.after.is_empty && state.after.entries == 0)
                }
                _ => skip(),
            }
        }
        ContractSpec::Precondition(SetEnvHashPreservesContentsWhenSame)
            if state.operation == SetEnvHash =>
        {
            match (state.before.as_ref(), state.requested_env_hash) {
                (Some(before), Some(requested))
                    if before.env_hash == requested && state.expected_lookup.is_some() =>
                {
                    ok(content_unchanged(before, &state.after) && probe_matches(state))
                }
                _ => skip(),
            }
        }
        ContractSpec::HashConsistency(SetModeHashUpdatesHash)
            if state.operation == SetModeHash && state.requested_mode_hash.is_some() =>
        {
            ok(state.requested_mode_hash == Some(state.after.mode_hash))
        }
        ContractSpec::HashConsistency(SetModeHashChangeClears)
            if state.operation == SetModeHash =>
        {
            match (state.before.as_ref(), state.requested_mode_hash) {
                (Some(before), Some(requested)) if before.mode_hash != requested => {
                    ok(state.after.is_empty && state.after.entries == 0)
                }
                _ => skip(),
            }
        }
        ContractSpec::Precondition(SetModeHashPreservesContentsWhenSame)
            if state.operation == SetModeHash =>
        {
            match (state.before.as_ref(), state.requested_mode_hash) {
                (Some(before), Some(requested))
                    if before.mode_hash == requested && state.expected_lookup.is_some() =>
                {
                    ok(content_unchanged(before, &state.after) && probe_matches(state))
                }
                _ => skip(),
            }
        }
        ContractSpec::Postcondition(GetReturnsInsertedValue)
            if state.operation == Get && state.expected_lookup.is_some() =>
        {
            ok(probe_matches(state))
        }
        ContractSpec::MonotonicGrowth(GetHitIncrementsHits) if state.operation == Get => {
            match state.before.as_ref() {
                Some(before) if state.lookup_result.is_some() => {
                    ok(state.after.hits == before.hits + 1 && state.after.misses == before.misses)
                }
                _ => skip(),
            }
        }
        ContractSpec::MonotonicGrowth(GetMissIncrementsMisses) if state.operation == Get => {
            match state.before.as_ref() {
                Some(before) if state.lookup_result.is_none() => {
                    ok(state.after.misses == before.misses + 1 && state.after.hits == before.hits)
                }
                _ => skip(),
            }
        }
        ContractSpec::Postcondition(InsertMakesLookupSucceed)
            if state.operation == Insert && state.expected_lookup.is_some() =>
        {
            ok(probe_matches(state))
        }
        ContractSpec::MonotonicGrowth(InsertEntriesMatchLen) if state.operation == Insert => {
            ok(state.after.entries == state.after.len)
        }
        ContractSpec::MonotonicGrowth(InsertLenBounded) if state.operation == Insert => {
            ok(state.after.len <= state.len_bound)
        }
        ContractSpec::Invariant(StatsReferenceIsCurrent) if state.operation == Stats => {
            ok(state.stats_observed && state.after.entries == state.after.len)
        }
        ContractSpec::Invariant(ClearEmptiesCache) if state.operation == Clear => {
            ok(state.after.is_empty)
        }
        ContractSpec::Invariant(ClearResetsHits) if state.operation == Clear => {
            ok(state.after.hits == 0)
        }
        ContractSpec::Invariant(ClearResetsMisses) if state.operation == Clear => {
            ok(state.after.misses == 0)
        }
        ContractSpec::HashConsistency(ClearPreservesEnvHash) if state.operation == Clear => {
            match state.before.as_ref() {
                Some(before) => ok(state.after.env_hash == before.env_hash),
                None => skip(),
            }
        }
        ContractSpec::HashConsistency(ClearPreservesModeHash) if state.operation == Clear => {
            match state.before.as_ref() {
                Some(before) => ok(state.after.mode_hash == before.mode_hash),
                None => skip(),
            }
        }
        ContractSpec::Invariant(LenZeroIffEmpty) if state.operation == Len => {
            ok((state.after.len == 0) == state.after.is_empty)
        }
        ContractSpec::Invariant(IsEmptyIffLenZero) if state.operation == IsEmpty => {
            ok(state.after.is_empty == (state.after.len == 0))
        }
        _ => skip(),
    }
}

#[derive(Clone, Debug, Default)]
pub(crate) struct CacheInvariantReport {
    pub operation: CacheOperation,
    pub checked: usize,
    pub held: Vec<&'static str>,
    pub failed: Vec<&'static str>,
}

impl CacheInvariantReport {
    pub(crate) fn from_state(state: &CacheState) -> Self {
        let mut report = Self {
            operation: state.operation,
            ..Self::default()
        };
        for contract in CACHE_CONTRACTS {
            let verdict = verify_cache_contract(contract.spec, state);
            if verdict.applicable {
                report.checked += 1;
                if verdict.holds {
                    report.held.push(contract.label);
                } else {
                    report.failed.push(contract.label);
                }
            }
        }
        report
    }

    pub(crate) fn all_hold(&self) -> bool {
        self.failed.is_empty()
    }
}

#[cfg(test)]
#[rustfmt::skip]
mod tests {
    use super::*;
    use crate::{expr::Expr, name::Name};

    fn key(name: &str) -> Expr { Expr::const_(Name::from_string(name), vec![]) }

    #[test]
    fn contract_catalog_covers_all_25_contracts() {
        assert_eq!(CACHE_CONTRACTS.len(), 25);
        assert!(CACHE_CONTRACTS.iter().any(|c| matches!(c.spec, ContractSpec::Invariant(_))));
        assert!(CACHE_CONTRACTS.iter().any(|c| matches!(c.spec, ContractSpec::Precondition(_))));
        assert!(CACHE_CONTRACTS.iter().any(|c| matches!(c.spec, ContractSpec::Postcondition(_))));
        assert!(CACHE_CONTRACTS.iter().any(|c| matches!(c.spec, ContractSpec::MonotonicGrowth(_))));
        assert!(CACHE_CONTRACTS.iter().any(|c| matches!(c.spec, ContractSpec::HashConsistency(_))));
    }

    #[test]
    fn insert_get_and_hash_transition_contracts_hold() {
        let expr = key("Cached");
        let type_ = Expr::type_();
        let miss = key("Missing");
        let mut cache = TypeCheckCache::new();

        let insert = { let before = CacheSnapshot::capture(&cache); cache.insert(&expr, type_.clone()); let got = cache.get(&expr).cloned(); CacheState::transition(CacheOperation::Insert, before, &cache).with_lookup(got, Some(type_.clone())) };
        let insert_report = CacheInvariantReport::from_state(&insert);
        assert_eq!(insert_report.checked, 3);
        assert!(insert_report.all_hold());

        let hit = { let before = CacheSnapshot::capture(&cache); let got = cache.get(&expr).cloned(); CacheState::transition(CacheOperation::Get, before, &cache).with_lookup(got, Some(type_.clone())) };
        assert!(verify_cache_contract(ContractSpec::Postcondition(CachePostcondition::GetReturnsInsertedValue), &hit).holds);
        assert!(verify_cache_contract(ContractSpec::MonotonicGrowth(MonotonicGrowth::GetHitIncrementsHits), &hit).holds);

        let miss_state = { let before = CacheSnapshot::capture(&cache); let got = cache.get(&miss).cloned(); CacheState::transition(CacheOperation::Get, before, &cache).with_lookup(got, None) };
        assert!(verify_cache_contract(ContractSpec::MonotonicGrowth(MonotonicGrowth::GetMissIncrementsMisses), &miss_state).holds);

        let same_env = { let before = CacheSnapshot::capture(&cache); cache.set_env_hash(0); let got = cache.get(&expr).cloned(); CacheState::transition(CacheOperation::SetEnvHash, before, &cache).with_requested_env_hash(0).with_lookup(got, Some(type_.clone())) };
        assert!(verify_cache_contract(ContractSpec::Precondition(CachePrecondition::SetEnvHashPreservesContentsWhenSame), &same_env).holds);

        let env_change = { let before = CacheSnapshot::capture(&cache); cache.set_env_hash(9); CacheState::transition(CacheOperation::SetEnvHash, before, &cache).with_requested_env_hash(9) };
        let env_report = CacheInvariantReport::from_state(&env_change);
        assert_eq!(env_report.checked, 2);
        assert!(env_report.all_hold());

        let mut mode_cache = TypeCheckCache::with_hashes(7, 3);
        mode_cache.insert(&expr, type_);
        let mode_change = { let before = CacheSnapshot::capture(&mode_cache); mode_cache.set_mode_hash(8); CacheState::transition(CacheOperation::SetModeHash, before, &mode_cache).with_requested_mode_hash(8) };
        let mode_report = CacheInvariantReport::from_state(&mode_change);
        assert_eq!(mode_report.checked, 2);
        assert!(mode_report.all_hold());
    }

    #[test]
    fn clear_stats_len_and_is_empty_contracts_hold() {
        let expr = key("Q");
        let mut cache = TypeCheckCache::with_hashes(17, 19);
        cache.insert(&expr, Expr::type_());
        let _ = cache.get(&expr);
        assert!(CacheInvariantReport::from_state(&CacheState::after(CacheOperation::Stats, &cache)).all_hold());
        assert!(CacheInvariantReport::from_state(&CacheState::after(CacheOperation::Len, &cache)).all_hold());
        assert!(CacheInvariantReport::from_state(&CacheState::after(CacheOperation::IsEmpty, &cache)).all_hold());
        let before = CacheSnapshot::capture(&cache);
        cache.clear();
        let clear = CacheInvariantReport::from_state(&CacheState::transition(CacheOperation::Clear, before, &cache));
        assert_eq!(clear.checked, 5);
        assert!(clear.all_hold(), "{clear:?}");
    }

    #[test]
    fn report_marks_broken_snapshots_as_failures() {
        let broken = CacheState {
            operation: CacheOperation::Clear,
            before: Some(CacheSnapshot { env_hash: 1, mode_hash: 2, len: 1, is_empty: false, hits: 4, misses: 5, entries: 1 }),
            after: CacheSnapshot { env_hash: 9, mode_hash: 7, len: 1, is_empty: false, hits: 3, misses: 2, entries: 1 },
            stats_observed: true,
            len_bound: INSERT_LEN_BOUND,
            ..CacheState::default()
        };
        let report = CacheInvariantReport::from_state(&broken);
        assert!(!report.all_hold());
        assert!(report.failed.contains(&"clear.empties_cache"));
        assert!(report.failed.contains(&"clear.preserves_env_hash"));
        assert!(report.failed.contains(&"clear.preserves_mode_hash"));
    }
}
