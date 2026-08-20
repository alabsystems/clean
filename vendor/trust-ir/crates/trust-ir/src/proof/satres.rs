// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! SAT-resolution certificate payload — the wire format a
//! [`ProofEvidence::CleanCic`](super::ProofEvidence::CleanCic) `term` carries
//! under the [`KERNEL_ANCHOR_TRUSTCG_LOWERING_RESOLUTION`] anchor (t-silicon
//! route 1: CNF-refutation assurance, kernel-re-checked through clean-kernel's
//! verified `Clean.Res.checkRefutes3` reflection checker). This payload is not
//! translation-validation authority by itself.
//!
//! # What the payload is
//!
//! A propositional refutation in exactly the shape the kernel checker
//! consumes:
//!
//! * `clauses` — the original CNF miter (global clause ids `0..n-1`), each
//!   literal a `(var, neg)` pair with 0-based variables.
//! * `steps` — a BINARY resolution chain; each step derives `resolvent` from
//!   the two premise clause ids `prem1`/`prem2` on `pivot_var`, and is
//!   assigned the next global id (`n`, `n+1`, ...). The chain refutes iff the
//!   final resolvent is empty.
//!
//! This is the data of `Clean.Res.checkRefutes3 (initialTrie cs) (listLen cs)
//! steps = Bool.true`; the trusted consumer (`trust_ir_build::validate`)
//! rebuilds the kernel term from THESE bytes and lets the `ck0` kernel decide.
//! Nothing here is trusted: a tampered payload merely reduces to `Bool.false`
//! in the kernel and the certificate is rejected.
//!
//! # Binding
//!
//! [`satres_formula`] pins the candidate obligation to the exact clause list via
//! [`clauses_digest`], so payload and formula cannot silently diverge. That is
//! not enough to discharge the obligation: both are producer-selected, and the
//! validator does not independently re-derive the exact miter from the named
//! lowering rule and Trust-IR machine semantics. Encoding fidelity is asserted
//! by the untrusted producer-side bit-blaster (trust-cg-verify `sat_blast`), even
//! when optional gate provenance is checked. Therefore replay proves only
//! UNSAT-of-this-clause-list and remains non-authoritative assurance.

use super::evidence::ProofDigest;
use super::obligations::ProofFormula;
use std::collections::BTreeSet;

/// One propositional literal: `(0-based variable, negated?)`. Matches the
/// clean-kernel `resolution_check` encoder convention (`Nat` literal
/// `2·var + neg`).
pub type SatLit = (u32, bool);

/// One binary resolution step in the global-id scheme of
/// `Clean.Res.checkRefutes3`: premise ids index `clauses ++ prior resolvents`.
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct SatResolutionStep {
    /// The claimed resolvent (checked by the kernel, set-equal, taut-free).
    pub resolvent: Vec<SatLit>,
    /// Global clause id of the premise holding the POSITIVE pivot (either
    /// orientation is accepted by the kernel's `checkStep3`).
    pub prem1: u32,
    /// Global clause id of the other premise.
    pub prem2: u32,
    /// The pivot VARIABLE (0-based; the kernel encodes it as the positive
    /// literal `2·pivot_var`).
    pub pivot_var: u32,
}

/// The full certificate payload: original clause list + binary resolution
/// refutation. Serialized into the `CleanCic` evidence's `term` bytes by
/// [`Self::to_bytes`]; the validator decodes with the strict
/// [`Self::from_bytes`].
#[derive(Debug, Clone, PartialEq, Eq, Default)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct SatResolutionCertPayload {
    /// Original CNF clauses, global ids `0..clauses.len()-1`.
    pub clauses: Vec<Vec<SatLit>>,
    /// Binary resolution chain, ids continuing at `clauses.len()`.
    pub steps: Vec<SatResolutionStep>,
}

/// Wire-format version magic for the payload byte encoding.
const MAGIC: &[u8; 14] = b"TIR-SATRES-v1\0";

/// Fail-closed decode caps. Adversarial payloads must not be able to make the
/// validator allocate unboundedly before the kernel ever runs.
const MAX_PAYLOAD_BYTES: usize = 64 * 1024 * 1024;
const MAX_CLAUSES: u32 = 1 << 20;
const MAX_STEPS: u32 = 1 << 22;
const MAX_LITS_PER_CLAUSE: u32 = 1 << 16;
const MAX_TOTAL_RECORDS: u32 = 1 << 20;
const MAX_TOTAL_LITERALS: u64 = 1 << 22;
/// Literal encoding is `2·var + neg`, so vars must fit `u32` after doubling.
const MAX_VAR: u32 = (u32::MAX >> 1) - 1;

/// Strict decode errors ([`SatResolutionCertPayload::from_bytes`] is
/// fail-closed: any anomaly rejects the whole payload).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SatResError {
    /// Missing/incorrect version magic.
    BadMagic,
    /// Input ended before the declared structure was complete.
    Truncated,
    /// Bytes remained after the declared structure — a smuggling channel,
    /// rejected.
    TrailingBytes(usize),
    /// A count exceeded its fail-closed cap.
    CapExceeded(&'static str),
    /// A variable id exceeded [`MAX_VAR`].
    VarOutOfRange(u32),
}

impl core::fmt::Display for SatResError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            SatResError::BadMagic => write!(f, "satres payload: bad or missing version magic"),
            SatResError::Truncated => write!(f, "satres payload: truncated"),
            SatResError::TrailingBytes(n) => {
                write!(f, "satres payload: {n} trailing byte(s) after structure")
            }
            SatResError::CapExceeded(what) => {
                write!(f, "satres payload: {what} exceeds the fail-closed cap")
            }
            SatResError::VarOutOfRange(v) => {
                write!(f, "satres payload: variable {v} out of encodable range")
            }
        }
    }
}

fn put_u32(out: &mut Vec<u8>, v: u32) {
    out.extend_from_slice(&v.to_le_bytes());
}

fn put_lits(out: &mut Vec<u8>, lits: &[SatLit]) {
    put_u32(out, lits.len() as u32);
    for &(var, neg) in lits {
        put_u32(out, var * 2 + u32::from(neg));
    }
}

struct Reader<'a> {
    bytes: &'a [u8],
    pos: usize,
    total_literals: u64,
}

impl<'a> Reader<'a> {
    fn remaining(&self) -> usize {
        self.bytes.len().saturating_sub(self.pos)
    }

    fn u32(&mut self) -> Result<u32, SatResError> {
        let end = self.pos.checked_add(4).ok_or(SatResError::Truncated)?;
        let slice = self
            .bytes
            .get(self.pos..end)
            .ok_or(SatResError::Truncated)?;
        self.pos = end;
        Ok(u32::from_le_bytes([slice[0], slice[1], slice[2], slice[3]]))
    }

    fn lits(&mut self, min_bytes_after: usize) -> Result<Vec<SatLit>, SatResError> {
        let n = self.u32()?;
        if n > MAX_LITS_PER_CLAUSE {
            return Err(SatResError::CapExceeded("literals per clause"));
        }
        self.total_literals = self
            .total_literals
            .checked_add(u64::from(n))
            .ok_or(SatResError::CapExceeded("total literals"))?;
        if self.total_literals > MAX_TOTAL_LITERALS {
            return Err(SatResError::CapExceeded("total literals"));
        }

        // Prove the claimed literal body and the minimum remaining structure
        // are physically present before reserving attacker-selected capacity.
        let required = (n as usize)
            .checked_mul(4)
            .and_then(|literal_bytes| literal_bytes.checked_add(min_bytes_after))
            .ok_or(SatResError::Truncated)?;
        if self.remaining() < required {
            return Err(SatResError::Truncated);
        }
        let mut lits = Vec::with_capacity(n as usize);
        for _ in 0..n {
            let enc = self.u32()?;
            let var = enc >> 1;
            if var > MAX_VAR {
                return Err(SatResError::VarOutOfRange(var));
            }
            lits.push((var, enc & 1 == 1));
        }
        Ok(lits)
    }
}

impl SatResolutionCertPayload {
    /// Serialize validated producer data to the versioned `term` byte format.
    ///
    /// Prefer [`Self::try_to_bytes`] for any data not already known to satisfy
    /// the carrier caps. This compatibility convenience panics instead of
    /// silently truncating counts or wrapping variables.
    #[must_use]
    pub fn to_bytes(&self) -> Vec<u8> {
        self.try_to_bytes()
            .expect("SAT-resolution payload exceeds carrier limits")
    }

    /// Fallible, cap-checked encoding. This applies the same aggregate and
    /// per-record limits as [`Self::from_bytes`] before allocating or casting
    /// counts to the wire's `u32` fields.
    pub fn try_to_bytes(&self) -> Result<Vec<u8>, SatResError> {
        let n_clauses = u32::try_from(self.clauses.len())
            .map_err(|_| SatResError::CapExceeded("clause count"))?;
        let n_steps =
            u32::try_from(self.steps.len()).map_err(|_| SatResError::CapExceeded("step count"))?;
        if n_clauses > MAX_CLAUSES {
            return Err(SatResError::CapExceeded("clause count"));
        }
        if n_steps > MAX_STEPS {
            return Err(SatResError::CapExceeded("step count"));
        }
        if n_clauses
            .checked_add(n_steps)
            .is_none_or(|records| records > MAX_TOTAL_RECORDS)
        {
            return Err(SatResError::CapExceeded("total records"));
        }

        let mut total_literals = 0_u64;
        let mut encoded_len = MAGIC.len() + 8; // clause count + step count
        for lits in self
            .clauses
            .iter()
            .chain(self.steps.iter().map(|step| &step.resolvent))
        {
            let count = u32::try_from(lits.len())
                .map_err(|_| SatResError::CapExceeded("literals per clause"))?;
            if count > MAX_LITS_PER_CLAUSE {
                return Err(SatResError::CapExceeded("literals per clause"));
            }
            total_literals = total_literals
                .checked_add(u64::from(count))
                .ok_or(SatResError::CapExceeded("total literals"))?;
            if total_literals > MAX_TOTAL_LITERALS {
                return Err(SatResError::CapExceeded("total literals"));
            }
            if let Some(&(var, _)) = lits.iter().find(|(var, _)| *var > MAX_VAR) {
                return Err(SatResError::VarOutOfRange(var));
            }
            encoded_len = encoded_len
                .checked_add(4)
                .and_then(|len| len.checked_add(lits.len().checked_mul(4)?))
                .ok_or(SatResError::CapExceeded("payload bytes"))?;
        }
        // Each step adds the three fixed u32 fields beyond its resolvent.
        encoded_len = encoded_len
            .checked_add(
                self.steps
                    .len()
                    .checked_mul(12)
                    .ok_or(SatResError::CapExceeded("payload bytes"))?,
            )
            .ok_or(SatResError::CapExceeded("payload bytes"))?;
        if encoded_len > MAX_PAYLOAD_BYTES {
            return Err(SatResError::CapExceeded("payload bytes"));
        }
        if let Some(step) = self.steps.iter().find(|step| step.pivot_var > MAX_VAR) {
            return Err(SatResError::VarOutOfRange(step.pivot_var));
        }

        let mut out = Vec::with_capacity(encoded_len);
        out.extend_from_slice(MAGIC);
        put_u32(&mut out, n_clauses);
        for clause in &self.clauses {
            put_lits(&mut out, clause);
        }
        put_u32(&mut out, n_steps);
        for step in &self.steps {
            put_lits(&mut out, &step.resolvent);
            put_u32(&mut out, step.prem1);
            put_u32(&mut out, step.prem2);
            put_u32(&mut out, step.pivot_var);
        }
        debug_assert_eq!(out.len(), encoded_len);
        Ok(out)
    }

    /// Strict, fail-closed decode: bad magic, truncation, trailing bytes,
    /// over-cap counts, and out-of-range variables all reject.
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, SatResError> {
        if bytes.len() > MAX_PAYLOAD_BYTES {
            return Err(SatResError::CapExceeded("payload bytes"));
        }
        let rest = bytes
            .strip_prefix(MAGIC.as_slice())
            .ok_or(SatResError::BadMagic)?;
        let mut r = Reader {
            bytes: rest,
            pos: 0,
            total_literals: 0,
        };

        let n_clauses = r.u32()?;
        if n_clauses > MAX_CLAUSES {
            return Err(SatResError::CapExceeded("clause count"));
        }
        if n_clauses > MAX_TOTAL_RECORDS {
            return Err(SatResError::CapExceeded("total records"));
        }
        // Every clause needs at least its literal-count word, followed by the
        // step-count word. Reject impossible outer counts before allocation.
        let minimum_clause_section = (n_clauses as usize)
            .checked_mul(4)
            .and_then(|bytes| bytes.checked_add(4))
            .ok_or(SatResError::Truncated)?;
        if r.remaining() < minimum_clause_section {
            return Err(SatResError::Truncated);
        }
        let mut clauses = Vec::with_capacity(n_clauses as usize);
        for clause_index in 0..n_clauses {
            let remaining_clauses = (n_clauses - clause_index - 1) as usize;
            let min_bytes_after = remaining_clauses
                .checked_mul(4)
                .and_then(|bytes| bytes.checked_add(4))
                .ok_or(SatResError::Truncated)?;
            clauses.push(r.lits(min_bytes_after)?);
        }

        let n_steps = r.u32()?;
        if n_steps > MAX_STEPS {
            return Err(SatResError::CapExceeded("step count"));
        }
        if n_clauses
            .checked_add(n_steps)
            .is_none_or(|records| records > MAX_TOTAL_RECORDS)
        {
            return Err(SatResError::CapExceeded("total records"));
        }
        // One step is at least: empty-resolvent count + three u32 fields.
        let minimum_step_section = (n_steps as usize)
            .checked_mul(16)
            .ok_or(SatResError::Truncated)?;
        if r.remaining() < minimum_step_section {
            return Err(SatResError::Truncated);
        }
        let mut steps = Vec::with_capacity(n_steps as usize);
        for step_index in 0..n_steps {
            let remaining_steps = (n_steps - step_index - 1) as usize;
            let min_bytes_after = remaining_steps
                .checked_mul(16)
                .and_then(|bytes| bytes.checked_add(12))
                .ok_or(SatResError::Truncated)?;
            let resolvent = r.lits(min_bytes_after)?;
            let prem1 = r.u32()?;
            let prem2 = r.u32()?;
            let pivot_var = r.u32()?;
            if pivot_var > MAX_VAR {
                return Err(SatResError::VarOutOfRange(pivot_var));
            }
            steps.push(SatResolutionStep {
                resolvent,
                prem1,
                prem2,
                pivot_var,
            });
        }

        if r.pos != rest.len() {
            return Err(SatResError::TrailingBytes(rest.len() - r.pos));
        }
        Ok(SatResolutionCertPayload { clauses, steps })
    }
}

/// Replay the binary resolution chain in pure Rust. This is a small trusted
/// validator capability for kernel-less consumers of `SmtProof`; it checks the
/// same clause/pivot/resolvent relation encoded for the Clean reflection path.
#[must_use]
pub fn replay_resolution(payload: &SatResolutionCertPayload) -> bool {
    fn clause_set(clause: &[SatLit]) -> Option<BTreeSet<SatLit>> {
        let set: BTreeSet<SatLit> = clause.iter().copied().collect();
        if set.iter().any(|(var, neg)| set.contains(&(*var, !*neg))) {
            return None;
        }
        Some(set)
    }

    let mut database: Vec<BTreeSet<SatLit>> =
        Vec::with_capacity(payload.clauses.len().saturating_add(payload.steps.len()));
    for clause in &payload.clauses {
        let Some(clause) = clause_set(clause) else {
            return false;
        };
        database.push(clause);
    }

    for step in &payload.steps {
        let Some(left) = database.get(step.prem1 as usize) else {
            return false;
        };
        let Some(right) = database.get(step.prem2 as usize) else {
            return false;
        };
        let positive = (step.pivot_var, false);
        let negative = (step.pivot_var, true);
        let oriented = (left.contains(&positive) && right.contains(&negative))
            || (left.contains(&negative) && right.contains(&positive));
        if !oriented {
            return false;
        }
        let mut expected: BTreeSet<SatLit> = left.union(right).copied().collect();
        expected.remove(&positive);
        expected.remove(&negative);
        if expected
            .iter()
            .any(|(var, neg)| expected.contains(&(*var, !*neg)))
        {
            return false;
        }
        let Some(claimed) = clause_set(&step.resolvent) else {
            return false;
        };
        if claimed != expected {
            return false;
        }
        database.push(claimed);
    }

    payload
        .steps
        .last()
        .is_some_and(|step| step.resolvent.is_empty())
}

/// Deterministic digest of the ORIGINAL clause list alone (the CNF the
/// kernel's `Unsat cs` conclusion is about). Bound into the obligation's
/// [`ProofFormula`] by [`satres_formula`] so a certificate's decoded payload
/// can be checked against the obligation's own claim.
#[must_use]
pub fn clauses_digest(clauses: &[Vec<SatLit>]) -> ProofDigest {
    let mut bytes = Vec::new();
    bytes.extend_from_slice(
        &u64::try_from(clauses.len())
            .expect("clause count exceeds canonical u64 framing")
            .to_le_bytes(),
    );
    for clause in clauses {
        bytes.extend_from_slice(
            &u64::try_from(clause.len())
                .expect("clause length exceeds canonical u64 framing")
                .to_le_bytes(),
        );
        for &(var, negated) in clause {
            bytes.extend_from_slice(&var.to_le_bytes());
            bytes.push(u8::from(negated));
        }
    }
    ProofDigest::sha256_domain("trust_ir.proof.satres.cnf.v2", &bytes)
}

/// Schema identifier for [`ProofFormula`]s carrying a SAT-refutation claim.
pub const SATRES_FORMULA_SCHEMA: &str = "trust-ir.satres.cnf.v2";

/// The ONE kernel theorem name a lowering-resolution recheck directive may
/// cite: the per-certificate ground theorem
/// `cert_unsat : Clean.Res.Unsat cs := Clean.Res.checkRefutes3_sound cs steps
/// (Eq.refl Bool Bool.true)`, registered by the validator into the anchor
/// environment FROM THE PAYLOAD (never from producer-supplied terms) and then
/// kernel-re-checked. The validator rejects any other citation set.
pub const SATRES_CERT_UNSAT_THEOREM: &str = "TrustCg.LoweringRes.cert_unsat";

/// Build the [`ProofFormula`] for a lowering-rule SAT-refutation obligation:
/// the payload names the lowering rule and pins the exact clause list by
/// digest. Returns `None` if `rule_name` contains a newline (the payload's
/// field separator — fail-closed rather than escaped).
#[must_use]
pub fn satres_formula(rule_name: &str, clauses: &[Vec<SatLit>]) -> Option<ProofFormula> {
    if rule_name.contains('\n') || rule_name.is_empty() {
        return None;
    }
    Some(ProofFormula {
        schema: SATRES_FORMULA_SCHEMA.to_string(),
        payload: format!("rule={rule_name}\ncnf={}", clauses_digest(clauses)),
        smtlib: None,
        sort: None,
    })
}

/// Strict parse of a [`satres_formula`] payload back into
/// `(rule_name, cnf_digest_string)`. `None` on any shape violation or schema
/// mismatch — callers treat that as fail-closed.
#[must_use]
pub fn satres_formula_parts(formula: &ProofFormula) -> Option<(&str, &str)> {
    if formula.schema != SATRES_FORMULA_SCHEMA {
        return None;
    }
    let (rule_part, cnf_part) = formula.payload.split_once('\n')?;
    let rule = rule_part.strip_prefix("rule=")?;
    let digest = cnf_part.strip_prefix("cnf=")?;
    if rule.is_empty() || digest.is_empty() || cnf_part.contains('\n') {
        return None;
    }
    Some((rule, digest))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sample() -> SatResolutionCertPayload {
        SatResolutionCertPayload {
            clauses: vec![vec![(0, false)], vec![(0, true)]],
            steps: vec![SatResolutionStep {
                resolvent: vec![],
                prem1: 0,
                prem2: 1,
                pivot_var: 0,
            }],
        }
    }

    #[test]
    fn roundtrip() {
        let payload = sample();
        let bytes = payload.to_bytes();
        assert_eq!(
            SatResolutionCertPayload::from_bytes(&bytes),
            Ok(payload),
            "payload must roundtrip byte-exactly"
        );
    }

    #[test]
    fn rust_resolution_replay_accepts_exact_chain_and_rejects_forgery() {
        let payload = sample();
        assert!(replay_resolution(&payload));

        let mut forged = payload.clone();
        forged.steps[0].resolvent.push((1, false));
        assert!(!replay_resolution(&forged));
    }

    #[test]
    fn strict_decode_rejects_anomalies() {
        let bytes = sample().to_bytes();

        // Bad magic.
        let mut bad = bytes.clone();
        bad[0] ^= 0xff;
        assert_eq!(
            SatResolutionCertPayload::from_bytes(&bad),
            Err(SatResError::BadMagic)
        );

        // Truncation at every prefix length must reject, never panic.
        for cut in 0..bytes.len() {
            assert!(
                SatResolutionCertPayload::from_bytes(&bytes[..cut]).is_err(),
                "prefix of {cut} bytes must be rejected"
            );
        }

        // Trailing garbage.
        let mut trailing = bytes.clone();
        trailing.push(0);
        assert_eq!(
            SatResolutionCertPayload::from_bytes(&trailing),
            Err(SatResError::TrailingBytes(1))
        );

        // Pivot variables feed the kernel literal encoder too; they obey the
        // same doubling bound as clause/resolvent variables.
        let mut bad_pivot = bytes.clone();
        let end = bad_pivot.len();
        bad_pivot[end - 4..].copy_from_slice(&(MAX_VAR + 1).to_le_bytes());
        assert_eq!(
            SatResolutionCertPayload::from_bytes(&bad_pivot),
            Err(SatResError::VarOutOfRange(MAX_VAR + 1))
        );

        // Over-cap clause count.
        let mut over = MAGIC.to_vec();
        over.extend_from_slice(&(MAX_CLAUSES + 1).to_le_bytes());
        assert_eq!(
            SatResolutionCertPayload::from_bytes(&over),
            Err(SatResError::CapExceeded("clause count"))
        );

        // A physically tiny payload may not trigger a huge outer allocation
        // merely by claiming millions of records.
        let mut impossible_steps = MAGIC.to_vec();
        impossible_steps.extend_from_slice(&0_u32.to_le_bytes());
        impossible_steps.extend_from_slice(&MAX_TOTAL_RECORDS.to_le_bytes());
        assert_eq!(
            SatResolutionCertPayload::from_bytes(&impossible_steps),
            Err(SatResError::Truncated)
        );

        // Likewise, a per-clause count is checked against remaining bytes
        // before reserving its vector capacity.
        let mut impossible_literals = MAGIC.to_vec();
        impossible_literals.extend_from_slice(&1_u32.to_le_bytes());
        impossible_literals.extend_from_slice(&MAX_LITS_PER_CLAUSE.to_le_bytes());
        impossible_literals.extend_from_slice(&0_u32.to_le_bytes());
        assert_eq!(
            SatResolutionCertPayload::from_bytes(&impossible_literals),
            Err(SatResError::Truncated)
        );
    }

    #[test]
    fn strict_decode_enforces_aggregate_literal_budget_before_allocation() {
        let one_literal = [1_u32.to_le_bytes(), 0_u32.to_le_bytes()].concat();
        let mut reader = Reader {
            bytes: &one_literal,
            pos: 0,
            total_literals: MAX_TOTAL_LITERALS,
        };
        assert_eq!(
            reader.lits(0),
            Err(SatResError::CapExceeded("total literals"))
        );
    }

    #[test]
    fn checked_encoder_rejects_unencodable_shapes() {
        let mut bad_pivot = sample();
        bad_pivot.steps[0].pivot_var = MAX_VAR + 1;
        assert_eq!(
            bad_pivot.try_to_bytes(),
            Err(SatResError::VarOutOfRange(MAX_VAR + 1))
        );

        let too_many = SatResolutionCertPayload {
            clauses: vec![vec![(0, false); (MAX_LITS_PER_CLAUSE + 1) as usize]],
            steps: vec![],
        };
        assert_eq!(
            too_many.try_to_bytes(),
            Err(SatResError::CapExceeded("literals per clause"))
        );
    }

    #[test]
    fn digest_is_clause_sensitive_and_step_insensitive() {
        let payload = sample();
        let d1 = clauses_digest(&payload.clauses);

        let mut other_clauses = payload.clauses.clone();
        other_clauses[0][0].1 = true;
        assert_ne!(
            d1,
            clauses_digest(&other_clauses),
            "flipping a clause literal must change the digest"
        );

        // The digest binds the CLAIM (the clause list), not the refutation.
        let d_again = clauses_digest(&payload.clauses);
        assert_eq!(d1, d_again, "digest must be deterministic");
    }

    #[test]
    fn formula_roundtrip_and_strictness() {
        let payload = sample();
        let formula = satres_formula("Iadd_I8 -> ADD (8-bit)", &payload.clauses).expect("formula");
        let (rule, digest) = satres_formula_parts(&formula).expect("parse");
        assert_eq!(rule, "Iadd_I8 -> ADD (8-bit)");
        assert_eq!(digest, clauses_digest(&payload.clauses).to_string());

        // Newline in the rule name is rejected, not escaped.
        assert!(satres_formula("evil\nrule", &payload.clauses).is_none());

        // Wrong schema fails the parse.
        let mut wrong = formula.clone();
        wrong.schema = "something-else".to_string();
        assert!(satres_formula_parts(&wrong).is_none());

        // Smuggled third line fails the parse.
        let mut smuggled = formula;
        smuggled.payload.push_str("\nextra=1");
        assert!(satres_formula_parts(&smuggled).is_none());
    }
}
