// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Structured clause PROVENANCE for a t-silicon lowering miter — the
//! encoding-fidelity audit surface carried in the certificate context.
//!
//! # What this is (and what it is not)
//!
//! The [`KERNEL_ANCHOR_TRUSTCG_LOWERING_RESOLUTION`](super::KERNEL_ANCHOR_TRUSTCG_LOWERING_RESOLUTION)
//! cert lets the `ck0` kernel certify **UNSAT of a clause list**
//! ([`super::satres`]). That leaves ONE named boundary open: is the clause list
//! actually the lowering rule's equivalence miter, or some other UNSAT instance
//! smuggled in? This module makes that boundary *structured and checkable*
//! instead of merely asserted, mirroring `ay-proof`'s `BvBlastProof` provenance
//! model (clause ↔ the gate it encodes):
//!
//!   * The untrusted producer (`trust-cg-verify::sat_blast`) records, for every
//!     clause it emits, the NAMED gate it is the CNF of, and serializes that as
//!     a [`MiterProvenance`] (the `satprov1` text form).
//!   * [`MiterProvenance::validate`] re-derives each gate's clause set from the
//!     gate's own truth table ([`canonical_gate_clauses`]) and confirms the
//!     miter's clause list is EXACTLY `⋃ gate-CNFs ∪ {disequality}`, and that
//!     the disequality compares the two sides bit-for-bit. So a reviewer — or
//!     this validator — can audit that the clause list is the rule's miter, not
//!     an arbitrary UNSAT problem.
//!
//! # What remains trusted (the residual boundary, stated honestly)
//!
//! `validate` proves *the clause list is the Tseitin miter of THESE gates,
//! compared bit-for-bit*. It does NOT prove that the recorded gate DAG faithfully
//! bit-blasts the rule's `SmtExpr` sides (that `blast(trust_ir_expr)` and
//! `blast(aarch64_expr)` compute the source/machine semantics). That
//! gate-DAG⇔SmtExpr correspondence is asserted by the untrusted blaster and is
//! NOT machine-checked here. The kernel still certifies UNSAT only; provenance
//! validation is a producer-side (untrusted) fidelity check, carried in the
//! cert for audit — it does not enter the `ck0` trusted base and cannot mint a
//! `Certified` translation-validation obligation.

use super::evidence::ProofDigest;
use super::satres::SatLit;
use std::collections::BTreeMap;

/// Which half of the miter a gate belongs to.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum MiterSide {
    /// A gate of the trust_ir (source) side.
    Ir,
    /// A gate of the machine (AArch64) side.
    Machine,
    /// A per-bit comparison gate (`ir_bit XOR machine_bit`).
    Diff,
}

impl MiterSide {
    /// Stable text tag (must match `trust-cg-verify::sat_blast::MiterSide::tag`).
    #[must_use]
    pub const fn tag(self) -> &'static str {
        match self {
            MiterSide::Ir => "ir",
            MiterSide::Machine => "mc",
            MiterSide::Diff => "diff",
        }
    }

    fn parse(s: &str) -> Option<Self> {
        match s {
            "ir" => Some(MiterSide::Ir),
            "mc" => Some(MiterSide::Machine),
            "diff" => Some(MiterSide::Diff),
            _ => None,
        }
    }
}

/// The Boolean gate a [`GateRecord`] names. The CNF each gate contributes is
/// [`canonical_gate_clauses`]; the truth table is [`GateKind::eval`]. This is a
/// byte-identical mirror of `trust-cg-verify::sat_blast::GateKind` — the two are
/// the CONTRACT the `satprov1` text serialization rides.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum GateKind {
    /// `out = in0 XOR in1`.
    Xor2,
    /// `out = in0 XOR in1 XOR in2` (full-adder sum).
    Xor3,
    /// `out = in0 AND in1`.
    And2,
    /// `out = MAJ(in0, in1, in2)` (full-adder carry).
    Maj3,
}

impl GateKind {
    /// Stable text tag.
    #[must_use]
    pub const fn tag(self) -> &'static str {
        match self {
            GateKind::Xor2 => "xor2",
            GateKind::Xor3 => "xor3",
            GateKind::And2 => "and2",
            GateKind::Maj3 => "maj3",
        }
    }

    fn parse(s: &str) -> Option<Self> {
        match s {
            "xor2" => Some(GateKind::Xor2),
            "xor3" => Some(GateKind::Xor3),
            "and2" => Some(GateKind::And2),
            "maj3" => Some(GateKind::Maj3),
            _ => None,
        }
    }

    /// Number of input literals this gate takes.
    #[must_use]
    pub const fn arity(self) -> usize {
        match self {
            GateKind::Xor2 | GateKind::And2 => 2,
            GateKind::Xor3 | GateKind::Maj3 => 3,
        }
    }

    /// The gate's truth table over its (polarity-resolved) input bits.
    #[must_use]
    pub fn eval(self, ins: &[bool]) -> bool {
        match self {
            GateKind::Xor2 => ins[0] ^ ins[1],
            GateKind::Xor3 => ins[0] ^ ins[1] ^ ins[2],
            GateKind::And2 => ins[0] && ins[1],
            GateKind::Maj3 => (ins[0] && ins[1]) || (ins[0] && ins[2]) || (ins[1] && ins[2]),
        }
    }
}

/// One recorded gate: `out = kind(ins...)` over SIGNED DIMACS literals (1-based
/// variables; `out` positive, `ins` possibly negated).
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct GateRecord {
    /// Which side of the miter the gate belongs to.
    pub side: MiterSide,
    /// The Boolean relation.
    pub kind: GateKind,
    /// Defined output literal (positive).
    pub out: i32,
    /// Ordered input literals (signed; length == `kind.arity()`).
    pub ins: Vec<i32>,
}

/// The structured provenance of a blasted miter. Serialized to the `satprov1`
/// text form by the producer ([`MiterProvenance::to_text`]) and re-checked
/// against the certificate payload's clause list by [`MiterProvenance::validate`].
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct MiterProvenance {
    /// The lowering rule this miter came from.
    pub rule_name: String,
    /// Output bit width of both sides.
    pub width: u32,
    /// Highest DIMACS variable in use.
    pub num_vars: u32,
    /// Declared inputs: `(name, var ids LSB-first)`.
    pub inputs: Vec<(String, Vec<u32>)>,
    /// Every clause-emitting gate, in emission order.
    pub gates: Vec<GateRecord>,
    /// The trust_ir side's output literals (LSB-first).
    pub ir_out: Vec<i32>,
    /// The machine side's output literals (LSB-first).
    pub machine_out: Vec<i32>,
    /// The per-bit diff literals fed into the disequality clause.
    pub diff: Vec<i32>,
}

/// The EXACT (compact) CNF a gate contributes, parameterized by signed literals.
/// Byte-identical to `trust-cg-verify::sat_blast::canonical_gate_clauses`; this
/// is the single source of gate CNF the [`MiterProvenance::validate`] multiset
/// check re-derives from.
///
/// # Panics
/// If `ins.len() != kind.arity()`.
#[must_use]
pub fn canonical_gate_clauses(kind: GateKind, out: i32, ins: &[i32]) -> Vec<Vec<i32>> {
    assert_eq!(ins.len(), kind.arity(), "gate arity mismatch");
    let o = out;
    match kind {
        GateKind::Xor2 => {
            let (a, b) = (ins[0], ins[1]);
            vec![
                vec![-a, -b, -o],
                vec![a, b, -o],
                vec![-a, b, o],
                vec![a, -b, o],
            ]
        }
        GateKind::Xor3 => {
            // Full-adder sum `o <-> a XOR b XOR c` (see the sat_blast note on the
            // corrected `so` sign — this matches the producer exactly).
            let (a, b, c) = (ins[0], ins[1], ins[2]);
            let mut v = Vec::with_capacity(8);
            for sa in [1i32, -1] {
                for sb in [1i32, -1] {
                    for sc in [1i32, -1] {
                        let parity = (sa < 0) ^ (sb < 0) ^ (sc < 0);
                        let so = if parity { -1 } else { 1 };
                        v.push(vec![-sa * a, -sb * b, -sc * c, so * o]);
                    }
                }
            }
            v
        }
        GateKind::And2 => {
            let (a, b) = (ins[0], ins[1]);
            vec![vec![-a, -b, o], vec![a, -o], vec![b, -o]]
        }
        GateKind::Maj3 => {
            let (a, b, c) = (ins[0], ins[1], ins[2]);
            vec![
                vec![-a, -b, o],
                vec![-a, -c, o],
                vec![-b, -c, o],
                vec![a, b, -o],
                vec![a, c, -o],
                vec![b, c, -o],
            ]
        }
    }
}

/// True iff `clause` is a logical CONSEQUENCE of the gate relation
/// `out = kind(ins...)`. Used by tests to confirm [`canonical_gate_clauses`] is
/// a genuine gate encoding (non-vacuous), mirroring the producer's check.
#[must_use]
pub fn clause_entailed_by_gate(clause: &[i32], kind: GateKind, out: i32, ins: &[i32]) -> bool {
    if ins.len() != kind.arity() {
        return false;
    }
    let mut vars: Vec<i32> = Vec::new();
    for &l in std::iter::once(&out).chain(ins.iter()) {
        let v = l.abs();
        if !vars.contains(&v) {
            vars.push(v);
        }
    }
    if clause.iter().any(|l| !vars.contains(&l.abs())) {
        return false;
    }
    let k = vars.len();
    for mask in 0u32..(1u32 << k) {
        let val = |lit: i32| -> bool {
            let idx = vars.iter().position(|&v| v == lit.abs()).expect("gate var");
            let bit = mask & (1 << idx) != 0;
            if lit > 0 { bit } else { !bit }
        };
        let in_vals: Vec<bool> = ins.iter().map(|&l| val(l)).collect();
        if val(out) != kind.eval(&in_vals) {
            continue;
        }
        if !clause.iter().any(|&l| val(l)) {
            return false;
        }
    }
    true
}

/// Errors from parsing or validating a [`MiterProvenance`]. Fail-closed: any
/// anomaly rejects the whole provenance.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SatProvError {
    /// The `satprov1` text is malformed (bad header, field, or token).
    BadText(String),
    /// A gate's input arity disagrees with its kind.
    BadArity {
        /// Gate index.
        gate: usize,
    },
    /// A literal references a variable outside `1..=num_vars`.
    VarOutOfRange(i32),
    /// `ir_out` / `machine_out` / `diff` lengths disagree with `width`.
    ShapeMismatch(String),
    /// A `Diff` gate is not `Xor2(ir_out[i], machine_out[i])`.
    DiffGateMismatch {
        /// Output bit position.
        bit: usize,
    },
    /// The clause list is not exactly `⋃ gate-CNFs ∪ {disequality}` — a clause
    /// is missing, extra, or does not match any recorded gate.
    ClauseSetMismatch {
        /// How many payload clauses were unaccounted-for by the provenance.
        payload_unmatched: usize,
        /// How many provenance clauses were missing from the payload.
        provenance_unmatched: usize,
    },
    /// The provenance's `rule_name` disagrees with the expected rule.
    RuleNameMismatch {
        /// The rule the provenance claims.
        got: String,
        /// The rule expected.
        expected: String,
    },
}

impl core::fmt::Display for SatProvError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            SatProvError::BadText(m) => write!(f, "satprov: malformed text: {m}"),
            SatProvError::BadArity { gate } => write!(f, "satprov: gate {gate} arity mismatch"),
            SatProvError::VarOutOfRange(v) => write!(f, "satprov: variable {v} out of range"),
            SatProvError::ShapeMismatch(m) => write!(f, "satprov: {m}"),
            SatProvError::DiffGateMismatch { bit } => {
                write!(
                    f,
                    "satprov: diff bit {bit} is not Xor2(ir_out, machine_out)"
                )
            }
            SatProvError::ClauseSetMismatch {
                payload_unmatched,
                provenance_unmatched,
            } => write!(
                f,
                "satprov: clause list is not the recorded miter \
                 ({payload_unmatched} payload clause(s) unaccounted-for, \
                 {provenance_unmatched} provenance clause(s) missing)"
            ),
            SatProvError::RuleNameMismatch { got, expected } => {
                write!(f, "satprov: rule name '{got}' != expected '{expected}'")
            }
        }
    }
}

/// Canonical, order-insensitive form of a clause: literals sorted, as `i64`.
fn canon_clause(lits: &[i32]) -> Vec<i64> {
    let mut v: Vec<i64> = lits.iter().map(|&l| i64::from(l)).collect();
    v.sort_unstable();
    v
}

/// 1-based signed DIMACS literal for a 0-based [`SatLit`] (matches
/// `trust_ir_build::satcert`).
fn satlit_to_dimacs((var, neg): SatLit) -> i64 {
    let v = i64::from(var) + 1;
    if neg { -v } else { v }
}

impl MiterProvenance {
    /// Serialize to the deterministic `satprov1` text form (see the producer's
    /// `MiterProvenance::to_text` for the grammar). `None` if the rule name
    /// contains a newline.
    #[must_use]
    pub fn to_text(&self) -> Option<String> {
        use std::fmt::Write as _;
        if self.rule_name.contains('\n') {
            return None;
        }
        let mut out = String::new();
        let _ = writeln!(out, "satprov1");
        let _ = writeln!(out, "rule {}", self.rule_name);
        let _ = writeln!(out, "width {}", self.width);
        let _ = writeln!(out, "vars {}", self.num_vars);
        for (name, ids) in &self.inputs {
            let _ = write!(out, "input {name}");
            for id in ids {
                let _ = write!(out, " {id}");
            }
            let _ = writeln!(out);
        }
        for g in &self.gates {
            let _ = write!(out, "gate {} {} {}", g.side.tag(), g.kind.tag(), g.out);
            for i in &g.ins {
                let _ = write!(out, " {i}");
            }
            let _ = writeln!(out);
        }
        let mut lits = |tag: &str, ls: &[i32]| {
            let _ = write!(out, "{tag}");
            for l in ls {
                let _ = write!(out, " {l}");
            }
            let _ = writeln!(out);
        };
        lits("irout", &self.ir_out);
        lits("mcout", &self.machine_out);
        lits("diff", &self.diff);
        Some(out)
    }

    /// Parse the `satprov1` text form. Strict / fail-closed.
    pub fn parse(text: &str) -> Result<Self, SatProvError> {
        let mut lines = text.lines();
        let header = lines.next().unwrap_or_default().trim();
        if header != "satprov1" {
            return Err(SatProvError::BadText(format!("bad header '{header}'")));
        }
        let mut rule_name: Option<String> = None;
        let mut width: Option<u32> = None;
        let mut num_vars: Option<u32> = None;
        let mut inputs: Vec<(String, Vec<u32>)> = Vec::new();
        let mut gates: Vec<GateRecord> = Vec::new();
        let mut ir_out: Option<Vec<i32>> = None;
        let mut machine_out: Option<Vec<i32>> = None;
        let mut diff: Option<Vec<i32>> = None;

        let parse_u32 = |s: &str| -> Result<u32, SatProvError> {
            s.parse::<u32>()
                .map_err(|_| SatProvError::BadText(format!("expected u32, got '{s}'")))
        };
        let parse_i32s = |it: &[&str]| -> Result<Vec<i32>, SatProvError> {
            it.iter()
                .map(|t| {
                    t.parse::<i32>()
                        .map_err(|_| SatProvError::BadText(format!("expected i32, got '{t}'")))
                })
                .collect()
        };

        for line in lines {
            let toks: Vec<&str> = line.split_whitespace().collect();
            match toks.split_first() {
                None => continue,
                Some((&"rule", _rest)) => {
                    // The rule name is the remainder verbatim (may contain spaces).
                    let idx = line.find("rule").expect("tag present") + "rule".len();
                    rule_name = Some(line[idx..].trim().to_string());
                }
                Some((&"width", rest)) => {
                    width = Some(parse_u32(rest.first().copied().unwrap_or(""))?);
                }
                Some((&"vars", rest)) => {
                    num_vars = Some(parse_u32(rest.first().copied().unwrap_or(""))?);
                }
                Some((&"input", rest)) => {
                    let (name, ids) = rest
                        .split_first()
                        .ok_or_else(|| SatProvError::BadText("input line missing name".into()))?;
                    let ids = ids
                        .iter()
                        .map(|t| parse_u32(t))
                        .collect::<Result<Vec<u32>, _>>()?;
                    inputs.push(((*name).to_string(), ids));
                }
                Some((&"gate", rest)) => {
                    if rest.len() < 3 {
                        return Err(SatProvError::BadText("gate line too short".into()));
                    }
                    let side = MiterSide::parse(rest[0])
                        .ok_or_else(|| SatProvError::BadText(format!("bad side '{}'", rest[0])))?;
                    let kind = GateKind::parse(rest[1])
                        .ok_or_else(|| SatProvError::BadText(format!("bad kind '{}'", rest[1])))?;
                    let out = parse_i32s(&rest[2..3])?[0];
                    let ins = parse_i32s(&rest[3..])?;
                    gates.push(GateRecord {
                        side,
                        kind,
                        out,
                        ins,
                    });
                }
                Some((&"irout", rest)) => ir_out = Some(parse_i32s(rest)?),
                Some((&"mcout", rest)) => machine_out = Some(parse_i32s(rest)?),
                Some((&"diff", rest)) => diff = Some(parse_i32s(rest)?),
                Some((tag, _)) => {
                    return Err(SatProvError::BadText(format!("unknown line tag '{tag}'")));
                }
            }
        }

        Ok(MiterProvenance {
            rule_name: rule_name.ok_or_else(|| SatProvError::BadText("missing rule".into()))?,
            width: width.ok_or_else(|| SatProvError::BadText("missing width".into()))?,
            num_vars: num_vars.ok_or_else(|| SatProvError::BadText("missing vars".into()))?,
            inputs,
            gates,
            ir_out: ir_out.ok_or_else(|| SatProvError::BadText("missing irout".into()))?,
            machine_out: machine_out
                .ok_or_else(|| SatProvError::BadText("missing mcout".into()))?,
            diff: diff.ok_or_else(|| SatProvError::BadText("missing diff".into()))?,
        })
    }

    /// A deterministic digest over the canonical text form, for binding the
    /// carried provenance to the certificate.
    #[must_use]
    pub fn digest(&self) -> Option<ProofDigest> {
        let text = self.to_text()?;
        Some(ProofDigest::sha256_domain(
            "trust_ir.proof.satprov.v2",
            text.as_bytes(),
        ))
    }

    /// Structurally validate the provenance AGAINST a clause list: confirm the
    /// clause list is EXACTLY `⋃ gate-CNFs ∪ {disequality}` (multiset-equal),
    /// that every gate has correct arity and in-range variables, that the
    /// disequality clause is the recorded `diff` disjunction, and that each
    /// `Diff` gate is `Xor2(ir_out[i], machine_out[i])`.
    ///
    /// On success the clause list is the Tseitin miter of the recorded gates,
    /// compared bit-for-bit — the gate-level encoding-fidelity guarantee. The
    /// residual trusted boundary (gate DAG ⇔ SmtExpr) is documented in the
    /// module header.
    ///
    /// # Errors
    /// Returns the first [`SatProvError`] encountered (fail-closed).
    pub fn validate(&self, clauses: &[Vec<SatLit>]) -> Result<(), SatProvError> {
        // 0. Basic shape.
        if self.ir_out.len() as u32 != self.width
            || self.machine_out.len() as u32 != self.width
            || self.diff.len() as u32 != self.width
        {
            return Err(SatProvError::ShapeMismatch(
                "ir_out / machine_out / diff length disagrees with width".into(),
            ));
        }
        let in_range = |l: i32| -> bool {
            let v = l.unsigned_abs();
            v >= 1 && v <= self.num_vars
        };
        for (g, rec) in self.gates.iter().enumerate() {
            if rec.ins.len() != rec.kind.arity() {
                return Err(SatProvError::BadArity { gate: g });
            }
            if !in_range(rec.out) || rec.out <= 0 || rec.ins.iter().any(|&l| !in_range(l)) {
                return Err(SatProvError::VarOutOfRange(rec.out));
            }
        }
        for &l in self
            .ir_out
            .iter()
            .chain(&self.machine_out)
            .chain(&self.diff)
        {
            if !in_range(l) {
                return Err(SatProvError::VarOutOfRange(l));
            }
        }

        // 1. Diff gates compare ir_out[i] with machine_out[i], and diff[i] is
        //    that gate's output.
        let diff_gates: Vec<&GateRecord> = self
            .gates
            .iter()
            .filter(|g| g.side == MiterSide::Diff)
            .collect();
        for (i, &d) in self.diff.iter().enumerate() {
            let gate = diff_gates.iter().find(|g| g.out == d.abs());
            let Some(gate) = gate else {
                return Err(SatProvError::DiffGateMismatch { bit: i });
            };
            if gate.kind != GateKind::Xor2 || gate.ins != vec![self.ir_out[i], self.machine_out[i]]
            {
                return Err(SatProvError::DiffGateMismatch { bit: i });
            }
        }

        // 2. Multiset of provenance clauses (all gate CNFs + the disequality)
        //    must equal the payload's clause multiset.
        let mut expected: BTreeMap<Vec<i64>, i64> = BTreeMap::new();
        for rec in &self.gates {
            for cl in canonical_gate_clauses(rec.kind, rec.out, &rec.ins) {
                *expected.entry(canon_clause(&cl)).or_default() += 1;
            }
        }
        *expected.entry(canon_clause(&self.diff)).or_default() += 1;

        let mut actual: BTreeMap<Vec<i64>, i64> = BTreeMap::new();
        for clause in clauses {
            let signed: Vec<i32> = clause
                .iter()
                .map(|&l| satlit_to_dimacs(l))
                .map(|l| i32::try_from(l).unwrap_or(i32::MAX))
                .collect();
            *actual.entry(canon_clause(&signed)).or_default() += 1;
        }

        if expected != actual {
            // Count the asymmetric differences for a useful error.
            let mut payload_unmatched = 0i64;
            let mut provenance_unmatched = 0i64;
            let mut keys: BTreeMap<Vec<i64>, ()> = BTreeMap::new();
            for k in expected.keys().chain(actual.keys()) {
                keys.insert(k.clone(), ());
            }
            for k in keys.keys() {
                let e = expected.get(k).copied().unwrap_or(0);
                let a = actual.get(k).copied().unwrap_or(0);
                if a > e {
                    payload_unmatched += a - e;
                } else if e > a {
                    provenance_unmatched += e - a;
                }
            }
            return Err(SatProvError::ClauseSetMismatch {
                payload_unmatched: payload_unmatched as usize,
                provenance_unmatched: provenance_unmatched as usize,
            });
        }
        Ok(())
    }

    /// Convenience: [`Self::validate`] plus a check that the provenance's
    /// `rule_name` equals `expected_rule` (fail-closed).
    pub fn validate_for_rule(
        &self,
        expected_rule: &str,
        clauses: &[Vec<SatLit>],
    ) -> Result<(), SatProvError> {
        if self.rule_name != expected_rule {
            return Err(SatProvError::RuleNameMismatch {
                got: self.rule_name.clone(),
                expected: expected_rule.to_string(),
            });
        }
        self.validate(clauses)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A tiny hand-built band-of-1-bit provenance: two AND gates over shared
    /// inputs, one diff xor gate, one disequality clause.
    fn tiny_band() -> (MiterProvenance, Vec<Vec<SatLit>>) {
        // vars: a=1, b=2, ir_and=3, mc_and=4, diff=5.
        let prov = MiterProvenance {
            rule_name: "Band_test".to_string(),
            width: 1,
            num_vars: 5,
            inputs: vec![("a".into(), vec![1]), ("b".into(), vec![2])],
            gates: vec![
                GateRecord {
                    side: MiterSide::Ir,
                    kind: GateKind::And2,
                    out: 3,
                    ins: vec![1, 2],
                },
                GateRecord {
                    side: MiterSide::Machine,
                    kind: GateKind::And2,
                    out: 4,
                    ins: vec![1, 2],
                },
                GateRecord {
                    side: MiterSide::Diff,
                    kind: GateKind::Xor2,
                    out: 5,
                    ins: vec![3, 4],
                },
            ],
            ir_out: vec![3],
            machine_out: vec![4],
            diff: vec![5],
        };
        // The clause list = the two AND gates + the diff xor + the disequality.
        let to_satlit = |l: i32| -> SatLit { (l.unsigned_abs() - 1, l < 0) };
        let mut clauses: Vec<Vec<SatLit>> = Vec::new();
        for cl in canonical_gate_clauses(GateKind::And2, 3, &[1, 2]) {
            clauses.push(cl.iter().map(|&l| to_satlit(l)).collect());
        }
        for cl in canonical_gate_clauses(GateKind::And2, 4, &[1, 2]) {
            clauses.push(cl.iter().map(|&l| to_satlit(l)).collect());
        }
        for cl in canonical_gate_clauses(GateKind::Xor2, 5, &[3, 4]) {
            clauses.push(cl.iter().map(|&l| to_satlit(l)).collect());
        }
        clauses.push(vec![to_satlit(5)]); // disequality: at least one diff true
        (prov, clauses)
    }

    #[test]
    fn validate_accepts_coherent_provenance() {
        let (prov, clauses) = tiny_band();
        prov.validate(&clauses)
            .expect("coherent provenance validates");
        prov.validate_for_rule("Band_test", &clauses)
            .expect("rule name matches");
        assert!(prov.digest().is_some());
    }

    #[test]
    fn validate_rejects_dropped_clause() {
        let (prov, mut clauses) = tiny_band();
        clauses.pop(); // drop the disequality
        assert!(matches!(
            prov.validate(&clauses),
            Err(SatProvError::ClauseSetMismatch { .. })
        ));
    }

    #[test]
    fn validate_rejects_foreign_clause() {
        let (prov, mut clauses) = tiny_band();
        // Swap the disequality for an unrelated (still in-range) clause.
        *clauses.last_mut().unwrap() = vec![(0, true)];
        assert!(matches!(
            prov.validate(&clauses),
            Err(SatProvError::ClauseSetMismatch { .. })
        ));
    }

    #[test]
    fn validate_rejects_tampered_diff_gate() {
        let (mut prov, clauses) = tiny_band();
        // Point the diff gate at the wrong ir output.
        prov.gates[2].ins = vec![4, 4];
        assert!(matches!(
            prov.validate(&clauses),
            Err(SatProvError::DiffGateMismatch { .. } | SatProvError::ClauseSetMismatch { .. })
        ));
    }

    #[test]
    fn text_round_trips() {
        let (prov, _) = tiny_band();
        let text = prov.to_text().expect("serialize");
        let back = MiterProvenance::parse(&text).expect("parse");
        assert_eq!(prov, back, "provenance must round-trip through text");
    }

    #[test]
    fn parse_rejects_bad_header() {
        assert!(matches!(
            MiterProvenance::parse("nope\n"),
            Err(SatProvError::BadText(_))
        ));
    }

    #[test]
    fn canonical_clauses_are_entailed() {
        for (kind, out, ins) in [
            (GateKind::Xor2, 10, vec![3, -4]),
            (GateKind::Xor3, 11, vec![3, -4, 5]),
            (GateKind::And2, 12, vec![-3, 4]),
            (GateKind::Maj3, 13, vec![3, 4, -5]),
        ] {
            for clause in canonical_gate_clauses(kind, out, &ins) {
                assert!(clause_entailed_by_gate(&clause, kind, out, &ins));
            }
        }
    }
}
