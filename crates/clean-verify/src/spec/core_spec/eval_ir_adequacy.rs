// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `EvalIR` — the adequacy grid's theorem band (plan W5, §4(c) of
//! `docs/analysis/evalir-completion-plan-2026-08-24.md`).
//!
//! The 28-arm dispatch (`super::eval_ir_machine`, `ir_exec`) binds every
//! field of every `IRInst` constructor and DROPS twenty of them — type
//! annotations, volatility flags, `gep`'s `inbounds`, `switch`'s
//! exhaustiveness flag, `callindirect`'s signature index and calling
//! convention. Three of the twenty have had kernel-checked irrelevance
//! theorems since the operand audit (`ir_exec_switch_exh_irrelevant`,
//! `ir_exec_callind_conv_irrelevant`, `ir_exec_callind_sig_irrelevant`,
//! registered beside the dispatch). This module is the other SEVENTEEN, one
//! per remaining dropped field, same mechanism: the kernel iota-reduces the
//! match on the concrete constructor, the dropped field never appears in the
//! answer, and `Eq.refl` closes the equation at EVERY module, state, result
//! list and sibling operand.
//!
//! Why this is worth seventeen theorems rather than one comment: the
//! constructor-NAME parity check in the trust-ir repo "cannot see semantic
//! depth" (`lean_schema_parity.rs`; `docs/GAP2_ENCODING_CORRESPONDENCE.md`).
//! The B-SEM exit replaces that sentence with a per-constructor account of
//! exactly what the Clean encoding preserves, drops, and why — the grid
//! `data/evalir_adequacy_grid.json`, generated fail-closed by
//! `scripts/evalir_adequacy_grid.py` from the `IRInst` telescopes and the
//! dispatch itself, and gated by `tests/eval_ir/adequacy_grid.rs`. A field
//! the semantics reads is a `relevant-by-design` row (no theorem is possible
//! — varying it changes the step); a field the dispatch drops is an
//! `irrelevance-proved-await-mint` row naming its theorem here; the erased
//! `align` slots are `audit-pin` rows; the measured executor divergences from
//! W1-W4 are `declared-delta` rows.
//!
//! Registration order: after `add_eval_ir_dispatch` (these statements consume
//! `ir_exec` and the arm evaluators, nothing later), appended at the END of
//! the machine stage so every pre-existing def keeps its position — the W4
//! precedent for extending a stage without disturbing its order.
//!
//! The statement pattern, fixed by the three precedents at
//! `eval_ir_machine.rs`: an `IRTy`/`Nat`-typed dropped field is varied as two
//! universally quantified binders (`t1`/`t2` — the `callind_conv` shape); a
//! `Bool`-typed one is stated at `Bool.true` vs `Bool.false` (the
//! `switch_exh` shape — with two inhabitants that IS full generality). The
//! proof term is the common iota-reduct: the dispatch arm's RHS verbatim.
//! The `#[cfg(test)]` band below checks, spec-free and on this box, that
//! every statement's two sides differ in exactly the claimed slot, that the
//! varied field really is dropped by the dispatch arm, and that the claimed
//! rows are EXACTLY the dispatch's dropped-field surface — so a dispatch
//! edit that starts reading a field, or drops a new one, fails here before
//! any kernel runs.

use crate::spec::error::SpecError;
use crate::spec::Specification;

/// One irrelevance theorem: the constructor, the varied field (the dispatch
/// arm's pattern-variable name), the registered source, and its description.
pub(crate) struct AdequacyRow {
    /// Consumed by the spec-free `#[cfg(test)]` band below (and re-derived by
    /// `scripts/evalir_adequacy_grid.py`); registration itself reads only
    /// `src`/`doc`.
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) ctor: &'static str,
    /// See `ctor`.
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) varied: &'static str,
    pub(crate) src: &'static str,
    doc: &'static str,
}

/// The seventeen W5 irrelevance theorems, in `IRInst` declaration order.
/// (The other three dropped fields — `switch.exh`, `callindirect.sig`,
/// `callindirect.cc` — have their theorems beside the dispatch since the
/// operand audit; the unit tests below hold the union to be exactly the
/// dispatch's dropped-field surface.)
pub(crate) const ADEQUACY_THEOREMS: &[AdequacyRow] = &[
    AdequacyRow {
        ctor: "load",
        varied: "t",
        src: "def ir_exec_load_ty_irrelevant (m : IRModule) (t1 : IRTy) (t2 : IRTy) (p : Nat) (vol : Bool) (rs : IRList Nat) (s : IRMachine) : Eq IRConfig (ir_exec m (IRInst.load t1 p vol) rs s) (ir_exec m (IRInst.load t2 p vol) rs s) := Eq.refl IRConfig (ir_bind_result s rs (ir_load_eval s (ir_getd s p)))",
        doc: "ir_exec_load_ty_irrelevant: the machine's step on a `load` is THE SAME \
              CONFIGURATION at any two printed types — a cell-addressed load returns the stored \
              VALUE whatever the annotation says it is. This is the semantic half of the \
              2026-08-19 operand-audit finding that BOTH parsers ignored `load`'s type slot (the \
              `load_tys` lineage lane now compares it): the type is a lineage fact about which \
              module was emitted, provably not a fact about what the load computes. \
              DerivedProved, zero axiom_deps.",
    },
    AdequacyRow {
        ctor: "load",
        varied: "vol",
        src: "def ir_exec_load_vol_irrelevant (m : IRModule) (t : IRTy) (p : Nat) (rs : IRList Nat) (s : IRMachine) : Eq IRConfig (ir_exec m (IRInst.load t p Bool.true) rs s) (ir_exec m (IRInst.load t p Bool.false) rs s) := Eq.refl IRConfig (ir_bind_result s rs (ir_load_eval s (ir_getd s p)))",
        doc: "ir_exec_load_vol_irrelevant: the volatility flag cannot change the step, either \
              way it is set. The machine has no observable the flag could order against — no \
              I/O, no concurrent writer — so volatility is outside the fragment because the \
              fragment provably does not consult it. DerivedProved, zero axiom_deps.",
    },
    AdequacyRow {
        ctor: "store",
        varied: "t",
        src: "def ir_exec_store_ty_irrelevant (m : IRModule) (t1 : IRTy) (t2 : IRTy) (p : Nat) (v : Nat) (vol : Bool) (rs : IRList Nat) (s : IRMachine) : Eq IRConfig (ir_exec m (IRInst.store t1 p v vol) rs s) (ir_exec m (IRInst.store t2 p v vol) rs s) := Eq.refl IRConfig (ir_store_exec s (ir_getd s p) (ir_getd s v))",
        doc: "ir_exec_store_ty_irrelevant: a `store` writes the operand VALUE into the cell at \
              any two printed types — the write dual of ir_exec_load_ty_irrelevant. \
              DerivedProved, zero axiom_deps.",
    },
    AdequacyRow {
        ctor: "store",
        varied: "vol",
        src: "def ir_exec_store_vol_irrelevant (m : IRModule) (t : IRTy) (p : Nat) (v : Nat) (rs : IRList Nat) (s : IRMachine) : Eq IRConfig (ir_exec m (IRInst.store t p v Bool.true) rs s) (ir_exec m (IRInst.store t p v Bool.false) rs s) := Eq.refl IRConfig (ir_store_exec s (ir_getd s p) (ir_getd s v))",
        doc: "ir_exec_store_vol_irrelevant: the write's volatility flag is dropped by the \
              dispatch exactly as the read's; same fragment boundary, same proof. \
              DerivedProved, zero axiom_deps.",
    },
    AdequacyRow {
        ctor: "alloca",
        varied: "t",
        src: "def ir_exec_alloca_ty_irrelevant (m : IRModule) (t1 : IRTy) (t2 : IRTy) (c : IROption Nat) (rs : IRList Nat) (s : IRMachine) : Eq IRConfig (ir_exec m (IRInst.alloca t1 c) rs s) (ir_exec m (IRInst.alloca t2 c) rs s) := Eq.refl IRConfig (ir_alloca_exec s rs c)",
        doc: "ir_exec_alloca_ty_irrelevant: `alloca` allocates its live undef CELLS whatever \
              type they are declared to hold — a cell holds a value, so the element type sizes \
              nothing. The neighbouring `align` operand does not even reach the instruction \
              (erased at IRInst; the audit-pin rows in data/evalir_adequacy_grid.json and the \
              operand_audit pin own that boundary). DerivedProved, zero axiom_deps.",
    },
    AdequacyRow {
        ctor: "gep",
        varied: "t",
        src: "def ir_exec_gep_ty_irrelevant (m : IRModule) (t1 : IRTy) (t2 : IRTy) (b : Nat) (idxs : IRList Nat) (inb : Bool) (rs : IRList Nat) (s : IRMachine) : Eq IRConfig (ir_exec m (IRInst.gep t1 b idxs inb) rs s) (ir_exec m (IRInst.gep t2 b idxs inb) rs s) := Eq.refl IRConfig (ir_bind_result s rs (ir_gep_eval (ir_getd s b) (ir_resolve s idxs)))",
        doc: "ir_exec_gep_ty_irrelevant: `gep`'s printed element type cannot change the step — \
              the machine's offset arithmetic is single-scale over cells, never byte-scaled by \
              a type's size. DerivedProved, zero axiom_deps.",
    },
    AdequacyRow {
        ctor: "gep",
        varied: "inb",
        src: "def ir_exec_gep_inbounds_irrelevant (m : IRModule) (t : IRTy) (b : Nat) (idxs : IRList Nat) (rs : IRList Nat) (s : IRMachine) : Eq IRConfig (ir_exec m (IRInst.gep t b idxs Bool.true) rs s) (ir_exec m (IRInst.gep t b idxs Bool.false) rs s) := Eq.refl IRConfig (ir_bind_result s rs (ir_gep_eval (ir_getd s b) (ir_resolve s idxs)))",
        doc: "ir_exec_gep_inbounds_irrelevant: the machine takes THE SAME step whichever way \
              `inbounds` is set — which is precisely the PRECONDITION of the no-wrap folding \
              the flag licenses (eval_ir_syntax.rs keeps the field as load-bearing for any \
              later optimisation argument): a licence changes what a TRANSFORM may do, never \
              what this machine does. DerivedProved, zero axiom_deps.",
    },
    AdequacyRow {
        ctor: "ptrdata",
        varied: "t",
        src: "def ir_exec_ptrdata_ty_irrelevant (m : IRModule) (t1 : IRTy) (t2 : IRTy) (p : Nat) (rs : IRList Nat) (s : IRMachine) : Eq IRConfig (ir_exec m (IRInst.ptrdata t1 p) rs s) (ir_exec m (IRInst.ptrdata t2 p) rs s) := Eq.refl IRConfig (ir_bind_result s rs (ir_ptrdata_eval (ir_getd s p)))",
        doc: "ir_exec_ptrdata_ty_irrelevant: `ptr_data` projects the pointer VALUE's data lane; \
              the printed pointer type is inert at every operand. DerivedProved, zero \
              axiom_deps.",
    },
    AdequacyRow {
        ctor: "ptrmetadata",
        varied: "pt",
        src: "def ir_exec_ptrmeta_pt_irrelevant (m : IRModule) (pt1 : IRTy) (pt2 : IRTy) (mt : IRTy) (p : Nat) (rs : IRList Nat) (s : IRMachine) : Eq IRConfig (ir_exec m (IRInst.ptrmetadata pt1 mt p) rs s) (ir_exec m (IRInst.ptrmetadata pt2 mt p) rs s) := Eq.refl IRConfig (ir_bind_result s rs (ir_ptrmeta_eval (ir_getd s p)))",
        doc: "ir_exec_ptrmeta_pt_irrelevant: `ptr_metadata` dispatches on the pointer VALUE's \
              thin-vs-fat shape (ir_ptrmeta_eval), not on the printed POINTER type; the slot is \
              inert at every operand. DerivedProved, zero axiom_deps.",
    },
    AdequacyRow {
        ctor: "ptrmetadata",
        varied: "mt",
        src: "def ir_exec_ptrmeta_mt_irrelevant (m : IRModule) (pt : IRTy) (mt1 : IRTy) (mt2 : IRTy) (p : Nat) (rs : IRList Nat) (s : IRMachine) : Eq IRConfig (ir_exec m (IRInst.ptrmetadata pt mt1 p) rs s) (ir_exec m (IRInst.ptrmetadata pt mt2 p) rs s) := Eq.refl IRConfig (ir_bind_result s rs (ir_ptrmeta_eval (ir_getd s p)))",
        doc: "ir_exec_ptrmeta_mt_irrelevant: the printed METADATA type is as inert as the \
              pointer type beside it — the W2b lane already recorded that the metadata VALUE \
              itself is carried as a bare Nat (the vtable/fnptr pointer-ness erasure); this \
              theorem is the instruction-level statement that the machine consults neither \
              annotation. DerivedProved, zero axiom_deps.",
    },
    AdequacyRow {
        ctor: "ptrfromparts",
        varied: "pt",
        src: "def ir_exec_ptrparts_pt_irrelevant (m : IRModule) (pt1 : IRTy) (pt2 : IRTy) (mt : IRTy) (d : Nat) (md : Nat) (rs : IRList Nat) (s : IRMachine) : Eq IRConfig (ir_exec m (IRInst.ptrfromparts pt1 mt d md) rs s) (ir_exec m (IRInst.ptrfromparts pt2 mt d md) rs s) := Eq.refl IRConfig (ir_bind_result s rs (ir_ptrparts_eval (ir_getd s d) (ir_getd s md)))",
        doc: "ir_exec_ptrparts_pt_irrelevant: the rebuild consumes the data and metadata \
              VALUES (ir_ptrparts_eval dispatches on their shapes); the printed pointer type \
              is inert at every pair. DerivedProved, zero axiom_deps.",
    },
    AdequacyRow {
        ctor: "ptrfromparts",
        varied: "mt",
        src: "def ir_exec_ptrparts_mt_irrelevant (m : IRModule) (pt : IRTy) (mt1 : IRTy) (mt2 : IRTy) (d : Nat) (md : Nat) (rs : IRList Nat) (s : IRMachine) : Eq IRConfig (ir_exec m (IRInst.ptrfromparts pt mt1 d md) rs s) (ir_exec m (IRInst.ptrfromparts pt mt2 d md) rs s) := Eq.refl IRConfig (ir_bind_result s rs (ir_ptrparts_eval (ir_getd s d) (ir_getd s md)))",
        doc: "ir_exec_ptrparts_mt_irrelevant: the printed metadata type slot of \
              `ptr_from_parts` is dropped exactly as `ptr_metadata`'s; the machine's thin/fat \
              decision reads the metadata VALUE. DerivedProved, zero axiom_deps.",
    },
    AdequacyRow {
        ctor: "extractfield",
        varied: "t",
        src: "def ir_exec_extractfield_ty_irrelevant (m : IRModule) (t1 : IRTy) (t2 : IRTy) (a : Nat) (k : Nat) (rs : IRList Nat) (s : IRMachine) : Eq IRConfig (ir_exec m (IRInst.extractfield t1 a k) rs s) (ir_exec m (IRInst.extractfield t2 a k) rs s) := Eq.refl IRConfig (ir_bind_result s rs (ir_ef_at (ir_getd s a) k))",
        doc: "ir_exec_extractfield_ty_irrelevant: the field read indexes the aggregate VALUE's \
              inline spine; the aggregate's printed type is inert (the operand audit's \
              `extract_tys` lineage lane compares the slot artifact-side, and this is the \
              kernel-checked reason the machine may drop it). DerivedProved, zero axiom_deps.",
    },
    AdequacyRow {
        ctor: "insertfield",
        varied: "t",
        src: "def ir_exec_insertfield_ty_irrelevant (m : IRModule) (t1 : IRTy) (t2 : IRTy) (a : Nat) (k : Nat) (v : Nat) (rs : IRList Nat) (s : IRMachine) : Eq IRConfig (ir_exec m (IRInst.insertfield t1 a k v) rs s) (ir_exec m (IRInst.insertfield t2 a k v) rs s) := Eq.refl IRConfig (ir_bind_result s rs (ir_insert_field (ir_getd s a) k (ir_getd s v)))",
        doc: "ir_exec_insertfield_ty_irrelevant: the functional field update rebuilds the \
              aggregate VALUE's spine; the printed aggregate type is inert. DerivedProved, \
              zero axiom_deps.",
    },
    AdequacyRow {
        ctor: "extractelement",
        varied: "t",
        src: "def ir_exec_extractelement_ty_irrelevant (m : IRModule) (t1 : IRTy) (t2 : IRTy) (a : Nat) (k : Nat) (rs : IRList Nat) (s : IRMachine) : Eq IRConfig (ir_exec m (IRInst.extractelement t1 a k) rs s) (ir_exec m (IRInst.extractelement t2 a k) rs s) := Eq.refl IRConfig (ir_bind_result s rs (ir_extract_elem (ir_getd s a) (ir_getd s k)))",
        doc: "ir_exec_extractelement_ty_irrelevant: the dynamically indexed element read walks \
              the aggregate VALUE's spine by the INDEX OPERAND's value; the printed container \
              type is inert. DerivedProved, zero axiom_deps.",
    },
    AdequacyRow {
        ctor: "undef",
        varied: "t",
        src: "def ir_exec_undef_ty_irrelevant (m : IRModule) (t1 : IRTy) (t2 : IRTy) (rs : IRList Nat) (s : IRMachine) : Eq IRConfig (ir_exec m (IRInst.undef t1) rs s) (ir_exec m (IRInst.undef t2) rs s) := Eq.refl IRConfig (ir_bind s rs IRScalar.undef_)",
        doc: "ir_exec_undef_ty_irrelevant: `undef` binds the one untyped poison value \
              IRScalar.undef_ whatever type the instruction is declared at; the annotation is \
              inert. (What HAPPENS to that value afterwards is the W2a declared delta — the \
              grid's `undef-execution` row — not this theorem's subject.) DerivedProved, zero \
              axiom_deps.",
    },
    AdequacyRow {
        ctor: "select",
        varied: "t",
        src: "def ir_exec_select_ty_irrelevant (m : IRModule) (t1 : IRTy) (t2 : IRTy) (c : Nat) (a : Nat) (b : Nat) (rs : IRList Nat) (s : IRMachine) : Eq IRConfig (ir_exec m (IRInst.select t1 c a b) rs s) (ir_exec m (IRInst.select t2 c a b) rs s) := Eq.refl IRConfig (ir_bind_result s rs (ir_select_eval (ir_getd s c) (ir_getd s a) (ir_getd s b)))",
        doc: "ir_exec_select_ty_irrelevant: `select` dispatches on the CONDITION VALUE and \
              returns one arm VALUE; the printed result type is inert at every triple. \
              DerivedProved, zero axiom_deps.",
    },
];

impl Specification {
    /// Register the seventeen W5 irrelevance theorems.
    ///
    /// # Errors
    /// Returns `SpecError` if any declaration fails to elaborate or
    /// kernel-check — for these `Eq.refl` statements that means the kernel
    /// REFUTED an irrelevance claim (the dispatch started reading the field),
    /// which is a finding to report, never a statement to weaken.
    pub(super) fn add_eval_ir_adequacy(&mut self) -> Result<(), SpecError> {
        for row in ADEQUACY_THEOREMS {
            self.add_recursive_def(row.src, row.doc)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    //! Spec-free string-level checks, runnable on the authoring box: the
    //! kernel half (registration) is the big-box E1 obligation recorded in
    //! `data/evalir_w5.PENDING.md`, so every transcription slip that CAN be
    //! caught without a kernel is caught here.

    use std::collections::BTreeSet;

    use super::ADEQUACY_THEOREMS;

    const MACHINE_SRC: &str = include_str!("eval_ir_machine.rs");
    const SYNTAX_SRC: &str = include_str!("eval_ir_syntax.rs");

    /// The three dropped-field theorems that predate W5 and live beside the
    /// dispatch in `eval_ir_machine.rs`.
    const PRE_EXISTING: &[(&str, &str, &str)] = &[
        ("switch", "exh", "ir_exec_switch_exh_irrelevant"),
        ("callindirect", "sig", "ir_exec_callind_sig_irrelevant"),
        ("callindirect", "cc", "ir_exec_callind_conv_irrelevant"),
    ];

    /// Identifier tokens of `s` (split on anything outside `[A-Za-z0-9_]`).
    fn word_tokens(s: &str) -> BTreeSet<String> {
        s.split(|c: char| !(c.is_ascii_alphanumeric() || c == '_'))
            .filter(|t| !t.is_empty())
            .map(str::to_string)
            .collect()
    }

    /// The `ir_exec` dispatch arms: `(ctor, pattern vars, rhs)`.
    fn dispatch_arms() -> Vec<(String, Vec<String>, String)> {
        let lines: Vec<&str> = MACHINE_SRC.lines().collect();
        let def_at = lines
            .iter()
            .position(|l| l.contains("def ir_exec (m : IRModule) (i : IRInst)"))
            .expect("the ir_exec dispatch definition must be present in eval_ir_machine.rs");
        let mut arms = Vec::new();
        for line in &lines[def_at + 1..] {
            let t = line.trim();
            let Some(rest) = t.strip_prefix("| IRInst.") else {
                break;
            };
            let rest = rest.strip_suffix("\",").unwrap_or(rest);
            let (lhs, rhs) = rest
                .split_once(" => ")
                .expect("every dispatch arm must be `| IRInst.<ctor> <vars> => <rhs>`");
            let mut toks = lhs.split_whitespace().map(str::to_string);
            let ctor = toks.next().expect("an arm names its constructor");
            arms.push((ctor, toks.collect(), rhs.to_string()));
        }
        assert_eq!(arms.len(), 28, "the dispatch must have exactly 28 arms");
        arms
    }

    /// The two `(IRInst.<ctor> …)` applications inside one theorem statement.
    fn applications(src: &str) -> Vec<(String, Vec<String>)> {
        let mut out = Vec::new();
        let mut rest = src;
        while let Some(at) = rest.find("(IRInst.") {
            let inner = &rest[at + 1..];
            let end = inner
                .find(')')
                .expect("an IRInst application must close its paren");
            let app = &inner[..end];
            let mut toks = app.split_whitespace().map(str::to_string);
            let head = toks.next().expect("the application has a head");
            out.push((
                head.strip_prefix("IRInst.")
                    .expect("the head is IRInst-qualified")
                    .to_string(),
                toks.collect(),
            ));
            rest = &inner[end..];
        }
        out
    }

    /// Every statement's two sides differ in EXACTLY the claimed slot, and
    /// the varied tokens never reach the proof term — the transcription
    /// classes (both sides `t1`; the wrong slot varied; a varied token pasted
    /// into the `Eq.refl` reduct) each fail here by construction.
    #[test]
    fn test_adequacy_statements_vary_exactly_the_claimed_slot() {
        let arms = dispatch_arms();
        for row in ADEQUACY_THEOREMS {
            let apps = applications(row.src);
            assert_eq!(
                apps.len(),
                2,
                "{}: a two-sided irrelevance statement applies its constructor exactly twice",
                row.ctor
            );
            let (c1, args1) = &apps[0];
            let (c2, args2) = &apps[1];
            assert_eq!(c1, row.ctor, "{}: LHS constructor", row.ctor);
            assert_eq!(c2, row.ctor, "{}: RHS constructor", row.ctor);
            assert_eq!(args1.len(), args2.len(), "{}: arity", row.ctor);
            let diff: Vec<usize> = (0..args1.len()).filter(|&i| args1[i] != args2[i]).collect();
            assert_eq!(
                diff.len(),
                1,
                "{}.{}: the two sides must differ in exactly one slot, found {:?}",
                row.ctor,
                row.varied,
                diff
            );
            // The differing position is the dispatch arm's pattern variable
            // the row claims to vary.
            let (_, vars, _) = arms
                .iter()
                .find(|(c, _, _)| c == row.ctor)
                .unwrap_or_else(|| panic!("{}: no dispatch arm", row.ctor));
            assert_eq!(
                vars[diff[0]], row.varied,
                "{}: the varied slot (index {}) is not the claimed field `{}`",
                row.ctor, diff[0], row.varied
            );
            // Neither varied token appears in the proof term.
            let proof = row
                .src
                .split(":= Eq.refl")
                .nth(1)
                .expect("every adequacy theorem is closed by Eq.refl");
            let proof_toks = word_tokens(proof);
            for side in [&args1[diff[0]], &args2[diff[0]]] {
                for tok in word_tokens(side) {
                    if tok == "Bool" {
                        continue; // Bool.true/Bool.false share the family name.
                    }
                    assert!(
                        !proof_toks.contains(&tok),
                        "{}.{}: varied token `{tok}` leaked into the proof term",
                        row.ctor,
                        row.varied
                    );
                }
            }
        }
    }

    /// The claimed rows are EXACTLY the dispatch's dropped-field surface:
    /// every bound-and-unused pattern variable has one theorem (here or
    /// beside the dispatch), and no theorem claims a field the arm reads.
    #[test]
    fn test_dropped_dispatch_operands_and_theorems_are_the_same_set() {
        let mut dropped = BTreeSet::new();
        for (ctor, vars, rhs) in dispatch_arms() {
            let used = word_tokens(&rhs);
            for v in vars {
                if !used.contains(&v) {
                    dropped.insert((ctor.clone(), v));
                }
            }
        }
        let mut claimed = BTreeSet::new();
        for row in ADEQUACY_THEOREMS {
            assert!(
                claimed.insert((row.ctor.to_string(), row.varied.to_string())),
                "{}.{}: duplicate theorem row",
                row.ctor,
                row.varied
            );
        }
        for (ctor, var, name) in PRE_EXISTING {
            assert!(
                claimed.insert(((*ctor).to_string(), (*var).to_string())),
                "{ctor}.{var}: claimed both here and in eval_ir_machine.rs"
            );
            assert!(
                MACHINE_SRC.contains(&format!("def {name} ")),
                "{name} must still be registered beside the dispatch"
            );
        }
        assert_eq!(
            dropped, claimed,
            "the dispatch's dropped fields and the irrelevance theorems must be the same set \
             (20 rows). A new dropped field needs a theorem; a field the dispatch now reads \
             must have its theorem REMOVED and its grid row flipped to relevant-by-design — \
             regenerate data/evalir_adequacy_grid.json either way."
        );
    }

    /// Arity cross-check against the `IRInst` telescopes: the dispatch binds
    /// exactly one variable per declared field, so the per-index grid rows
    /// derived from these two sources name real slots.
    #[test]
    fn test_dispatch_arity_matches_the_irinst_telescopes() {
        let lines: Vec<&str> = SYNTAX_SRC.lines().collect();
        let at = lines
            .iter()
            .position(|l| l.contains("inductive IRInst : Type"))
            .expect("the IRInst inductive must be present in eval_ir_syntax.rs");
        let mut fields = Vec::new();
        for line in &lines[at + 1..] {
            let t = line.trim();
            let Some(rest) = t.strip_prefix("| ") else {
                break;
            };
            let (name, tele) = rest
                .split_once(" : ")
                .expect("every IRInst constructor line is `| name : telescope`");
            let n_fields = tele.split('\u{2192}').count() - 1; // drop the result type
            fields.push((name.to_string(), n_fields));
        }
        assert_eq!(
            fields.len(),
            28,
            "IRInst must declare exactly 28 constructors"
        );
        let arms = dispatch_arms();
        for (name, n_fields) in fields {
            let (_, vars, _) = arms
                .iter()
                .find(|(c, _, _)| *c == name)
                .unwrap_or_else(|| panic!("{name}: declared in IRInst but has no dispatch arm"));
            assert_eq!(
                vars.len(),
                n_fields,
                "{name}: the dispatch binds {} variables for {} declared fields",
                vars.len(),
                n_fields
            );
        }
    }
}
