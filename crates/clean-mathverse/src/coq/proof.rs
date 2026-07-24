// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Coq proof term analysis: vernacular parsing, skeleton extraction, tactic recognition.

use std::collections::HashMap;

#[cfg(test)]
use crate::coq::alpha::CicCase;
use crate::coq::alpha::{
    cic_to_flat_expr, classify_coq_module, import_mutual_inductive, sexp_to_cic,
    sexp_to_mutual_inductive, CicSort, CicTerm, CoqImportStats, CoqMutualInductive, Sexp,
};
use crate::error::{MathverseError, MathverseResult};
use crate::shard::ShardWriter;
use crate::skeleton::{DifficultyEstimate, Direction, ProofSkeleton, ProofStep};
use crate::types::{
    AxiomProfile, ContentDomain, ImportConfidence, MathverseConstantHeader, SourceSystem, NO_VALUE,
};

// -- Vernacular commands ------------------------------------------------------

/// Parsed Coq vernacular command from SerAPI output.
#[derive(Clone, Debug)]
pub enum CoqVernacular {
    Definition {
        name: String,
        type_: CicTerm,
        body: CicTerm,
    },
    Lemma {
        name: String,
        type_: CicTerm,
        proof: Option<CicTerm>,
    },
    Theorem {
        name: String,
        type_: CicTerm,
        proof: Option<CicTerm>,
    },
    Axiom {
        name: String,
        type_: CicTerm,
    },
    Inductive(CoqMutualInductive),
    Fixpoint {
        name: String,
        type_: CicTerm,
        body: CicTerm,
        decreasing_arg: u32,
    },
    Instance {
        name: String,
        class: String,
        type_: CicTerm,
        body: CicTerm,
    },
    Record {
        name: String,
        params: Vec<(String, CicTerm)>,
        fields: Vec<(String, CicTerm)>,
    },
    Opaque {
        name: String,
        type_: CicTerm,
    },
}

/// Parse a Coq vernacular command from a SerAPI s-expression.
pub fn parse_vernacular(sexp: &Sexp) -> Result<CoqVernacular, MathverseError> {
    let items = match sexp {
        Sexp::List(v) if !v.is_empty() => v,
        _ => return Err(vern_err("expected non-empty list")),
    };
    let head = match &items[0] {
        Sexp::Atom(s) => s.as_str(),
        _ => return Err(vern_err("expected atom head")),
    };
    match head {
        "CoqDefinition" => {
            req(items, 4, "CoqDefinition")?;
            Ok(CoqVernacular::Definition {
                name: atom(items, 1)?,
                type_: sexp_to_cic(&items[2])?,
                body: sexp_to_cic(&items[3])?,
            })
        }
        "CoqLemma" => {
            req(items, 3, "CoqLemma")?;
            Ok(CoqVernacular::Lemma {
                name: atom(items, 1)?,
                type_: sexp_to_cic(&items[2])?,
                proof: items.get(3).and_then(|s| sexp_to_cic(s).ok()),
            })
        }
        "CoqTheorem" => {
            req(items, 3, "CoqTheorem")?;
            Ok(CoqVernacular::Theorem {
                name: atom(items, 1)?,
                type_: sexp_to_cic(&items[2])?,
                proof: items.get(3).and_then(|s| sexp_to_cic(s).ok()),
            })
        }
        "CoqAxiom" => {
            req(items, 3, "CoqAxiom")?;
            Ok(CoqVernacular::Axiom {
                name: atom(items, 1)?,
                type_: sexp_to_cic(&items[2])?,
            })
        }
        "CoqInductive" => {
            req(items, 2, "CoqInductive")?;
            Ok(CoqVernacular::Inductive(sexp_to_mutual_inductive(
                &items[1],
            )?))
        }
        "CoqFixpoint" => {
            req(items, 4, "CoqFixpoint")?;
            let da = items
                .get(4)
                .and_then(|s| match s {
                    Sexp::Atom(a) => a.parse::<u32>().ok(),
                    _ => None,
                })
                .unwrap_or(0);
            Ok(CoqVernacular::Fixpoint {
                name: atom(items, 1)?,
                type_: sexp_to_cic(&items[2])?,
                body: sexp_to_cic(&items[3])?,
                decreasing_arg: da,
            })
        }
        "CoqInstance" => {
            req(items, 5, "CoqInstance")?;
            Ok(CoqVernacular::Instance {
                name: atom(items, 1)?,
                class: atom(items, 2)?,
                type_: sexp_to_cic(&items[3])?,
                body: sexp_to_cic(&items[4])?,
            })
        }
        "CoqRecord" => {
            req(items, 4, "CoqRecord")?;
            Ok(CoqVernacular::Record {
                name: atom(items, 1)?,
                params: parse_binders(&items[2])?,
                fields: parse_binders(&items[3])?,
            })
        }
        "CoqOpaque" => {
            req(items, 3, "CoqOpaque")?;
            Ok(CoqVernacular::Opaque {
                name: atom(items, 1)?,
                type_: sexp_to_cic(&items[2])?,
            })
        }
        other => Err(vern_err(&format!("unknown vernacular command: {other}"))),
    }
}

// -- Proof skeleton extraction ------------------------------------------------

/// Extract a proof skeleton from a CIC proof term.
pub fn extract_proof_skeleton(proof: &CicTerm) -> ProofSkeleton {
    let (mut steps, mut key_lemmas) = (Vec::new(), Vec::new());
    extract_steps(proof, &mut steps, &mut key_lemmas);
    ProofSkeleton {
        difficulty: estimate_difficulty(&steps),
        strategy: steps,
        key_lemmas,
    }
}

fn extract_steps(
    term: &CicTerm,
    steps: &mut Vec<ProofStep>,
    lemmas: &mut Vec<(String, Option<u32>)>,
) {
    match term {
        CicTerm::App(f, args) if matches!(f.as_ref(), CicTerm::Const(_)) => {
            let name = match f.as_ref() {
                CicTerm::Const(n) => n,
                _ => unreachable!(),
            };
            match name.as_str() {
                "eq_ind" => {
                    push_lemma(args, lemmas);
                    steps.push(ProofStep::Rewrite {
                        lemma: None,
                        direction: Direction::Forward,
                    });
                }
                "eq_ind_r" => {
                    push_lemma(args, lemmas);
                    steps.push(ProofStep::Rewrite {
                        lemma: None,
                        direction: Direction::Backward,
                    });
                }
                "False_ind" | "False_rect" | "absurd" => steps.push(ProofStep::Contradiction),
                n if n.ends_with("_ind") || n.ends_with("_rec") || n.ends_with("_rect") => {
                    steps.push(ProofStep::Induction {
                        on_arg: induction_arg(args),
                    });
                    lemmas.push((n.to_owned(), None));
                    for a in args {
                        extract_steps(a, steps, lemmas);
                    }
                }
                "eq_refl" => {} // trivial
                "eq_sym" => {
                    lemmas.push(("eq_sym".into(), None));
                    steps.push(ProofStep::Rewrite {
                        lemma: None,
                        direction: Direction::Backward,
                    });
                }
                "eq_trans" => {
                    lemmas.push(("eq_trans".into(), None));
                    steps.push(ProofStep::Apply { lemma: None });
                    for a in args {
                        extract_steps(a, steps, lemmas);
                    }
                }
                _ => {
                    lemmas.push((name.clone(), None));
                    steps.push(ProofStep::Apply { lemma: None });
                    for a in args {
                        extract_steps(a, steps, lemmas);
                    }
                }
            }
        }
        CicTerm::App(f, args) => {
            extract_steps(f, steps, lemmas);
            for a in args {
                extract_steps(a, steps, lemmas);
            }
        }
        CicTerm::Lambda(_, _, body) => extract_steps(body, steps, lemmas),
        CicTerm::LetIn(_, val, _, body) => {
            steps.push(ProofStep::Computation);
            extract_steps(val, steps, lemmas);
            extract_steps(body, steps, lemmas);
        }
        CicTerm::Case(case) => {
            steps.push(ProofStep::CaseSplit {
                num_cases: case.branches.len() as u32,
            });
            for b in &case.branches {
                extract_steps(b, steps, lemmas);
            }
        }
        CicTerm::Fix(bodies, _) => {
            steps.push(ProofStep::Induction { on_arg: 0 });
            for (_, _, b) in bodies {
                extract_steps(b, steps, lemmas);
            }
        }
        CicTerm::Const(name) => {
            lemmas.push((name.clone(), None));
        }
        _ => {}
    }
}

fn push_lemma(args: &[CicTerm], lemmas: &mut Vec<(String, Option<u32>)>) {
    if let Some(n) = find_const_in_args(args) {
        lemmas.push((n, None));
    }
}

fn find_const_in_args(args: &[CicTerm]) -> Option<String> {
    args.iter().find_map(|a| match a {
        CicTerm::Const(n) => Some(n.clone()),
        CicTerm::App(f, _) => match f.as_ref() {
            CicTerm::Const(n) => Some(n.clone()),
            _ => None,
        },
        _ => None,
    })
}

fn induction_arg(args: &[CicTerm]) -> u32 {
    for (i, a) in args.iter().enumerate() {
        match a {
            CicTerm::Rel(n) => return *n,
            CicTerm::Var(_) => return i as u32,
            _ => {}
        }
    }
    0
}

fn estimate_difficulty(steps: &[ProofStep]) -> DifficultyEstimate {
    let ind = steps
        .iter()
        .filter(|s| matches!(s, ProofStep::Induction { .. }))
        .count();
    let cas = steps
        .iter()
        .filter(|s| matches!(s, ProofStep::CaseSplit { .. }))
        .count();
    if steps.len() <= 3 && ind == 0 {
        DifficultyEstimate::Easy
    } else if ind <= 1 && cas <= 2 {
        DifficultyEstimate::Medium
    } else if ind <= 2 {
        DifficultyEstimate::Hard
    } else {
        DifficultyEstimate::Unknown
    }
}

// -- Tactic recognition -------------------------------------------------------

/// Recognized Coq proof tactic inferred from proof term structure.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum RecognizedTactic {
    Rewrite(String, Direction),
    Apply(String),
    Induction(String, u32),
    Destruct(String),
    Reflexivity,
    Symmetry,
    Transitivity,
    Assumption,
    Auto,
    Mathverse,
    Unfold(String),
    Simpl,
}

/// Analyze a CIC proof term and extract a sequence of recognized tactics.
pub fn analyze_proof_tactics(proof: &CicTerm) -> Vec<RecognizedTactic> {
    let mut t = Vec::new();
    analyze_inner(proof, &mut t);
    if t.is_empty() && proof_depth(proof) <= 2 {
        t.push(RecognizedTactic::Auto);
    }
    t
}

fn analyze_inner(term: &CicTerm, t: &mut Vec<RecognizedTactic>) {
    match term {
        CicTerm::App(f, args) if matches!(f.as_ref(), CicTerm::Const(_)) => {
            let name = match f.as_ref() {
                CicTerm::Const(n) => n,
                _ => unreachable!(),
            };
            match name.as_str() {
                "eq_refl" => t.push(RecognizedTactic::Reflexivity),
                "eq_sym" => t.push(RecognizedTactic::Symmetry),
                "eq_trans" => {
                    t.push(RecognizedTactic::Transitivity);
                    for a in args {
                        analyze_inner(a, t);
                    }
                }
                "eq_ind" => t.push(RecognizedTactic::Rewrite(
                    find_const_in_args(args).unwrap_or_default(),
                    Direction::Forward,
                )),
                "eq_ind_r" => t.push(RecognizedTactic::Rewrite(
                    find_const_in_args(args).unwrap_or_default(),
                    Direction::Backward,
                )),
                "False_ind" | "False_rect" | "absurd" => {
                    t.push(RecognizedTactic::Apply("False_ind".into()))
                }
                n if is_mathverse_const(n) => t.push(RecognizedTactic::Mathverse),
                n if n.ends_with("_ind") || n.ends_with("_rec") || n.ends_with("_rect") => {
                    t.push(RecognizedTactic::Induction(
                        n.to_owned(),
                        induction_arg(args),
                    ));
                    for a in args {
                        analyze_inner(a, t);
                    }
                }
                _ => {
                    t.push(RecognizedTactic::Apply(name.clone()));
                    for a in args {
                        analyze_inner(a, t);
                    }
                }
            }
        }
        CicTerm::App(f, args) => {
            analyze_inner(f, t);
            for a in args {
                analyze_inner(a, t);
            }
        }
        CicTerm::Lambda(_, _, body) => analyze_inner(body, t),
        CicTerm::LetIn(_, val, _, body) => {
            t.push(RecognizedTactic::Simpl);
            analyze_inner(val, t);
            analyze_inner(body, t);
        }
        CicTerm::Case(case) => {
            t.push(RecognizedTactic::Destruct("?".into()));
            for b in &case.branches {
                analyze_inner(b, t);
            }
        }
        CicTerm::Fix(bodies, _) => {
            t.push(RecognizedTactic::Induction("fix".into(), 0));
            for (_, _, b) in bodies {
                analyze_inner(b, t);
            }
        }
        CicTerm::Rel(_) => t.push(RecognizedTactic::Assumption),
        _ => {}
    }
}

fn is_mathverse_const(n: &str) -> bool {
    n.starts_with("Coq.mathverse.")
        || n.starts_with("Coq.micrmathverse.")
        || n == "mathverse_nat"
        || n == "lia"
        || n.starts_with("ZArith_dec.")
}

fn proof_depth(term: &CicTerm) -> u32 {
    match term {
        CicTerm::App(f, args) => {
            1 + proof_depth(f).max(args.iter().map(proof_depth).max().unwrap_or(0))
        }
        CicTerm::Lambda(_, _, b) | CicTerm::Prod(_, _, b) => 1 + proof_depth(b),
        CicTerm::LetIn(_, v, _, b) => 1 + proof_depth(v).max(proof_depth(b)),
        CicTerm::Case(case) => 1 + case.branches.iter().map(proof_depth).max().unwrap_or(0),
        CicTerm::Fix(bs, _) | CicTerm::CoFix(bs, _) => {
            1 + bs.iter().map(|(_, _, b)| proof_depth(b)).max().unwrap_or(0)
        }
        _ => 0,
    }
}

// -- Vernacular stream import -------------------------------------------------

/// Import a stream of Coq vernacular commands into a shard.
pub fn import_vernacular_stream(
    commands: &[CoqVernacular],
    module_path: &str,
    writer: &mut ShardWriter,
) -> MathverseResult<CoqImportStats> {
    let mp = classify_coq_module(module_path);
    let mut s = CoqImportStats::default();
    for cmd in commands {
        s.total += 1;
        match cmd {
            CoqVernacular::Definition { name, type_, body } => {
                emit(
                    writer,
                    name,
                    type_,
                    Some(body),
                    mp,
                    crate::types::DeclKind::Definition,
                );
                s.translated += 1;
            }
            CoqVernacular::Lemma { name, type_, proof }
            | CoqVernacular::Theorem { name, type_, proof } => {
                if let Some(pf) = proof {
                    emit(
                        writer,
                        name,
                        type_,
                        Some(pf),
                        mp,
                        crate::types::DeclKind::Theorem,
                    );
                    s.translated += 1;
                } else {
                    emit(
                        writer,
                        name,
                        type_,
                        None,
                        mp,
                        crate::types::DeclKind::Theorem,
                    );
                    s.axiomatized += 1;
                }
            }
            CoqVernacular::Axiom { name, type_ } | CoqVernacular::Opaque { name, type_ } => {
                emit(
                    writer,
                    name,
                    type_,
                    None,
                    mp | AxiomProfile::AXIOMATIZED,
                    crate::types::DeclKind::Axiom,
                );
                s.axiomatized += 1;
            }
            CoqVernacular::Inductive(mind) => {
                let n = import_mutual_inductive(mind, module_path, writer)?.len() as u32;
                s.translated += n;
                s.total += n.saturating_sub(1);
            }
            CoqVernacular::Fixpoint {
                name, type_, body, ..
            } => {
                emit(
                    writer,
                    name,
                    type_,
                    Some(body),
                    mp,
                    crate::types::DeclKind::Definition,
                );
                s.translated += 1;
            }
            CoqVernacular::Instance {
                name,
                type_,
                body,
                class,
            } => {
                let full = format!("{name} [instance: {class}]");
                emit(
                    writer,
                    &full,
                    type_,
                    Some(body),
                    mp,
                    crate::types::DeclKind::Definition,
                );
                s.translated += 1;
            }
            CoqVernacular::Record { name, fields, .. } => {
                let sort = CicTerm::Sort(CicSort::type_at(0));
                emit(
                    writer,
                    name,
                    &sort,
                    None,
                    mp,
                    crate::types::DeclKind::Inductive,
                );
                // Record field projections are definitions (accessors), not constructors.
                for (f, ty) in fields {
                    emit(
                        writer,
                        &format!("{name}.{f}"),
                        ty,
                        None,
                        mp,
                        crate::types::DeclKind::Definition,
                    );
                }
                s.translated += 1 + fields.len() as u32;
                s.total += fields.len() as u32;
            }
        }
    }
    Ok(s)
}

fn emit(
    w: &mut ShardWriter,
    name: &str,
    ty: &CicTerm,
    val: Option<&CicTerm>,
    profile: AxiomProfile,
    kind: crate::types::DeclKind,
) {
    let type_idx = cic_to_flat_expr(ty, w);
    let (value_idx, confidence) = match val {
        Some(v) => (cic_to_flat_expr(v, w), ImportConfidence::Translated),
        None => (NO_VALUE, ImportConfidence::Axiomatized),
    };
    let name_idx = w.add_string(name);
    w.add_constant(MathverseConstantHeader {
        name_idx,
        type_idx,
        value_idx,
        source_system: SourceSystem::Coq as u8,
        import_confidence: confidence as u8,
        content_domain: ContentDomain::PureMath as u8,
        decl_kind: kind as u8,
        axiom_profile: profile,
        sidecar_digest: 0,
        provenance_idx: 0,
        level_params_start: 0,
        level_params_count: 0,
        _pad2: [0u8; 26],
    });
}

// -- Helpers ------------------------------------------------------------------

fn vern_err(reason: &str) -> MathverseError {
    MathverseError::ImportFailed {
        system: "Coq/Vernacular".into(),
        reason: reason.into(),
    }
}
fn atom(items: &[Sexp], i: usize) -> Result<String, MathverseError> {
    match items.get(i) {
        Some(Sexp::Atom(s)) => Ok(s.clone()),
        _ => Err(vern_err(&format!("expected atom at {i}"))),
    }
}
fn req(items: &[Sexp], min: usize, cmd: &str) -> Result<(), MathverseError> {
    if items.len() < min {
        Err(vern_err(&format!("{cmd}: need {min}, got {}", items.len())))
    } else {
        Ok(())
    }
}

fn parse_binders(sexp: &Sexp) -> Result<Vec<(String, CicTerm)>, MathverseError> {
    let items = match sexp {
        Sexp::List(v) => v,
        _ => return Err(vern_err("expected binder list")),
    };
    let mut out = Vec::new();
    for item in items {
        if let Sexp::List(pair) = item {
            if pair.len() >= 2 {
                if let Sexp::Atom(n) = &pair[0] {
                    out.push((n.clone(), sexp_to_cic(&pair[1])?));
                }
            }
        }
    }
    Ok(out)
}

// -- Tactic translation table -------------------------------------------------

/// A single entry mapping a Coq tactic to its clean equivalent.
#[derive(Clone, Debug)]
pub struct CoqTacticEntry {
    /// Coq tactic name (lowercase, canonical form).
    pub coq_name: String,
    /// clean tactic equivalent.
    pub lean_equiv: String,
    /// Translation confidence (0.0 = speculative, 1.0 = exact semantic match).
    pub confidence: f64,
    /// Additional notes on translation caveats or behavioral differences.
    pub notes: String,
}

/// Mapping from Coq tactic names to clean equivalents.
///
/// Covers 30+ common Coq tactics used in Ltac proof scripts.
/// Confidence scores reflect semantic fidelity: 1.0 means the clean tactic
/// has identical behavior, lower values indicate approximate translations
/// that may require manual adjustment.
pub struct CoqTacticMap {
    entries: HashMap<String, CoqTacticEntry>,
}

impl CoqTacticMap {
    /// Build the default tactic translation table.
    pub fn new() -> Self {
        let mut entries = HashMap::new();
        let table: &[(&str, &str, f64, &str)] = &[
            (
                "rewrite",
                "rw",
                0.95,
                "Lean rw applies left-to-right by default; use rw [<-] for reverse",
            ),
            (
                "apply",
                "exact",
                0.9,
                "Lean exact requires full term; apply also works for partial",
            ),
            ("induction", "induction", 1.0, "Direct equivalent"),
            (
                "destruct",
                "cases",
                0.9,
                "Lean cases is the closest match; rcases for deeper patterns",
            ),
            (
                "simpl",
                "simp",
                0.85,
                "Lean simp is more aggressive; may need simp only [...]",
            ),
            (
                "auto",
                "auto",
                0.8,
                "Lean auto is less powerful than Coq's; consider aesop",
            ),
            (
                "mathverse",
                "mathverse",
                1.0,
                "Direct equivalent for linear arithmetic",
            ),
            (
                "lia",
                "mathverse",
                0.95,
                "Coq lia maps to Lean mathverse; both handle linear integer arithmetic",
            ),
            (
                "intros",
                "intro",
                0.95,
                "Lean intro takes one name at a time; use repeated intro or rintro",
            ),
            ("unfold", "unfold", 1.0, "Direct equivalent"),
            (
                "split",
                "constructor",
                0.9,
                "Lean constructor generalizes split to any single-constructor type",
            ),
            ("left", "left", 1.0, "Direct equivalent"),
            ("right", "right", 1.0, "Direct equivalent"),
            (
                "exists",
                "use",
                0.9,
                "Lean use provides the witness; exact <witness, proof> also works",
            ),
            (
                "assert",
                "have",
                0.95,
                "Lean have introduces intermediate goals similarly",
            ),
            ("ring", "ring", 1.0, "Direct equivalent"),
            (
                "field",
                "field",
                0.9,
                "Lean field_simp may be needed for some field goals",
            ),
            (
                "discriminate",
                "contradiction",
                0.85,
                "Lean contradiction covers discriminate cases; exact absurd also works",
            ),
            ("injection", "injection", 1.0, "Direct equivalent"),
            (
                "f_equal",
                "congr",
                0.9,
                "Lean congr generalizes f_equal to arbitrary congruence",
            ),
            ("exfalso", "exfalso", 1.0, "Direct equivalent"),
            ("clear", "clear", 1.0, "Direct equivalent"),
            (
                "rename",
                "rename",
                0.9,
                "Lean rename_i for inaccessible names",
            ),
            (
                "pose",
                "let",
                0.85,
                "Lean let introduces a local definition; have for propositions",
            ),
            ("generalize", "generalize", 1.0, "Direct equivalent"),
            ("specialize", "specialize", 1.0, "Direct equivalent"),
            (
                "eauto",
                "aesop",
                0.7,
                "Lean aesop is the closest automation; behavior differs significantly",
            ),
            (
                "tauto",
                "tauto",
                0.95,
                "Lean tauto handles propositional logic similarly",
            ),
            (
                "congruence",
                "congr",
                0.8,
                "Lean congr is less automated; may need ext or funext",
            ),
            (
                "trivial",
                "trivial",
                0.9,
                "Lean trivial is weaker; consider exact? or assumption",
            ),
            ("reflexivity", "rfl", 1.0, "Direct equivalent"),
            ("symmetry", "symm", 1.0, "Direct equivalent"),
            (
                "transitivity",
                "trans",
                0.95,
                "Lean trans requires the intermediate term explicitly",
            ),
        ];
        for &(coq, lean, conf, notes) in table {
            entries.insert(
                coq.to_owned(),
                CoqTacticEntry {
                    coq_name: coq.to_owned(),
                    lean_equiv: lean.to_owned(),
                    confidence: conf,
                    notes: notes.to_owned(),
                },
            );
        }
        Self { entries }
    }

    /// Look up a Coq tactic by name. Returns `None` if no mapping exists.
    pub fn lookup(&self, coq_tactic: &str) -> Option<&CoqTacticEntry> {
        self.entries.get(coq_tactic)
    }

    /// Look up a Coq tactic and return the clean equivalent string.
    pub fn translate(&self, coq_tactic: &str) -> Option<&str> {
        self.entries.get(coq_tactic).map(|e| e.lean_equiv.as_str())
    }

    /// Return all entries with confidence >= the given threshold.
    pub fn high_confidence(&self, threshold: f64) -> Vec<&CoqTacticEntry> {
        self.entries
            .values()
            .filter(|e| e.confidence >= threshold)
            .collect()
    }

    /// Number of tactic mappings in the table.
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// Whether the table is empty.
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// Translate a recognized tactic enum into a clean tactic string.
    pub fn translate_recognized(&self, tactic: &RecognizedTactic) -> String {
        match tactic {
            RecognizedTactic::Rewrite(lemma, dir) => {
                let arrow = match dir {
                    Direction::Forward => "",
                    Direction::Backward => "<- ",
                };
                format!("rw [{arrow}{lemma}]")
            }
            RecognizedTactic::Apply(lemma) => format!("exact {lemma}"),
            RecognizedTactic::Induction(name, _) => format!("induction {name}"),
            RecognizedTactic::Destruct(name) => format!("cases {name}"),
            RecognizedTactic::Reflexivity => "rfl".to_owned(),
            RecognizedTactic::Symmetry => "symm".to_owned(),
            RecognizedTactic::Transitivity => "trans".to_owned(),
            RecognizedTactic::Assumption => "assumption".to_owned(),
            RecognizedTactic::Auto => "auto".to_owned(),
            RecognizedTactic::Mathverse => "mathverse".to_owned(),
            RecognizedTactic::Unfold(name) => format!("unfold {name}"),
            RecognizedTactic::Simpl => "simp".to_owned(),
        }
    }
}

impl Default for CoqTacticMap {
    fn default() -> Self {
        Self::new()
    }
}

// -- Proof obligation extraction -----------------------------------------------

/// A proof obligation extracted from a CIC term — a subgoal that needs solving.
#[derive(Clone, Debug)]
pub struct ProofObligation {
    /// The type of the goal to be proved.
    pub goal_type: CicTerm,
    /// Local context: variable name and its type.
    pub context: Vec<(String, CicTerm)>,
    /// Hint for which tactic might solve this obligation.
    pub tactic_hint: Option<String>,
}

/// Walk a CIC proof term and extract proof obligations (holes, underscores,
/// unresolved variables that represent subgoals).
///
/// Detects:
/// - `Var("_")` or `Var` names starting with `_` (underscore holes)
/// - `Rel` references in non-binding positions (potential unresolved goals)
/// - `App` of a constant to fewer arguments than expected (partial application holes)
/// - Lambda/Prod binders that create context entries
pub fn extract_proof_obligations(term: &CicTerm) -> Vec<ProofObligation> {
    let mut obligations = Vec::new();
    let mut context: Vec<(String, CicTerm)> = Vec::new();
    collect_obligations(term, &mut context, &mut obligations);
    obligations
}

fn collect_obligations(
    term: &CicTerm,
    context: &mut Vec<(String, CicTerm)>,
    obligations: &mut Vec<ProofObligation>,
) {
    match term {
        // Underscore variables are explicit holes.
        CicTerm::Var(name)
            if name == "_" || name.starts_with("_Unresolved") || name.starts_with("?") =>
        {
            obligations.push(ProofObligation {
                goal_type: CicTerm::Sort(CicSort::Prop),
                context: context.clone(),
                tactic_hint: Some("auto".to_owned()),
            });
        }
        // Lambda introduces a binder; the body may contain obligations.
        CicTerm::Lambda(name, ty, body) => {
            context.push((name.clone(), *ty.clone()));
            collect_obligations(body, context, obligations);
            context.pop();
        }
        // Prod (forall) introduces a binder similarly.
        CicTerm::Prod(name, ty, body) => {
            context.push((name.clone(), *ty.clone()));
            collect_obligations(body, context, obligations);
            context.pop();
        }
        // LetIn introduces a local definition; both value and body may have holes.
        CicTerm::LetIn(name, val, ty, body) => {
            collect_obligations(val, context, obligations);
            context.push((name.clone(), *ty.clone()));
            collect_obligations(body, context, obligations);
            context.pop();
        }
        // Application: check the function and each argument for holes.
        CicTerm::App(f, args) => {
            // If the function is a known constant and some args are holes,
            // record obligations for each hole argument.
            if let CicTerm::Const(fname) = f.as_ref() {
                for arg in args {
                    if is_hole_term(arg) {
                        let hint = tactic_hint_for_app(fname);
                        obligations.push(ProofObligation {
                            goal_type: arg.clone(),
                            context: context.clone(),
                            tactic_hint: Some(hint),
                        });
                    } else {
                        collect_obligations(arg, context, obligations);
                    }
                }
            } else {
                collect_obligations(f, context, obligations);
                for arg in args {
                    collect_obligations(arg, context, obligations);
                }
            }
        }
        // Case: discriminant, params, motive and each branch may contain holes.
        CicTerm::Case(case) => {
            collect_obligations(&case.discriminant, context, obligations);
            collect_obligations(&case.motive, context, obligations);
            for p in &case.params {
                collect_obligations(p, context, obligations);
            }
            for br in &case.branches {
                collect_obligations(br, context, obligations);
            }
        }
        // Fix/CoFix: each body may contain holes.
        CicTerm::Fix(bodies, _) | CicTerm::CoFix(bodies, _) => {
            for (name, ty, body) in bodies {
                context.push((name.clone(), *ty.clone()));
                collect_obligations(body, context, obligations);
                context.pop();
            }
        }
        // StructFix: motive, params and each minor-premise branch may contain holes.
        CicTerm::StructFix(fix) => {
            collect_obligations(&fix.motive, context, obligations);
            for p in &fix.params {
                collect_obligations(p, context, obligations);
            }
            for br in &fix.branches {
                collect_obligations(br, context, obligations);
            }
        }
        // Projection: the inner expression may contain holes.
        CicTerm::Proj(_, _, inner) => {
            collect_obligations(inner, context, obligations);
        }
        // Leaf nodes that are not holes: nothing to extract.
        CicTerm::Rel(_)
        | CicTerm::Var(_)
        | CicTerm::Sort(_)
        | CicTerm::Const(_)
        | CicTerm::ConstU(_, _)
        | CicTerm::Ind(_, _)
        | CicTerm::Construct(_, _, _)
        | CicTerm::Int(_)
        | CicTerm::Float(_) => {}
    }
}

/// Check if a CIC term represents a hole (underscore, unresolved variable, etc.).
fn is_hole_term(term: &CicTerm) -> bool {
    match term {
        CicTerm::Var(name) => {
            name == "_" || name.starts_with("_Unresolved") || name.starts_with("?")
        }
        _ => false,
    }
}

/// Suggest a tactic hint based on the function name in an application.
fn tactic_hint_for_app(fname: &str) -> String {
    match fname {
        "eq_ind" | "eq_ind_r" => "rw".to_owned(),
        "eq_refl" => "rfl".to_owned(),
        "False_ind" | "False_rect" | "absurd" => "contradiction".to_owned(),
        n if n.ends_with("_ind") || n.ends_with("_rec") => "induction".to_owned(),
        n if is_mathverse_const(n) => "mathverse".to_owned(),
        _ => "exact".to_owned(),
    }
}

// -- Ltac2 pattern recognition ------------------------------------------------

/// Recognized Ltac2 pattern from s-expression form.
///
/// Ltac2 is Coq's next-generation tactic language. These patterns cover
/// the most common structural forms found in serialized Ltac2 code.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Ltac2Pattern {
    /// `match <expr> with ...` — term-level pattern matching.
    Match {
        scrutinee: String,
        num_branches: usize,
    },
    /// `match goal with ...` — goal-level pattern matching.
    MatchGoal { num_patterns: usize },
    /// `constr:(...)` — quoted Gallina term.
    Constr(String),
    /// `@ident` or `ident` — identifier reference.
    Ident(String),
    /// Function application.
    App { func: String, num_args: usize },
    /// Sequential composition `t1 ; t2`.
    Seq { num_steps: usize },
    /// Alternation `t1 + t2` or `first [...]`.
    Or { num_alternatives: usize },
    /// `try t` — run tactic, absorb failure.
    Try,
    /// `fail` or `fail n "msg"` — explicit failure.
    Fail { level: u32, message: Option<String> },
    /// `progress t` — succeed only if tactic makes progress.
    Progress,
    /// `repeat t` — repeat until failure.
    Repeat,
}

/// Attempt to recognize a common Ltac2 pattern from an s-expression.
///
/// Expects patterns like:
/// - `(Match <scrutinee> <branch>...)` for term matching
/// - `(MatchGoal <pattern>...)` for goal matching
/// - `(Constr <term>)` for quoted terms
/// - `(Ident <name>)` for identifiers
/// - `(App <func> <arg>...)` for application
/// - `(Seq <step>...)` for sequential composition
/// - `(Or <alt>...)` for alternation
/// - `(Try <tactic>)` for try
/// - `(Fail <level> <msg>?)` for failure
/// - `(Progress <tactic>)` for progress check
/// - `(Repeat <tactic>)` for repetition
pub fn recognize_ltac2_pattern(sexp: &Sexp) -> Option<Ltac2Pattern> {
    let items = match sexp {
        Sexp::List(v) if !v.is_empty() => v,
        _ => return None,
    };
    let head = match &items[0] {
        Sexp::Atom(s) => s.as_str(),
        _ => return None,
    };
    match head {
        "Match" | "match" => {
            let scrutinee = match items.get(1) {
                Some(Sexp::Atom(s)) => s.clone(),
                Some(Sexp::List(_)) => "<expr>".to_owned(),
                _ => return None,
            };
            let num_branches = items.len().saturating_sub(2);
            Some(Ltac2Pattern::Match {
                scrutinee,
                num_branches,
            })
        }
        "MatchGoal" | "match_goal" | "lazymatch_goal" => {
            let num_patterns = items.len().saturating_sub(1);
            Some(Ltac2Pattern::MatchGoal { num_patterns })
        }
        "Constr" | "constr" | "open_constr" => {
            let repr = match items.get(1) {
                Some(Sexp::Atom(s)) => s.clone(),
                Some(s) => format!("{s:?}"),
                None => return None,
            };
            Some(Ltac2Pattern::Constr(repr))
        }
        "Ident" | "ident" => {
            let name = match items.get(1) {
                Some(Sexp::Atom(s)) => s.clone(),
                _ => return None,
            };
            Some(Ltac2Pattern::Ident(name))
        }
        "App" | "app" => {
            let func = match items.get(1) {
                Some(Sexp::Atom(s)) => s.clone(),
                Some(Sexp::List(inner)) => {
                    // Nested function expression — extract head if possible.
                    match inner.first() {
                        Some(Sexp::Atom(s)) => s.clone(),
                        _ => "<fn>".to_owned(),
                    }
                }
                _ => return None,
            };
            let num_args = items.len().saturating_sub(2);
            Some(Ltac2Pattern::App { func, num_args })
        }
        "Seq" | "seq" => {
            let num_steps = items.len().saturating_sub(1);
            Some(Ltac2Pattern::Seq { num_steps })
        }
        "Or" | "or" | "first" | "+" => {
            let num_alternatives = items.len().saturating_sub(1);
            Some(Ltac2Pattern::Or { num_alternatives })
        }
        "Try" | "try" => Some(Ltac2Pattern::Try),
        "Fail" | "fail" => {
            let level = match items.get(1) {
                Some(Sexp::Atom(s)) => s.parse::<u32>().unwrap_or(0),
                _ => 0,
            };
            let message = match items.get(2) {
                Some(Sexp::Atom(s)) => Some(s.clone()),
                _ => None,
            };
            Some(Ltac2Pattern::Fail { level, message })
        }
        "Progress" | "progress" => Some(Ltac2Pattern::Progress),
        "Repeat" | "repeat" => Some(Ltac2Pattern::Repeat),
        _ => None,
    }
}

// -- Tests --------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::coq::alpha::parse_sexp;
    fn s(input: &str) -> Sexp {
        parse_sexp(input).expect("valid sexp")
    }
    fn app(name: &str, args: Vec<CicTerm>) -> CicTerm {
        CicTerm::App(Box::new(CicTerm::Const(name.into())), args)
    }

    // Vernacular parsing
    #[test]
    fn test_parse_definition() {
        let v = parse_vernacular(&s("(CoqDefinition my_id (Prod A (Sort (Type 0)) (Prod x (Rel 0) (Rel 0))) (Lambda A (Sort (Type 0)) (Lambda x (Rel 0) (Rel 0))))")).unwrap();
        assert!(matches!(v, CoqVernacular::Definition { name, .. } if name == "my_id"));
    }
    #[test]
    fn test_parse_lemma_with_proof() {
        let v = parse_vernacular(&s(
            "(CoqLemma my_lemma (Sort Prop) (App (Const eq_refl) (Rel 0)))",
        ))
        .unwrap();
        assert!(
            matches!(v, CoqVernacular::Lemma { name, proof: Some(_), .. } if name == "my_lemma")
        );
    }
    #[test]
    fn test_parse_lemma_without_proof() {
        assert!(matches!(
            parse_vernacular(&s("(CoqLemma my_lemma (Sort Prop))")).unwrap(),
            CoqVernacular::Lemma { proof: None, .. }
        ));
    }
    #[test]
    fn test_parse_theorem() {
        assert!(
            matches!(parse_vernacular(&s("(CoqTheorem thm1 (Sort Prop) (App (Const eq_refl) (Sort Prop)))")).unwrap(), CoqVernacular::Theorem { name, proof: Some(_), .. } if name == "thm1")
        );
    }
    #[test]
    fn test_parse_axiom() {
        assert!(
            matches!(parse_vernacular(&s("(CoqAxiom classic (Sort Prop))")).unwrap(), CoqVernacular::Axiom { name, .. } if name == "classic")
        );
    }
    #[test]
    fn test_parse_inductive() {
        match parse_vernacular(&s("(CoqInductive (MutualInductive (Params) (Body nat (Sort (Type 0)) (Ctor O (Sort (Type 0))))))")).unwrap() {
            CoqVernacular::Inductive(mind) => { assert_eq!(mind.bodies.len(), 1); assert_eq!(mind.bodies[0].name, "nat"); }
            other => panic!("expected Inductive, got {other:?}"),
        }
    }
    #[test]
    fn test_parse_fixpoint() {
        match parse_vernacular(&s("(CoqFixpoint add (Prod n (Sort (Type 0)) (Sort (Type 0))) (Lambda n (Sort (Type 0)) (Rel 0)) 0)")).unwrap() {
            CoqVernacular::Fixpoint { name, decreasing_arg, .. } => { assert_eq!(name, "add"); assert_eq!(decreasing_arg, 0); }
            other => panic!("expected Fixpoint, got {other:?}"),
        }
    }
    #[test]
    fn test_parse_instance() {
        match parse_vernacular(&s(
            "(CoqInstance my_inst Monad (Sort (Type 0)) (Lambda x (Sort (Type 0)) (Rel 0)))",
        ))
        .unwrap()
        {
            CoqVernacular::Instance { name, class, .. } => {
                assert_eq!(name, "my_inst");
                assert_eq!(class, "Monad");
            }
            other => panic!("expected Instance, got {other:?}"),
        }
    }
    #[test]
    fn test_parse_record() {
        match parse_vernacular(&s(
            "(CoqRecord point ((A (Sort (Type 0)))) ((x (Rel 0)) (y (Rel 0))))",
        ))
        .unwrap()
        {
            CoqVernacular::Record {
                name,
                params,
                fields,
            } => {
                assert_eq!(name, "point");
                assert_eq!(params.len(), 1);
                assert_eq!(fields.len(), 2);
                assert_eq!(fields[0].0, "x");
            }
            other => panic!("expected Record, got {other:?}"),
        }
    }
    #[test]
    fn test_parse_opaque() {
        assert!(
            matches!(parse_vernacular(&s("(CoqOpaque secret (Sort Prop))")).unwrap(), CoqVernacular::Opaque { name, .. } if name == "secret")
        );
    }
    #[test]
    fn test_parse_vernacular_errors() {
        assert!(parse_vernacular(&s("()")).is_err());
        assert!(parse_vernacular(&Sexp::Atom("bad".into())).is_err());
        assert!(parse_vernacular(&s("(CoqUnknown x y)")).is_err());
        assert!(parse_vernacular(&s("(CoqDefinition x)")).is_err());
    }

    // Proof skeleton extraction
    #[test]
    fn test_skeleton_reflexivity() {
        let sk = extract_proof_skeleton(&app("eq_refl", vec![CicTerm::Sort(CicSort::Prop)]));
        assert_eq!(sk.difficulty, DifficultyEstimate::Easy);
        assert!(sk.strategy.is_empty());
    }
    #[test]
    fn test_skeleton_rewrite() {
        let sk = extract_proof_skeleton(&app(
            "eq_ind",
            vec![
                CicTerm::Sort(CicSort::Prop),
                CicTerm::Const("add_comm".into()),
                CicTerm::Rel(0),
            ],
        ));
        assert!(sk.strategy.iter().any(|s| matches!(
            s,
            ProofStep::Rewrite {
                direction: Direction::Forward,
                ..
            }
        )));
        assert!(sk.key_lemmas.iter().any(|(n, _)| n == "add_comm"));
    }
    #[test]
    fn test_skeleton_backward_rewrite() {
        let sk = extract_proof_skeleton(&app(
            "eq_ind_r",
            vec![
                CicTerm::Sort(CicSort::Prop),
                CicTerm::Const("mul_comm".into()),
            ],
        ));
        assert!(sk.strategy.iter().any(|s| matches!(
            s,
            ProofStep::Rewrite {
                direction: Direction::Backward,
                ..
            }
        )));
    }
    #[test]
    fn test_skeleton_induction() {
        let sk = extract_proof_skeleton(&app(
            "nat_ind",
            vec![
                CicTerm::Sort(CicSort::Prop),
                CicTerm::Rel(0),
                CicTerm::Lambda(
                    "n".into(),
                    Box::new(CicTerm::Sort(CicSort::type_at(0))),
                    Box::new(CicTerm::Rel(0)),
                ),
                CicTerm::Rel(1),
            ],
        ));
        assert!(sk
            .strategy
            .iter()
            .any(|s| matches!(s, ProofStep::Induction { .. })));
        assert!(sk.key_lemmas.iter().any(|(n, _)| n == "nat_ind"));
        assert!(sk.difficulty >= DifficultyEstimate::Medium);
    }
    #[test]
    fn test_skeleton_case_split() {
        let sk = extract_proof_skeleton(&CicTerm::Case(Box::new(CicCase {
            ind_name: "or".into(),
            ind_idx: 0,
            params: vec![],
            motive: Box::new(CicTerm::Sort(CicSort::Prop)),
            branches: vec![CicTerm::Rel(1), CicTerm::Rel(2)],
            discriminant: Box::new(CicTerm::Rel(0)),
        })));
        assert!(sk
            .strategy
            .iter()
            .any(|s| matches!(s, ProofStep::CaseSplit { num_cases: 2 })));
    }
    #[test]
    fn test_skeleton_contradiction() {
        let sk = extract_proof_skeleton(&app(
            "False_ind",
            vec![CicTerm::Sort(CicSort::Prop), CicTerm::Rel(0)],
        ));
        assert!(sk
            .strategy
            .iter()
            .any(|s| matches!(s, ProofStep::Contradiction)));
    }
    #[test]
    fn test_skeleton_let_computation() {
        let sk = extract_proof_skeleton(&CicTerm::LetIn(
            "x".into(),
            Box::new(CicTerm::Int(42)),
            Box::new(CicTerm::Sort(CicSort::type_at(0))),
            Box::new(CicTerm::Rel(0)),
        ));
        assert!(sk
            .strategy
            .iter()
            .any(|s| matches!(s, ProofStep::Computation)));
    }
    #[test]
    fn test_skeleton_fix_induction() {
        let sk = extract_proof_skeleton(&CicTerm::Fix(
            vec![(
                "f".into(),
                Box::new(CicTerm::Sort(CicSort::Prop)),
                Box::new(CicTerm::Rel(0)),
            )],
            0,
        ));
        assert!(sk
            .strategy
            .iter()
            .any(|s| matches!(s, ProofStep::Induction { .. })));
    }

    // Difficulty estimation
    #[test]
    fn test_difficulty_easy() {
        assert_eq!(
            estimate_difficulty(&[ProofStep::Apply { lemma: None }]),
            DifficultyEstimate::Easy
        );
    }
    #[test]
    fn test_difficulty_medium() {
        assert_eq!(
            estimate_difficulty(&[
                ProofStep::Induction { on_arg: 0 },
                ProofStep::Apply { lemma: None },
                ProofStep::Apply { lemma: None },
                ProofStep::Apply { lemma: None }
            ]),
            DifficultyEstimate::Medium
        );
    }
    #[test]
    fn test_difficulty_hard() {
        assert_eq!(
            estimate_difficulty(&[
                ProofStep::Induction { on_arg: 0 },
                ProofStep::Induction { on_arg: 1 },
                ProofStep::CaseSplit { num_cases: 3 }
            ]),
            DifficultyEstimate::Hard
        );
    }
    #[test]
    fn test_difficulty_unknown() {
        assert_eq!(
            estimate_difficulty(&[
                ProofStep::Induction { on_arg: 0 },
                ProofStep::Induction { on_arg: 1 },
                ProofStep::Induction { on_arg: 2 }
            ]),
            DifficultyEstimate::Unknown
        );
    }

    // Tactic recognition
    #[test]
    fn test_tactic_reflexivity() {
        assert!(
            analyze_proof_tactics(&app("eq_refl", vec![CicTerm::Sort(CicSort::Prop)]))
                .contains(&RecognizedTactic::Reflexivity)
        );
    }
    #[test]
    fn test_tactic_rewrite_forward() {
        let t = analyze_proof_tactics(&app(
            "eq_ind",
            vec![CicTerm::Const("add_zero".into()), CicTerm::Rel(0)],
        ));
        assert!(t.iter().any(
            |x| matches!(x, RecognizedTactic::Rewrite(n, Direction::Forward) if n == "add_zero")
        ));
    }
    #[test]
    fn test_tactic_rewrite_backward() {
        let t = analyze_proof_tactics(&app("eq_ind_r", vec![CicTerm::Const("mul_one".into())]));
        assert!(t.iter().any(
            |x| matches!(x, RecognizedTactic::Rewrite(n, Direction::Backward) if n == "mul_one")
        ));
    }
    #[test]
    fn test_tactic_apply() {
        assert!(
            analyze_proof_tactics(&app("some_lemma", vec![CicTerm::Rel(0)]))
                .iter()
                .any(|x| matches!(x, RecognizedTactic::Apply(n) if n == "some_lemma"))
        );
    }
    #[test]
    fn test_tactic_induction() {
        assert!(analyze_proof_tactics(&app(
            "nat_ind",
            vec![CicTerm::Sort(CicSort::Prop), CicTerm::Rel(0)]
        ))
        .iter()
        .any(|x| matches!(x, RecognizedTactic::Induction(n, _) if n == "nat_ind")));
    }
    #[test]
    fn test_tactic_destruct() {
        let t = analyze_proof_tactics(&CicTerm::Case(Box::new(CicCase {
            ind_name: "or".into(),
            ind_idx: 0,
            params: vec![],
            motive: Box::new(CicTerm::Sort(CicSort::Prop)),
            branches: vec![CicTerm::Rel(1), CicTerm::Rel(2)],
            discriminant: Box::new(CicTerm::Rel(0)),
        })));
        assert!(t.iter().any(|x| matches!(x, RecognizedTactic::Destruct(_))));
    }
    #[test]
    fn test_tactic_symmetry() {
        assert!(analyze_proof_tactics(&app("eq_sym", vec![CicTerm::Rel(0)]))
            .contains(&RecognizedTactic::Symmetry));
    }
    #[test]
    fn test_tactic_mathverse() {
        assert!(analyze_proof_tactics(&app(
            "Coq.mathverse.MathverseLemmas.foo",
            vec![CicTerm::Rel(0)]
        ))
        .contains(&RecognizedTactic::Mathverse));
    }
    #[test]
    fn test_tactic_auto_trivial() {
        let t = analyze_proof_tactics(&CicTerm::Rel(0));
        assert!(t.contains(&RecognizedTactic::Assumption) || t.contains(&RecognizedTactic::Auto));
    }
    #[test]
    fn test_tactic_simpl_via_letin() {
        let t = analyze_proof_tactics(&CicTerm::LetIn(
            "x".into(),
            Box::new(CicTerm::Int(1)),
            Box::new(CicTerm::Sort(CicSort::type_at(0))),
            Box::new(CicTerm::Rel(0)),
        ));
        assert!(t.contains(&RecognizedTactic::Simpl));
    }

    // Vernacular stream import
    #[test]
    fn test_import_empty() {
        let mut w = ShardWriter::new();
        assert_eq!(
            import_vernacular_stream(&[], "Coq.Init", &mut w)
                .unwrap()
                .total,
            0
        );
    }
    #[test]
    fn test_import_definition() {
        let cmd = parse_vernacular(&s("(CoqDefinition id (Prod A (Sort (Type 0)) (Prod x (Rel 0) (Rel 0))) (Lambda A (Sort (Type 0)) (Lambda x (Rel 0) (Rel 0))))")).unwrap();
        let mut w = ShardWriter::new();
        let st = import_vernacular_stream(&[cmd], "Coq.Init", &mut w).unwrap();
        assert_eq!((st.total, st.translated), (1, 1));
    }
    #[test]
    fn test_import_axiom() {
        let cmd = parse_vernacular(&s("(CoqAxiom classic (Sort Prop))")).unwrap();
        let mut w = ShardWriter::new();
        assert_eq!(
            import_vernacular_stream(&[cmd], "Coq.Logic.Classical", &mut w)
                .unwrap()
                .axiomatized,
            1
        );
    }
    #[test]
    fn test_import_mixed_stream() {
        let cmds = vec![
            parse_vernacular(&s("(CoqDefinition f (Sort Prop) (Sort Prop))")).unwrap(),
            parse_vernacular(&s("(CoqAxiom ax (Sort Prop))")).unwrap(),
            parse_vernacular(&s(
                "(CoqTheorem thm (Sort Prop) (App (Const eq_refl) (Sort Prop)))",
            ))
            .unwrap(),
            parse_vernacular(&s("(CoqOpaque opq (Sort Prop))")).unwrap(),
        ];
        let mut w = ShardWriter::new();
        let st = import_vernacular_stream(&cmds, "Coq.Init", &mut w).unwrap();
        assert_eq!((st.total, st.translated, st.axiomatized), (4, 2, 2));
    }
    #[test]
    fn test_import_record() {
        let cmd = parse_vernacular(&s(
            "(CoqRecord point ((A (Sort (Type 0)))) ((x (Rel 0)) (y (Rel 0))))",
        ))
        .unwrap();
        let mut w = ShardWriter::new();
        let st = import_vernacular_stream(&[cmd], "Coq.Init", &mut w).unwrap();
        assert_eq!((st.total, st.translated), (3, 3)); // record + 2 fields
    }
    #[test]
    fn test_import_shard_roundtrip() {
        let cmds = vec![
            parse_vernacular(&s("(CoqDefinition f (Sort Prop) (Sort Prop))")).unwrap(),
            parse_vernacular(&s("(CoqAxiom ax (Sort Prop))")).unwrap(),
        ];
        let mut w = ShardWriter::new();
        import_vernacular_stream(&cmds, "Coq.Init", &mut w).unwrap();
        let mut buf = Vec::new();
        w.write(&mut buf).unwrap();
        let reader = crate::shard::ShardReader::from_bytes(&buf).unwrap();
        assert_eq!(reader.header.constant_count, 2);
        assert!(reader.constants[0].has_value());
        assert!(!reader.constants[1].has_value());
    }
    #[test]
    fn test_skeleton_roundtrip_serde() {
        let sk = extract_proof_skeleton(&app(
            "nat_ind",
            vec![
                CicTerm::Sort(CicSort::Prop),
                CicTerm::Rel(0),
                CicTerm::Lambda(
                    "n".into(),
                    Box::new(CicTerm::Sort(CicSort::type_at(0))),
                    Box::new(CicTerm::Rel(0)),
                ),
                CicTerm::Rel(1),
            ],
        ));
        let json = serde_json::to_string(&sk).expect("serialize");
        let restored: ProofSkeleton = serde_json::from_str(&json).expect("deserialize");
        assert_eq!(sk.difficulty, restored.difficulty);
        assert_eq!(sk.strategy.len(), restored.strategy.len());
        assert_eq!(sk.key_lemmas.len(), restored.key_lemmas.len());
    }

    // -- Tactic map tests -------------------------------------------------

    #[test]
    fn test_tactic_map_has_30_plus_entries() {
        let map = CoqTacticMap::new();
        assert!(map.len() >= 30, "expected 30+ entries, got {}", map.len());
        assert!(!map.is_empty());
    }

    #[test]
    fn test_tactic_map_default_trait() {
        let map = CoqTacticMap::default();
        assert!(map.len() >= 30);
    }

    #[test]
    fn test_tactic_map_rewrite() {
        let map = CoqTacticMap::new();
        let entry = map.lookup("rewrite").expect("rewrite should exist");
        assert_eq!(entry.lean_equiv, "rw");
        assert!(entry.confidence > 0.9);
    }

    #[test]
    fn test_tactic_map_translate_direct_equivalents() {
        let map = CoqTacticMap::new();
        assert_eq!(map.translate("mathverse"), Some("mathverse"));
        assert_eq!(map.translate("left"), Some("left"));
        assert_eq!(map.translate("right"), Some("right"));
        assert_eq!(map.translate("unfold"), Some("unfold"));
        assert_eq!(map.translate("reflexivity"), Some("rfl"));
        assert_eq!(map.translate("symmetry"), Some("symm"));
        assert_eq!(map.translate("exfalso"), Some("exfalso"));
        assert_eq!(map.translate("ring"), Some("ring"));
    }

    #[test]
    fn test_tactic_map_translate_renamed() {
        let map = CoqTacticMap::new();
        assert_eq!(map.translate("simpl"), Some("simp"));
        assert_eq!(map.translate("destruct"), Some("cases"));
        assert_eq!(map.translate("split"), Some("constructor"));
        assert_eq!(map.translate("exists"), Some("use"));
        assert_eq!(map.translate("assert"), Some("have"));
        assert_eq!(map.translate("lia"), Some("mathverse"));
        assert_eq!(map.translate("eauto"), Some("aesop"));
        assert_eq!(map.translate("pose"), Some("let"));
    }

    #[test]
    fn test_tactic_map_missing_lookup() {
        let map = CoqTacticMap::new();
        assert!(map.lookup("nonexistent_tactic").is_none());
        assert!(map.translate("zzzz").is_none());
    }

    #[test]
    fn test_tactic_map_high_confidence() {
        let map = CoqTacticMap::new();
        let perfect = map.high_confidence(1.0);
        // At least mathverse, induction, unfold, left, right, etc. have 1.0 confidence
        assert!(
            perfect.len() >= 8,
            "expected >=8 perfect entries, got {}",
            perfect.len()
        );
        for entry in &perfect {
            assert!((entry.confidence - 1.0).abs() < f64::EPSILON);
        }
    }

    #[test]
    fn test_tactic_map_all_entries_valid() {
        let map = CoqTacticMap::new();
        for entry in map.entries.values() {
            assert!(!entry.coq_name.is_empty(), "empty coq_name");
            assert!(
                !entry.lean_equiv.is_empty(),
                "empty lean_equiv for {}",
                entry.coq_name
            );
            assert!(
                entry.confidence >= 0.0 && entry.confidence <= 1.0,
                "confidence {} out of range for {}",
                entry.confidence,
                entry.coq_name
            );
            assert!(
                !entry.notes.is_empty(),
                "empty notes for {}",
                entry.coq_name
            );
        }
    }

    #[test]
    fn test_tactic_map_translate_recognized_rewrite() {
        let map = CoqTacticMap::new();
        let result = map.translate_recognized(&RecognizedTactic::Rewrite(
            "add_comm".into(),
            Direction::Forward,
        ));
        assert_eq!(result, "rw [add_comm]");
    }

    #[test]
    fn test_tactic_map_translate_recognized_rewrite_backward() {
        let map = CoqTacticMap::new();
        let result = map.translate_recognized(&RecognizedTactic::Rewrite(
            "mul_zero".into(),
            Direction::Backward,
        ));
        assert_eq!(result, "rw [<- mul_zero]");
    }

    #[test]
    fn test_tactic_map_translate_recognized_various() {
        let map = CoqTacticMap::new();
        assert_eq!(
            map.translate_recognized(&RecognizedTactic::Reflexivity),
            "rfl"
        );
        assert_eq!(
            map.translate_recognized(&RecognizedTactic::Symmetry),
            "symm"
        );
        assert_eq!(map.translate_recognized(&RecognizedTactic::Auto), "auto");
        assert_eq!(
            map.translate_recognized(&RecognizedTactic::Mathverse),
            "mathverse"
        );
        assert_eq!(map.translate_recognized(&RecognizedTactic::Simpl), "simp");
        assert_eq!(
            map.translate_recognized(&RecognizedTactic::Assumption),
            "assumption"
        );
    }

    // -- Proof obligation tests -------------------------------------------

    #[test]
    fn test_obligations_no_holes() {
        let term = app("eq_refl", vec![CicTerm::Sort(CicSort::Prop)]);
        let obs = extract_proof_obligations(&term);
        assert!(
            obs.is_empty(),
            "expected no obligations in a complete proof"
        );
    }

    #[test]
    fn test_obligations_underscore_hole() {
        let term = CicTerm::Var("_".into());
        let obs = extract_proof_obligations(&term);
        assert_eq!(obs.len(), 1);
        assert_eq!(obs[0].tactic_hint.as_deref(), Some("auto"));
    }

    #[test]
    fn test_obligations_unresolved_var() {
        let term = CicTerm::Var("_Unresolved_42".into());
        let obs = extract_proof_obligations(&term);
        assert_eq!(obs.len(), 1);
    }

    #[test]
    fn test_obligations_evar_style_hole() {
        let term = CicTerm::Var("?Goal".into());
        let obs = extract_proof_obligations(&term);
        assert_eq!(obs.len(), 1);
    }

    #[test]
    fn test_obligations_in_app_args() {
        let term = CicTerm::App(
            Box::new(CicTerm::Const("eq_ind".into())),
            vec![
                CicTerm::Rel(0),
                CicTerm::Var("_".into()),
                CicTerm::Var("_".into()),
            ],
        );
        let obs = extract_proof_obligations(&term);
        assert_eq!(
            obs.len(),
            2,
            "two hole arguments should produce two obligations"
        );
        // eq_ind holes should get "rw" hint
        assert_eq!(obs[0].tactic_hint.as_deref(), Some("rw"));
    }

    #[test]
    fn test_obligations_preserves_context() {
        let term = CicTerm::Lambda(
            "x".into(),
            Box::new(CicTerm::Sort(CicSort::type_at(0))),
            Box::new(CicTerm::Var("_".into())),
        );
        let obs = extract_proof_obligations(&term);
        assert_eq!(obs.len(), 1);
        assert_eq!(obs[0].context.len(), 1);
        assert_eq!(obs[0].context[0].0, "x");
    }

    #[test]
    fn test_obligations_nested_lambda_context() {
        let term = CicTerm::Lambda(
            "A".into(),
            Box::new(CicTerm::Sort(CicSort::type_at(0))),
            Box::new(CicTerm::Lambda(
                "x".into(),
                Box::new(CicTerm::Rel(0)),
                Box::new(CicTerm::Var("_".into())),
            )),
        );
        let obs = extract_proof_obligations(&term);
        assert_eq!(obs.len(), 1);
        assert_eq!(obs[0].context.len(), 2);
        assert_eq!(obs[0].context[0].0, "A");
        assert_eq!(obs[0].context[1].0, "x");
    }

    #[test]
    fn test_obligations_in_case_branches() {
        let term = CicTerm::Case(Box::new(CicCase {
            ind_name: "or".into(),
            ind_idx: 0,
            params: vec![],
            motive: Box::new(CicTerm::Sort(CicSort::Prop)),
            branches: vec![CicTerm::Var("_".into()), CicTerm::Rel(1)],
            discriminant: Box::new(CicTerm::Rel(0)),
        }));
        let obs = extract_proof_obligations(&term);
        assert_eq!(obs.len(), 1, "one branch has a hole");
    }

    #[test]
    fn test_obligations_in_letin() {
        let term = CicTerm::LetIn(
            "h".into(),
            Box::new(CicTerm::Var("_".into())),
            Box::new(CicTerm::Sort(CicSort::Prop)),
            Box::new(CicTerm::Rel(0)),
        );
        let obs = extract_proof_obligations(&term);
        assert_eq!(obs.len(), 1, "the let-value is a hole");
    }

    #[test]
    fn test_obligations_tactic_hint_for_false_ind() {
        let term = CicTerm::App(
            Box::new(CicTerm::Const("False_ind".into())),
            vec![CicTerm::Var("_".into())],
        );
        let obs = extract_proof_obligations(&term);
        assert_eq!(obs.len(), 1);
        assert_eq!(obs[0].tactic_hint.as_deref(), Some("contradiction"));
    }

    // -- Ltac2 pattern recognition tests ----------------------------------

    #[test]
    fn test_ltac2_match() {
        let sexp = s("(Match x (branch1) (branch2) (branch3))");
        let pat = recognize_ltac2_pattern(&sexp).expect("should recognize Match");
        assert_eq!(
            pat,
            Ltac2Pattern::Match {
                scrutinee: "x".into(),
                num_branches: 3
            }
        );
    }

    #[test]
    fn test_ltac2_match_goal() {
        let sexp = s("(MatchGoal (pattern1) (pattern2))");
        let pat = recognize_ltac2_pattern(&sexp).expect("should recognize MatchGoal");
        assert_eq!(pat, Ltac2Pattern::MatchGoal { num_patterns: 2 });
    }

    #[test]
    fn test_ltac2_constr() {
        let sexp = s("(Constr nat)");
        let pat = recognize_ltac2_pattern(&sexp).expect("should recognize Constr");
        assert_eq!(pat, Ltac2Pattern::Constr("nat".into()));
    }

    #[test]
    fn test_ltac2_ident() {
        let sexp = s("(Ident my_lemma)");
        let pat = recognize_ltac2_pattern(&sexp).expect("should recognize Ident");
        assert_eq!(pat, Ltac2Pattern::Ident("my_lemma".into()));
    }

    #[test]
    fn test_ltac2_app() {
        let sexp = s("(App apply_tac arg1 arg2)");
        let pat = recognize_ltac2_pattern(&sexp).expect("should recognize App");
        assert_eq!(
            pat,
            Ltac2Pattern::App {
                func: "apply_tac".into(),
                num_args: 2
            }
        );
    }

    #[test]
    fn test_ltac2_app_nested_func() {
        let sexp = s("(App (compose f g) x)");
        let pat = recognize_ltac2_pattern(&sexp).expect("should recognize App with nested func");
        assert_eq!(
            pat,
            Ltac2Pattern::App {
                func: "compose".into(),
                num_args: 1
            }
        );
    }

    #[test]
    fn test_ltac2_seq() {
        let sexp = s("(Seq step1 step2 step3)");
        let pat = recognize_ltac2_pattern(&sexp).expect("should recognize Seq");
        assert_eq!(pat, Ltac2Pattern::Seq { num_steps: 3 });
    }

    #[test]
    fn test_ltac2_or() {
        let sexp = s("(Or alt1 alt2)");
        let pat = recognize_ltac2_pattern(&sexp).expect("should recognize Or");
        assert_eq!(
            pat,
            Ltac2Pattern::Or {
                num_alternatives: 2
            }
        );
    }

    #[test]
    fn test_ltac2_first() {
        let sexp = s("(first tac1 tac2 tac3)");
        let pat = recognize_ltac2_pattern(&sexp).expect("should recognize first as Or");
        assert_eq!(
            pat,
            Ltac2Pattern::Or {
                num_alternatives: 3
            }
        );
    }

    #[test]
    fn test_ltac2_try() {
        let sexp = s("(Try (App auto))");
        let pat = recognize_ltac2_pattern(&sexp).expect("should recognize Try");
        assert_eq!(pat, Ltac2Pattern::Try);
    }

    #[test]
    fn test_ltac2_fail_simple() {
        let sexp = s("(Fail 0)");
        let pat = recognize_ltac2_pattern(&sexp).expect("should recognize Fail");
        assert_eq!(
            pat,
            Ltac2Pattern::Fail {
                level: 0,
                message: None
            }
        );
    }

    #[test]
    fn test_ltac2_fail_with_message() {
        let sexp = s("(Fail 1 \"not found\")");
        let pat = recognize_ltac2_pattern(&sexp).expect("should recognize Fail with msg");
        assert_eq!(
            pat,
            Ltac2Pattern::Fail {
                level: 1,
                message: Some("not found".into())
            }
        );
    }

    #[test]
    fn test_ltac2_progress() {
        let sexp = s("(Progress (App simpl))");
        let pat = recognize_ltac2_pattern(&sexp).expect("should recognize Progress");
        assert_eq!(pat, Ltac2Pattern::Progress);
    }

    #[test]
    fn test_ltac2_repeat() {
        let sexp = s("(Repeat (App auto))");
        let pat = recognize_ltac2_pattern(&sexp).expect("should recognize Repeat");
        assert_eq!(pat, Ltac2Pattern::Repeat);
    }

    #[test]
    fn test_ltac2_lowercase_variants() {
        assert_eq!(
            recognize_ltac2_pattern(&s("(match x (b))")).unwrap(),
            Ltac2Pattern::Match {
                scrutinee: "x".into(),
                num_branches: 1
            }
        );
        assert_eq!(
            recognize_ltac2_pattern(&s("(match_goal (p))")).unwrap(),
            Ltac2Pattern::MatchGoal { num_patterns: 1 }
        );
        assert_eq!(
            recognize_ltac2_pattern(&s("(constr nat)")).unwrap(),
            Ltac2Pattern::Constr("nat".into())
        );
        assert_eq!(
            recognize_ltac2_pattern(&s("(ident foo)")).unwrap(),
            Ltac2Pattern::Ident("foo".into())
        );
        assert_eq!(
            recognize_ltac2_pattern(&s("(try x)")).unwrap(),
            Ltac2Pattern::Try
        );
        assert_eq!(
            recognize_ltac2_pattern(&s("(progress x)")).unwrap(),
            Ltac2Pattern::Progress
        );
        assert_eq!(
            recognize_ltac2_pattern(&s("(repeat x)")).unwrap(),
            Ltac2Pattern::Repeat
        );
    }

    #[test]
    fn test_ltac2_unrecognized_returns_none() {
        assert!(recognize_ltac2_pattern(&s("(UnknownForm x y)")).is_none());
        assert!(recognize_ltac2_pattern(&Sexp::Atom("bare_atom".into())).is_none());
        assert!(recognize_ltac2_pattern(&s("()")).is_none());
    }

    #[test]
    fn test_ltac2_seq_operator() {
        // Note: bare ";" is a comment in sexp syntax, so Ltac2 serialization
        // uses "seq" or "Seq" as the head atom instead.
        let sexp = s("(seq step1 step2)");
        let pat = recognize_ltac2_pattern(&sexp).expect("should recognize seq");
        assert_eq!(pat, Ltac2Pattern::Seq { num_steps: 2 });
    }

    #[test]
    fn test_ltac2_plus_or() {
        let sexp = s("(+ a b c)");
        let pat = recognize_ltac2_pattern(&sexp).expect("should recognize + as Or");
        assert_eq!(
            pat,
            Ltac2Pattern::Or {
                num_alternatives: 3
            }
        );
    }
}
