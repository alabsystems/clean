// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Run the real checker on an instance and judge every accepted step semantically.
//!
//! Two judgements are made, both with the independent evaluator:
//!
//! * **Local**: for a step outside any context-introducing subproof, whose rule does not read
//!   an implicit subproof premise, the conjunction of its premise clauses must entail its
//!   conclusion clause.
//! * **Global**: every accepted top-level command must be entailed by the top-level hypotheses:
//!   the `assume`d premises, and the clauses of `hole`/`lia_generic` steps (and of subproofs that
//!   contain one), which are unverified by construction.
//!
//! A counterexample is a model in which every hypothesis evaluates to a *definite* `true` and the
//! judged clause to a *definite* `false`.

use crate::datatypes::DtTable;
use crate::eval::Evaluator;
use crate::model::{Model, Rng, Vocab};
use crate::sort::S;
use crate::value::{fmt_value, Env, V};
use carcara::ast::{pool::PrimitivePool, Constant, ProofCommand, ProofStep, Rc as TRc, Term};
use carcara::{checker, parser, Error};
use rug::Rational;
use std::collections::{BTreeMap, BTreeSet};
use std::panic::{catch_unwind, AssertUnwindSafe};
use std::rc::Rc;

/// Rules that read their implicit premise from the enclosing subproof.
pub const SUBPROOF_CLOSERS: &[&str] = &[
    "subproof",
    "bind",
    "let",
    "onepoint",
    "sko_ex",
    "sko_forall",
    "bind_let",
];

/// Rules whose steps are holes by definition.
pub const HOLE_RULES: &[&str] = &["hole", "lia_generic"];

#[derive(Debug, Clone)]
pub struct Instance {
    pub defs: String,
    pub proof: String,
}

#[derive(Debug, Clone)]
pub struct Cex {
    pub step: String,
    pub rule: String,
    pub global: bool,
    pub model: String,
}

#[derive(Debug, Clone, Default)]
pub struct Outcome {
    pub parse_error: Option<String>,
    pub panic: Option<String>,
    /// `(step id, rule)` of every accepted non-assume command, in proof order.
    pub accepted: Vec<(String, String)>,
    /// Accepted steps whose judgement found at least one model with all hypotheses true.
    pub exercised: BTreeSet<String>,
    pub first_error: Option<(String, String, String)>,
    pub cexs: Vec<Cex>,
}

/// The parser configuration instances are read under: upstream's default, or Clean's Alethe
/// dialect (`Config::clean_dialect()`, third-party/carcara/DOWNSTREAM.md § Dialect), which is what
/// `clean cert verify-external` parses with.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum Dialect {
    #[default]
    Upstream,
    Clean,
    /// Added in Clean: opt in to the separately versioned bounded spine rule.
    CleanBvOffsetSpinesV1,
    /// Explicit full-width reconstruction capability, independent of spine opt-in.
    CleanBvReconstructV1,
}

impl Dialect {
    pub fn name(self) -> &'static str {
        match self {
            Dialect::Upstream => "upstream",
            Dialect::Clean => "clean",
            Dialect::CleanBvOffsetSpinesV1 => "clean-bv-offset-spines-v1",
            Dialect::CleanBvReconstructV1 => "clean-bv-reconstruct-v1",
        }
    }

    pub fn from_name(name: &str) -> Option<Self> {
        match name {
            "upstream" => Some(Dialect::Upstream),
            "clean" => Some(Dialect::Clean),
            "clean-bv-offset-spines-v1" => Some(Dialect::CleanBvOffsetSpinesV1),
            "clean-bv-reconstruct-v1" => Some(Dialect::CleanBvReconstructV1),
            _ => None,
        }
    }

    /// The parser configuration, with problem `define-fun`s expanded as the battery always has.
    pub fn parser_config(self) -> parser::Config {
        let base = match self {
            Dialect::Upstream => parser::Config::new(),
            Dialect::Clean | Dialect::CleanBvOffsetSpinesV1 | Dialect::CleanBvReconstructV1 => {
                parser::Config::clean_dialect()
            }
        };
        base.apply_function_defs(true)
    }

    /// Added in Clean: select the rule dialect as explicitly as the parser.
    pub fn checker_config(self) -> checker::Config {
        match self {
            Dialect::Upstream => checker::Config::new(),
            Dialect::Clean => checker::Config::clean_dialect(),
            Dialect::CleanBvReconstructV1 => {
                checker::Config::clean_dialect().with_bv_reconstruct_v1()
            }
            Dialect::CleanBvOffsetSpinesV1 => {
                checker::Config::clean_dialect().with_bv_offset_spines_v1()
            }
        }
    }
}

#[derive(Clone)]
pub struct OracleConfig {
    pub random_models: usize,
    pub exhaustive_limit: usize,
    /// Total evaluation budget for one judgement, shared by all of its models.
    pub fuel: u64,
    pub seed: u64,
    pub dialect: Dialect,
}

const FUEL_PER_MODEL: u64 = 200_000;

impl Default for OracleConfig {
    fn default() -> Self {
        OracleConfig {
            random_models: 200,
            exhaustive_limit: 4096,
            fuel: 3_000_000,
            seed: 7,
            dialect: Dialect::Upstream,
        }
    }
}

struct Judgement {
    step: String,
    rule: String,
    global: bool,
    hyps: Vec<Vec<TRc<Term>>>,
    goal: Vec<TRc<Term>>,
}

/// Generators may leave the computed part of a conclusion open: a proof starting with
/// `; @@fill NAME` mentions the declared constant `NAME` where the checker's own expected term
/// belongs. The checker is run once to learn that term from its equality error, the term is
/// printed into the proof, and the completed instance is then checked and judged normally.
pub const FILL_MARKER: &str = "; @@fill ";

pub fn fill_instance(inst: &Instance, dialect: Dialect) -> Result<Instance, Outcome> {
    let name: String = inst.proof[FILL_MARKER.len()..]
        .split_whitespace()
        .next()
        .unwrap_or("")
        .to_owned();
    let parsed = catch_unwind(AssertUnwindSafe(|| {
        parser::parse_instance(&inst.defs, &inst.proof, None, dialect.parser_config())
    }));
    let (mut problem, proof, rules, mut pool) = match parsed {
        Ok(Ok(p)) => p,
        Ok(Err(e)) => {
            return Err(Outcome {
                parse_error: Some(first_line(&format!("{}", e))),
                ..Default::default()
            })
        }
        Err(p) => {
            return Err(Outcome {
                parse_error: Some(panic_text(&p)),
                ..Default::default()
            })
        }
    };
    set_premises(&inst.defs, &mut problem, &proof);
    let result = catch_unwind(AssertUnwindSafe(|| {
        checker::ProofChecker::new(&mut pool, &rules, dialect.checker_config())
            .check(&problem, &proof)
    }));
    use carcara::checker::error::{CheckerError, EqualityError};
    let is_hole = |t: &TRc<Term>| matches!(t.as_ref(), Term::Var(n, _) if *n == name);
    let expected = match result {
        Ok(Err(Error::Checker {
            inner: CheckerError::TermEquality(e),
            ..
        })) => match e {
            EqualityError::ExpectedEqual(a, b) if is_hole(&b) => Some(a),
            EqualityError::ExpectedEqual(a, b) if is_hole(&a) => Some(b),
            EqualityError::ExpectedToBe { expected, got } if is_hole(&got) => Some(expected),
            _ => None,
        },
        Err(p) => {
            return Err(Outcome {
                panic: Some(panic_text(&p)),
                ..Default::default()
            })
        }
        _ => None,
    };
    let Some(expected) = expected else {
        return Err(Outcome {
            first_error: Some((
                String::new(),
                String::new(),
                "fill: no expected term".into(),
            )),
            ..Default::default()
        });
    };
    // In full: `Display` abridges a large term, and this text goes into the proof.
    let printed = expected.unabridged().to_string();
    let body = inst.proof.splitn(2, '\n').nth(1).unwrap_or("");
    let filled = replace_symbol(body, &name, &printed);
    Ok(Instance {
        defs: inst.defs.clone(),
        proof: filled,
    })
}

fn replace_symbol(text: &str, name: &str, with: &str) -> String {
    let mut out = String::new();
    let chars: Vec<char> = text.chars().collect();
    let n: Vec<char> = name.chars().collect();
    let is_sym = |c: char| !c.is_whitespace() && !matches!(c, '(' | ')' | '"' | ';' | '|');
    let mut i = 0;
    while i < chars.len() {
        if chars[i..].starts_with(&n)
            && (i == 0 || !is_sym(chars[i - 1]))
            && (i + n.len() == chars.len() || !is_sym(chars[i + n.len()]))
        {
            out.push_str(with);
            i += n.len();
        } else {
            out.push(chars[i]);
            i += 1;
        }
    }
    out
}

/// Without explicit `(assert ...)` commands the `assume`d terms are the premises (as in
/// Carcara's own rule tests). With explicit asserts, those are the premises, and `assume`
/// steps are themselves judged against them.
fn set_premises(defs: &str, problem: &mut carcara::ast::Problem, proof: &carcara::ast::Proof) {
    if !defs.contains("(assert") {
        problem.premises = proof
            .commands
            .iter()
            .filter_map(|c| match c {
                ProofCommand::Assume { term, .. } => Some(term.clone()),
                _ => None,
            })
            .collect();
    }
}

/// Parse and check. Panics inside Carcara are caught and reported, never propagated.
pub fn check_instance(inst: &Instance, cfg: &OracleConfig) -> Outcome {
    if inst.proof.starts_with(FILL_MARKER) {
        return match fill_instance(inst, cfg.dialect) {
            Ok(filled) => check_instance(&filled, cfg),
            Err(o) => o,
        };
    }
    let mut out = Outcome::default();
    let parsed = catch_unwind(AssertUnwindSafe(|| {
        parser::parse_instance(&inst.defs, &inst.proof, None, cfg.dialect.parser_config())
    }));
    let (mut problem, proof, rules, mut pool) = match parsed {
        Ok(Ok(p)) => p,
        Ok(Err(e)) => {
            out.parse_error = Some(first_line(&format!("{}", e)));
            return out;
        }
        Err(p) => {
            out.parse_error = Some(format!("parser panic: {}", panic_text(&p)));
            return out;
        }
    };
    set_premises(&inst.defs, &mut problem, &proof);
    let explicit_asserts: Option<Vec<TRc<Term>>> = inst
        .defs
        .contains("(assert")
        .then(|| problem.premises.iter().cloned().collect());

    let result = catch_unwind(AssertUnwindSafe(|| {
        checker::ProofChecker::new(&mut pool, &rules, cfg.dialect.checker_config())
            .check(&problem, &proof)
    }));
    let failing_step = match result {
        Ok(Ok(_)) | Ok(Err(Error::DoesNotReachEmptyClause)) => None,
        Ok(Err(Error::Checker { inner, rule, step })) => {
            out.first_error = Some((
                step.to_string(),
                rule.to_string(),
                first_line(&inner.to_string()),
            ));
            Some(step.to_string())
        }
        Ok(Err(e)) => {
            out.first_error = Some((String::new(), String::new(), first_line(&format!("{}", e))));
            return out;
        }
        Err(p) => {
            out.panic = Some(panic_text(&p));
            return out;
        }
    };

    let judgements = collect_judgements(
        &proof.commands,
        failing_step.as_deref(),
        explicit_asserts.as_deref(),
        &mut out,
    );
    if judgements.is_empty() {
        return out;
    }
    let mut vocab = Vocab::default();
    for c in &proof.commands {
        collect_vocab_cmd(c, &mut vocab);
    }
    let vocab = Rc::new(vocab);
    let defs: Vec<(String, TRc<Term>)> = proof.constant_definitions.clone();
    let datatypes = Rc::new(datatype_table(&pool, &problem, &proof.commands, &defs));
    for j in &judgements {
        if let Some(cex) = judge(
            j,
            &defs,
            &vocab,
            &datatypes,
            &mut pool,
            cfg,
            &mut out.exercised,
        ) {
            out.cexs.push(cex);
        }
    }
    out
}

/// The datatypes of every term in the instance. A constructor or selector that an ordinary
/// `declare-fun`/`declare-const` redeclares with the same sort is read as uninterpreted (the
/// parser refuses such a script; this keeps the judgement independent of that refusal).
fn datatype_table(
    pool: &PrimitivePool,
    problem: &carcara::ast::Problem,
    commands: &[ProofCommand],
    defs: &[(String, TRc<Term>)],
) -> DtTable {
    fn terms<'a>(commands: &'a [ProofCommand], acc: &mut Vec<&'a TRc<Term>>) {
        for c in commands {
            match c {
                ProofCommand::Assume { term, .. } => acc.push(term),
                ProofCommand::Step(s) => acc.extend(s.clause.iter().chain(&s.args)),
                ProofCommand::Subproof(sp) => terms(&sp.commands, acc),
            }
        }
    }
    let mut all: Vec<&TRc<Term>> = problem.premises.iter().collect();
    terms(commands, &mut all);
    all.extend(defs.iter().map(|(_, body)| body));
    let mut table = DtTable::from_terms(pool, all);
    for (name, sort) in problem.prelude.function_declarations() {
        table.shadow(name, S::from_sort(sort));
    }
    table
}

fn first_line(s: &str) -> String {
    s.lines().next().unwrap_or("").chars().take(400).collect()
}

fn panic_text(p: &Box<dyn std::any::Any + Send>) -> String {
    if let Some(s) = p.downcast_ref::<&str>() {
        s.to_string()
    } else if let Some(s) = p.downcast_ref::<String>() {
        first_line(s)
    } else {
        "panic".to_owned()
    }
}

fn contains_hole(commands: &[ProofCommand]) -> bool {
    commands.iter().any(|c| match c {
        ProofCommand::Step(s) => HOLE_RULES.contains(&s.rule.as_str()),
        ProofCommand::Subproof(sp) => contains_hole(&sp.commands),
        ProofCommand::Assume { .. } => false,
    })
}

struct Walk<'a> {
    stack: Vec<&'a [ProofCommand]>,
    failing: Option<&'a str>,
    stopped: bool,
}

fn collect_judgements(
    commands: &[ProofCommand],
    failing: Option<&str>,
    asserts: Option<&[TRc<Term>]>,
    out: &mut Outcome,
) -> Vec<Judgement> {
    let mut judgements = Vec::new();
    let mut walk = Walk {
        stack: vec![commands],
        failing,
        stopped: false,
    };
    let mut global_hyps: Vec<Vec<TRc<Term>>> = Vec::new();
    if let Some(asserts) = asserts {
        for a in asserts {
            global_hyps.push(vec![a.clone()]);
        }
    }
    let mut global_goals: Vec<(String, String, Vec<TRc<Term>>)> = Vec::new();

    for (i, cmd) in commands.iter().enumerate() {
        if walk.stopped {
            break;
        }
        let _ = i;
        match cmd {
            ProofCommand::Assume { id, term } => {
                if walk.failing == Some(id.as_str()) {
                    break;
                }
                match asserts {
                    None => global_hyps.push(vec![term.clone()]),
                    Some(_) => {
                        out.accepted.push((id.clone(), "assume".into()));
                        global_goals.push((id.clone(), "assume".into(), vec![term.clone()]));
                    }
                }
            }
            ProofCommand::Step(step) => {
                if walk.failing == Some(step.id.as_str()) {
                    walk.stopped = true;
                    break;
                }
                out.accepted.push((step.id.clone(), step.rule.clone()));
                if HOLE_RULES.contains(&step.rule.as_str()) {
                    global_hyps.push(step.clause.clone());
                    continue;
                }
                if let Some(j) = local_judgement(step, &walk.stack) {
                    judgements.push(j);
                }
                global_goals.push((step.id.clone(), step.rule.clone(), step.clause.clone()));
            }
            ProofCommand::Subproof(sp) => {
                let completed = walk_subproof(
                    &sp.commands,
                    !sp.args.is_empty(),
                    &mut walk,
                    &mut judgements,
                    out,
                );
                if !completed {
                    break;
                }
                let last = sp.commands.last();
                let (id, rule, clause) = match last {
                    Some(ProofCommand::Step(s)) => (s.id.clone(), s.rule.clone(), s.clause.clone()),
                    _ => continue,
                };
                if contains_hole(&sp.commands) {
                    global_hyps.push(clause);
                } else {
                    global_goals.push((id, format!("{}", rule), clause));
                }
            }
        }
    }
    for (step, rule, goal) in global_goals {
        judgements.push(Judgement {
            step,
            rule,
            global: true,
            hyps: global_hyps.clone(),
            goal,
        });
    }
    judgements
}

/// Returns `false` if the failing step was reached inside the subproof.
fn walk_subproof<'a>(
    commands: &'a [ProofCommand],
    in_context: bool,
    walk: &mut Walk<'a>,
    judgements: &mut Vec<Judgement>,
    out: &mut Outcome,
) -> bool {
    walk.stack.push(commands);
    let n = commands.len();
    for (i, cmd) in commands.iter().enumerate() {
        match cmd {
            ProofCommand::Assume { .. } => {}
            ProofCommand::Step(step) => {
                if walk.failing == Some(step.id.as_str()) {
                    walk.stopped = true;
                    walk.stack.pop();
                    return false;
                }
                out.accepted.push((step.id.clone(), step.rule.clone()));
                let is_end = i + 1 == n;
                if !in_context
                    && !HOLE_RULES.contains(&step.rule.as_str())
                    && !(is_end && SUBPROOF_CLOSERS.contains(&step.rule.as_str()))
                {
                    if let Some(j) = local_judgement(step, &walk.stack) {
                        judgements.push(j);
                    }
                }
            }
            ProofCommand::Subproof(sp) => {
                let ctx = in_context || !sp.args.is_empty();
                if !walk_subproof(&sp.commands, ctx, walk, judgements, out) {
                    walk.stack.pop();
                    return false;
                }
            }
        }
    }
    walk.stack.pop();
    true
}

fn local_judgement(step: &ProofStep, stack: &[&[ProofCommand]]) -> Option<Judgement> {
    if SUBPROOF_CLOSERS.contains(&step.rule.as_str()) && stack.len() > 1 {
        return None;
    }
    let mut hyps = Vec::new();
    for &(depth, index) in &step.premises {
        let cmd = stack.get(depth)?.get(index)?;
        hyps.push(cmd.clause().to_vec());
    }
    Some(Judgement {
        step: step.id.clone(),
        rule: step.rule.clone(),
        global: false,
        hyps,
        goal: step.clause.clone(),
    })
}

fn collect_vocab_cmd(c: &ProofCommand, vocab: &mut Vocab) {
    match c {
        ProofCommand::Assume { term, .. } => collect_vocab(term, vocab, &mut BTreeSet::new()),
        ProofCommand::Step(s) => {
            let mut seen = BTreeSet::new();
            for t in s.clause.iter().chain(&s.args) {
                collect_vocab(t, vocab, &mut seen);
            }
        }
        ProofCommand::Subproof(sp) => {
            for c in &sp.commands {
                collect_vocab_cmd(c, vocab);
            }
        }
    }
}

fn collect_vocab(t: &TRc<Term>, vocab: &mut Vocab, seen: &mut BTreeSet<usize>) {
    if !seen.insert(TRc::as_ptr(t) as usize) || seen.len() > 20_000 {
        return;
    }
    match t.as_ref() {
        Term::Const(Constant::Integer(i)) => {
            vocab.ints.insert(i.clone());
        }
        Term::Const(Constant::Real(r)) => {
            vocab.reals.insert(r.clone());
        }
        Term::Const(Constant::String(s)) => {
            vocab.strings.insert(s.chars().map(|c| c as u32).collect());
        }
        Term::Const(_) | Term::Var(..) => {}
        Term::App(f, args) => {
            collect_vocab(f, vocab, seen);
            for a in args {
                collect_vocab(a, vocab, seen);
            }
        }
        Term::Op(_, args) | Term::AsOp(_, _, args) => {
            for a in args {
                collect_vocab(a, vocab, seen);
            }
        }
        Term::ParamOp { op_args, args, .. } => {
            for a in op_args.iter().chain(args) {
                collect_vocab(a, vocab, seen);
            }
        }
        Term::Binder(_, _, body) => collect_vocab(body, vocab, seen),
        Term::Let(bindings, body) => {
            for (_, v) in bindings.iter() {
                collect_vocab(v, vocab, seen);
            }
            collect_vocab(body, vocab, seen);
        }
        Term::Match(s, cases) => {
            collect_vocab(s, vocab, seen);
            for c in cases {
                collect_vocab(&c.body, vocab, seen);
            }
        }
    }
}

fn free_consts(
    t: &TRc<Term>,
    datatypes: &DtTable,
    bound: &mut Vec<(String, Option<S>)>,
    acc: &mut BTreeSet<(String, S)>,
    seen: &mut BTreeSet<usize>,
) {
    // Terms under binders cannot be cached by pointer alone.
    if bound.is_empty() && !seen.insert(TRc::as_ptr(t) as usize) {
        return;
    }
    match t.as_ref() {
        Term::Const(_) => {}
        Term::Var(name, sort) => {
            let s = S::from_sort(sort);
            let is_bound = bound
                .iter()
                .any(|(n, bs)| n == name && bs.as_ref().map_or(true, |b| *b == s));
            // A nullary constructor is a value, not a free constant.
            let is_datatype_symbol = !matches!(datatypes.symbol(name, &s), Ok(None));
            if !is_bound && !matches!(s, S::Fun(..)) && !is_datatype_symbol {
                acc.insert((name.clone(), s));
            }
        }
        Term::App(f, args) => {
            free_consts(f, datatypes, bound, acc, seen);
            for a in args {
                free_consts(a, datatypes, bound, acc, seen);
            }
        }
        Term::Op(_, args) | Term::AsOp(_, _, args) | Term::ParamOp { args, .. } => {
            for a in args {
                free_consts(a, datatypes, bound, acc, seen);
            }
        }
        Term::Binder(_, bindings, body) => {
            let n = bound.len();
            for (name, s) in bindings.iter() {
                bound.push((name.clone(), Some(S::from_sort(s))));
            }
            free_consts(body, datatypes, bound, acc, seen);
            bound.truncate(n);
        }
        Term::Let(bindings, body) => {
            for (_, v) in bindings.iter() {
                free_consts(v, datatypes, bound, acc, seen);
            }
            // A let-bound name shadows every same-named variable, whatever its sort.
            let n = bound.len();
            for (name, _) in bindings.iter() {
                bound.push((name.clone(), None));
            }
            free_consts(body, datatypes, bound, acc, seen);
            bound.truncate(n);
        }
        Term::Match(s, cases) => {
            free_consts(s, datatypes, bound, acc, seen);
            for c in cases {
                free_consts(&c.body, datatypes, bound, acc, seen);
            }
        }
    }
}

fn judge(
    j: &Judgement,
    defs: &[(String, TRc<Term>)],
    vocab: &Rc<Vocab>,
    datatypes: &Rc<DtTable>,
    pool: &mut PrimitivePool,
    cfg: &OracleConfig,
    exercised: &mut BTreeSet<String>,
) -> Option<Cex> {
    let mut consts = BTreeSet::new();
    let mut seen = BTreeSet::new();
    for t in j.hyps.iter().flatten().chain(&j.goal) {
        free_consts(t, datatypes, &mut Vec::new(), &mut consts, &mut seen);
    }
    let def_names: BTreeSet<&str> = defs.iter().map(|(n, _)| n.as_str()).collect();
    let consts: Vec<(String, S)> = consts
        .into_iter()
        .filter(|(n, _)| !def_names.contains(n.as_str()))
        .collect();

    // Exhaustive enumeration over finite free constants when affordable.
    let mut seed_rng = Rng::new(cfg.seed ^ hash_str(&j.step) ^ hash_str(&j.rule));
    let mut probe = Model::new(seed_rng.next_u64(), vocab.clone());
    probe.datatypes = datatypes.clone();
    let mut finite = true;
    let mut total: f64 = 1.0;
    let mut doms = Vec::new();
    for (_, s) in &consts {
        let (d, complete) = probe.domain(s);
        finite &= complete;
        total *= d.len().max(1) as f64;
        doms.push(d);
    }
    let mut assignments: Vec<Option<Vec<V>>> = Vec::new();
    if finite && total <= cfg.exhaustive_limit as f64 {
        for p in crate::model::product(&doms) {
            assignments.push(Some(p));
        }
        for _ in 0..16 {
            assignments.push(None);
        }
    } else {
        for _ in 0..cfg.random_models {
            assignments.push(None);
        }
    }

    let mut remaining = cfg.fuel;
    for assignment in assignments {
        if remaining == 0 {
            break;
        }
        let mut model = Model::new(seed_rng.next_u64(), vocab.clone());
        model.datatypes = datatypes.clone();
        if let Some(values) = &assignment {
            for ((n, s), v) in consts.iter().zip(values) {
                model.fixed.insert((n.clone(), s.clone()), v.clone());
            }
        }
        let budget = remaining.min(FUEL_PER_MODEL);
        let mut ev = Evaluator::new(&mut model, pool, budget);
        // Proof-local definitions are fixed before anything else is evaluated.
        let mut ok = true;
        for (name, body) in defs {
            let sort = ev.sort_of(body);
            match ev.eval(body, &Env::new()) {
                Ok(v) => {
                    ev.model.fixed.insert((name.clone(), sort), v);
                }
                Err(_) => ok = false,
            }
        }
        if !ok {
            remaining -= budget - ev.fuel_left();
            continue;
        }
        let mut hyps_true = true;
        for h in &j.hyps {
            if clause_value(&mut ev, h) != Some(true) {
                hyps_true = false;
                break;
            }
        }
        if !hyps_true {
            remaining -= budget - ev.fuel_left();
            continue;
        }
        let verdict = clause_value(&mut ev, &j.goal);
        remaining -= budget - ev.fuel_left();
        match verdict {
            Some(true) => {
                exercised.insert(j.step.clone());
            }
            Some(false) => {
                exercised.insert(j.step.clone());
                let mut desc = Vec::new();
                for (n, s) in &consts {
                    if let Some(v) = ev.model.const_value(n, s) {
                        desc.push(format!("{} = {}", n, fmt_value(&v)));
                    }
                }
                return Some(Cex {
                    step: j.step.clone(),
                    rule: j.rule.clone(),
                    global: j.global,
                    model: desc.join(", "),
                });
            }
            None => {}
        }
    }
    None
}

fn clause_value(ev: &mut Evaluator, clause: &[TRc<Term>]) -> Option<bool> {
    let mut unknown = false;
    for lit in clause {
        match ev.eval_bool(lit, &Env::new()) {
            Ok(true) => return Some(true),
            Ok(false) => {}
            Err(_) => unknown = true,
        }
    }
    if unknown {
        None
    } else {
        Some(false)
    }
}

fn hash_str(s: &str) -> u64 {
    let mut h: u64 = 0xcbf2_9ce4_8422_2325;
    for b in s.bytes() {
        h ^= b as u64;
        h = h.wrapping_mul(0x0000_0100_0000_01B3);
    }
    h
}

#[allow(dead_code)]
fn _silence(_: BTreeMap<u8, u8>, _: Rational) {}
