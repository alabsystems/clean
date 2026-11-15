// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
//! Cache-free experimental core. No ordinary checker calls this evaluator.
//! Labelled syntax and every diagnostic remain outside the trusted entry.
use super::term::{Label, Node, Term};
use super::{DomainClass, Journal, Token};
use crate::env::Environment;
use crate::expr::{stack_safe, Expr, ExprKind};
use crate::level::Level;
use crate::name::Name;
use std::collections::{BTreeMap, HashSet};

/// A tracing refusal is separate from the reference kernel's verdict.
#[derive(Clone, Debug, thiserror::Error)]
pub enum Refusal {
    /// An unsupported source must remain visible in a corpus report.
    #[error("unimplemented tracing construction {source_name}: {term}")]
    Coverage { source_name: String, term: String },
    /// A local type or conversion check failed.
    #[error("tracing check failed: {0}")]
    Check(String),
    /// The experiment ran out of its own operation budget.
    #[error("tracing operation budget exhausted")]
    Budget,
}

/// Call-chain and inference-volume measurements for design Revision 1.
#[derive(Clone, Debug, Default, serde::Serialize)]
pub struct Volume {
    /// Actual producer call depth, including consecutive head continuations.
    pub max_call_depth: u64,
    /// Depth after collapsing head continuations and telescope walk frames.
    pub max_non_head_depth: u64,
    /// Longest consecutive sequence of head steps.
    pub longest_head_run: u64,
    /// Largest actual labelled term, excluding diagnostic universe provenance.
    pub largest_term_height: u32,
    /// Node visits split into the declaration's input and derived inference.
    pub inference_nodes: BTreeMap<String, u64>,
    /// Producer-computed generous counter; not a fixed completeness limit.
    pub depth_bound: u64,
}
#[derive(Clone, Copy, PartialEq, Eq)]
enum FrameKind {
    Check,
    Infer,
    Whnf,
    Conv,
    Walk,
}
struct Frame {
    kind: FrameKind,
    effective: u64,
    head_run: u64,
}

/// One argument-position comparison in a recursor or constructor telescope.
#[derive(Clone, Debug, serde::Serialize)]
pub struct SpineComparison {
    /// Iota/K/structure-eta/literal entry path.
    pub entry: String,
    /// Inductive family.
    pub family: String,
    /// Recursor or constructor walk.
    pub target: String,
    /// Parameter, motive, minor, index, major, or constructor field.
    pub position_kind: String,
    /// Zero-based position in the entire telescope.
    pub position: usize,
    /// The recorded domain result.
    pub class: DomainClass,
    /// Successful-path conversion certificate length.
    pub conversion_tokens: u64,
    /// Actual head reductions performed while comparing the pair.
    pub conversion_head_steps: u64,
}

/// Actual existing-kernel work for one independently checked comparison.
/// Heartbeats count kernel operations, including structural work, rather than
/// only contracted beta/delta/iota steps. The checker and profiler are fresh.
#[derive(Clone, Debug, serde::Serialize)]
pub struct OracleConversion {
    /// Label guard or diagnostic fallback which requested this comparison.
    pub source: String,
    /// The kernel's conversion result (undecided when budget_exhausted).
    pub equal: bool,
    /// Whether the kernel ran out of its own heartbeat budget.
    pub budget_exhausted: bool,
    /// Total actual kernel operation heartbeats.
    pub heartbeats: u64,
    /// Breakdown from the kernel's existing profiler.
    pub categories: BTreeMap<String, u64>,
}

/// A refused domain pair with its construction and local redex.
#[derive(Clone, Debug, serde::Serialize)]
pub struct DomainProblem {
    /// Construction or reducer which exposed the pair.
    pub source: String,
    /// Exact diagnostic erasure of the redex.
    pub term: String,
    /// Exact erasure of the stored label, when present.
    pub label: Option<String>,
    /// Exact erasure of the expected binder/telescope domain.
    pub domain: String,
    /// Conversion refusal or missing-source name.
    pub class: DomainClass,
}
/// Persistent annotated syntax of earlier admitted declarations. This stores
/// terms, not cached conversion/inference answers. Every new declaration still
/// starts with an empty journal and no equation cache.
#[derive(Default)]
pub struct LabelledEnvironment {
    entries: BTreeMap<Name, (Term, Option<Term>)>,
    rules: BTreeMap<(Name, Name), Term>,
}
impl LabelledEnvironment {
    /// Install syntax only after both tracing and ordinary admission succeeded.
    pub fn insert(&mut self, name: Name, annotation: (Term, Option<Term>)) {
        self.entries.insert(name, annotation);
    }
    /// Extend with a completely traced block after ordinary admission.
    pub fn extend(&mut self, other: Self) {
        self.entries.extend(other.entries);
        self.rules.extend(other.rules);
    }
    /// Install a checked, generic recursor RHS, before universe instantiation.
    pub fn insert_rule(&mut self, recursor: Name, constructor: Name, rhs: Term) {
        self.rules.insert((recursor, constructor), rhs);
    }
}

/// One declaration's independent, untrusted producer. No union-find, sharing
/// between recursor arms, inference shortcut, or conversion cache is present.
/// The constant store contains annotated syntax, NOT inference/equation answers.
pub struct CoreTracer<'a> {
    env: &'a Environment,
    labelled: Option<&'a LabelledEnvironment>,
    constants: BTreeMap<Name, (Term, Option<Term>)>,
    context: Vec<Term>,
    context_values: Vec<Option<Term>>,
    remaining: u64,
    /// Successful-path journal; scoped by this object's lifetime.
    pub journal: Journal,
    /// Every beta observation, including failed speculative paths. These are
    /// diagnostic events, not tokens, so rollback deliberately does not hide them.
    pub beta_classes: Vec<DomainClass>,
    /// Actual conversion head reductions for each completed beta comparison.
    pub beta_conversion_head_steps: Vec<u64>,
    /// All exposed failed or absent label pairs, with their exact local terms.
    pub domain_problems: Vec<DomainProblem>,
    /// Applications whose existing labels inferAnn had to compare.
    pub infer_ann_comparisons: u64,
    /// Earlier entries which had to be reannotated because their trace was not
    /// available. These are explicit corpus-coverage holes, not advice savings.
    pub reannotated_dependencies: std::collections::BTreeSet<String>,
    /// Major-premise domain observations for iota, by recursor name.
    pub iota_classes: Vec<(String, DomainClass)>,
    /// Major-premise domain observations for K conversion, by recursor name.
    pub k_classes: Vec<(String, DomainClass)>,
    /// Comparisons performed by inferAnn, attributed to its caller.
    pub infer_ann_by_source: BTreeMap<String, u64>,
    /// Domain classes for inferAnn, attributed to its caller.
    pub infer_ann_classes: Vec<(String, DomainClass)>,
    infer_ann_source: &'static str,
    group_names: std::collections::BTreeSet<Name>,
    frames: Vec<Frame>,
    raw_phase: &'static str,
    /// Call-chain and node-visit census.
    pub volume: Volume,
    /// Telescope comparisons; every failed/missing source remains named.
    pub spine_comparisons: Vec<SpineComparison>,
    /// Reductions whose application nodes were built with another head.
    pub recursor_spines_other_head: u64,
    /// Minor-premise beta labels, split as the design addendum requests.
    pub minor_beta: BTreeMap<String, u64>,
    /// Literal expansion attempts declined by canonical-definition admission.
    pub literal_admission_skips: BTreeMap<String, u64>,
    /// Canonically admitted literal expansions, including conversion-only uses.
    pub literal_expansions: BTreeMap<String, u64>,
    /// Constructor/recursor universe-argument comparisons at iota.
    pub constructor_levels: BTreeMap<String, u64>,
    /// Actual head-step work, including failed speculative conversions.
    pub attempted_head_steps: u64,
    /// Fresh existing-kernel conversion profiles, independent of producer tokens.
    pub oracle_conversions: Vec<OracleConversion>,
    active_conversions: HashSet<(Term, Term)>,
    /// Cyclic producer search branches cut without reusing any equality answer.
    pub conversion_cycles_cut: u64,
    retain_nat_function_head: bool,
    /// Admitted primitive Nat folds, outside the core design Term.
    pub native_nat_steps: BTreeMap<String, u64>,
    /// Primitive applications the existing kernel deliberately leaves stuck.
    pub native_nat_stops: BTreeMap<String, u64>,
}

impl<'a> CoreTracer<'a> {
    /// Start a fresh declaration. An explicit operation budget makes a partial
    /// measurement a refusal rather than a silently truncated successful row.
    pub fn new(env: &'a Environment, operations: u64) -> Self {
        let mut journal = Journal::default();
        journal.push(Token::Depth(0));
        Self {
            env,
            labelled: None,
            constants: BTreeMap::new(),
            context: vec![],
            context_values: vec![],
            remaining: operations,
            journal,
            beta_classes: vec![],
            beta_conversion_head_steps: vec![],
            domain_problems: vec![],
            infer_ann_comparisons: 0,
            reannotated_dependencies: Default::default(),
            iota_classes: vec![],
            k_classes: vec![],
            infer_ann_by_source: BTreeMap::new(),
            infer_ann_classes: vec![],
            infer_ann_source: "CHECK",
            group_names: Default::default(),
            frames: vec![],
            raw_phase: "generated",
            volume: Default::default(),
            spine_comparisons: vec![],
            recursor_spines_other_head: 0,
            minor_beta: BTreeMap::new(),
            attempted_head_steps: 0,
            oracle_conversions: vec![],
            active_conversions: HashSet::new(),
            conversion_cycles_cut: 0,
            retain_nat_function_head: false,
            native_nat_steps: BTreeMap::new(),
            native_nat_stops: BTreeMap::new(),
            constructor_levels: BTreeMap::new(),
            literal_expansions: BTreeMap::new(),
            literal_admission_skips: BTreeMap::new(),
        }
    }
    /// Start a declaration with the labelled syntax of the already admitted
    /// prefix. No unchecked inference or cross-declaration equation is reused.
    pub fn with_labelled_environment(
        env: &'a Environment,
        labelled: &'a LabelledEnvironment,
        operations: u64,
    ) -> Self {
        let mut tracer = Self::new(env, operations);
        tracer.labelled = Some(labelled);
        tracer
    }
    /// Annotate one newly admitted inductive/primitive block. Signature members
    /// may refer to the other members of the SAME block; they are not treated
    /// as missing earlier declarations. All caches still die with this block.
    pub fn annotate_group(&mut self, names: &[Name]) -> Result<LabelledEnvironment, Refusal> {
        self.group_names.extend(names.iter().cloned());
        let mut result = LabelledEnvironment::default();
        for name in names {
            let info = self
                .env
                .get_const(name)
                .cloned()
                .ok_or_else(|| Refusal::Check(format!("missing group member {name}")))?;
            let ty = self.constant_type(name)?;
            let existing = self.constants.get(name).and_then(|(_, v)| v.clone());
            let value = if let Some(value) = existing {
                Some(value)
            } else if let Some(raw) = info.value {
                let (value, inferred) = self.check(&raw)?;
                if !self.conv(&inferred, &ty)? {
                    return Err(Refusal::Check(format!("group member value type {name}")));
                }
                Some(value)
            } else {
                None
            };
            self.constants
                .insert(name.clone(), (ty.clone(), value.clone()));
            result.entries.insert(name.clone(), (ty, value));
        }
        let recursors: Vec<_> = self
            .env
            .recursors()
            .filter(|r| self.group_names.contains(&r.name))
            .cloned()
            .collect();
        for rec in recursors {
            for rule in &rec.rules {
                if !matches!(rule.rhs.kind(), ExprKind::Lam(..)) {
                    if rec.is_k && rule.num_fields == 0 {
                        continue;
                    }
                    return Err(self.hole("legacy_recursor_rhs", &rule.rhs));
                }
                let (rhs, _) = self.check(&rule.rhs)?;
                let rhs = rhs.mark_minor_heads(
                    &rec.name,
                    rec.num_params + rec.num_motives,
                    rec.num_minors,
                );
                result
                    .rules
                    .insert((rec.name.clone(), rule.constructor_name.clone()), rhs);
            }
        }
        Ok(result)
    }
    /// Trace a whole ordinary declaration without admitting it or granting any
    /// authority. A separate reference entry must decide the ordinary verdict.
    pub fn declaration(&mut self, declaration: &crate::env::Declaration) -> Result<(), Refusal> {
        self.declaration_labelled(declaration).map(|_| ())
    }
    /// Check an ordinary input and retain its annotated type and body for the
    /// next declaration's environment. The caller must gate insertion on the
    /// independent reference entry's acceptance too.
    pub fn declaration_labelled(
        &mut self,
        declaration: &crate::env::Declaration,
    ) -> Result<(Term, Option<Term>), Refusal> {
        use crate::env::Declaration;
        let (ty, value) = match declaration {
            Declaration::Definition { type_, value, .. }
            | Declaration::Theorem { type_, value, .. }
            | Declaration::Opaque { type_, value, .. } => (type_, Some(value)),
            Declaration::Axiom { type_, .. } => (type_, None),
        };
        let (ty, ty_type) = self.check_as(ty, "input_type")?;
        let sort = self.whnf(&ty_type)?;
        if !matches!(sort.0.as_ref(), Node::Sort(_)) {
            return Err(Refusal::Check("declaration type is not a type".into()));
        }
        let value = if let Some(value) = value {
            let (value, inferred) = self.check_as(value, "input_body")?;
            if !self.conv(&inferred, &ty)? {
                return Err(Refusal::Check("declaration value type".into()));
            }
            Some(value)
        } else {
            None
        };
        Ok((ty, value))
    }
    fn enter(&mut self, kind: FrameKind, continuation: bool) {
        let tail = continuation
            && self
                .frames
                .last()
                .is_some_and(|f| f.kind == FrameKind::Whnf);
        let effective = self.frames.last().map_or(1, |f| {
            f.effective + u64::from(!tail && kind != FrameKind::Walk)
        });
        let head_run = if tail {
            self.frames.last().map_or(1, |f| f.head_run + 1)
        } else {
            0
        };
        self.frames.push(Frame {
            kind,
            effective,
            head_run,
        });
        self.volume.max_call_depth = self.volume.max_call_depth.max(self.frames.len() as u64);
        self.volume.max_non_head_depth = self.volume.max_non_head_depth.max(effective);
        self.volume.longest_head_run = self.volume.longest_head_run.max(head_run);
    }
    fn visit(&mut self, kind: String) {
        *self.volume.inference_nodes.entry(kind).or_default() += 1;
    }
    fn built(&mut self, t: &Term) {
        self.volume.largest_term_height = self.volume.largest_term_height.max(t.height());
    }
    fn check_as(&mut self, raw: &Expr, phase: &'static str) -> Result<(Term, Term), Refusal> {
        let previous = self.raw_phase;
        self.raw_phase = phase;
        let result = self.check(raw);
        self.raw_phase = previous;
        result
    }
    /// Finalise the declaration-supplied depth counter from measured work/height.
    pub fn finish_journal(&mut self) {
        let n = self.journal.tokens.len() as u64;
        self.volume.depth_bound = (n + 1)
            .saturating_mul(u64::from(self.volume.largest_term_height) + 1)
            .max(self.volume.max_call_depth + 1);
        if let Some(header) = self.journal.tokens.first_mut() {
            *header = Token::Depth(self.volume.depth_bound);
        }
    }
    fn tick(&mut self) -> Result<(), Refusal> {
        self.remaining = self.remaining.checked_sub(1).ok_or(Refusal::Budget)?;
        Ok(())
    }
    fn hole(&self, source: &str, e: &Expr) -> Refusal {
        Refusal::Coverage {
            source_name: source.into(),
            term: format!("{e}").chars().take(512).collect(),
        }
    }
    /// Elaborate a raw core term and its type, writing an application's domain
    /// only after the argument's inferred type actually converts to that domain.
    pub fn check(&mut self, raw: &Expr) -> Result<(Term, Term), Refusal> {
        self.enter(FrameKind::Check, false);
        self.visit(self.raw_phase.to_string());
        let result = stack_safe(|| self.check_inner(raw));
        if let Ok((term, ty)) = &result {
            self.built(term);
            self.built(ty);
        }
        self.frames.pop();
        result
    }
    fn check_inner(&mut self, raw: &Expr) -> Result<(Term, Term), Refusal> {
        self.tick()?;
        match raw.kind() {
            ExprKind::Sort(l) => Ok((
                Term::new(Node::Sort(l.clone())),
                Term::new(Node::Sort(Level::succ(l.clone()))),
            )),
            ExprKind::Const(n, ls) => {
                let ty = self.constant_type(n)?;
                let Some(info) = self.env.get_const(n) else {
                    return Err(Refusal::Check(format!("unknown {n}")));
                };
                if info.level_params.len() != ls.len() {
                    return Err(Refusal::Check(format!("level arity for {n}")));
                }
                Ok((
                    Term::new(Node::Const(n.clone(), ls.to_vec())),
                    ty.instantiate_levels(&info.level_params, ls),
                ))
            }
            ExprKind::FVar(id) => {
                let index = usize::try_from(id.0).map_err(|_| self.hole("external_fvar", raw))?;
                let ty = self
                    .context
                    .get(index)
                    .cloned()
                    .ok_or_else(|| self.hole("external_fvar", raw))?;
                let level = u32::try_from(index).map_err(|_| Refusal::Budget)?;
                Ok((Term::new(Node::Local(level)), ty))
            }
            ExprKind::BVar(_) => Err(self.hole("loose_bvar", raw)),
            ExprKind::App(f, a) => {
                let (f, ty) = self.check(f)?;
                let pi = self.whnf(&ty)?;
                let Node::Pi(_, d, b) = pi.0.as_ref() else {
                    return Err(Refusal::Check("function type is not Pi".into()));
                };
                let (a, aty) = self.check(a)?;
                if !self.conv(&aty, d)? {
                    return Err(Refusal::Check("application argument type".into()));
                }
                let result = b.instantiate(&a);
                Ok((
                    Term::new(Node::App(f, a, Label::Checked(d.clone()))),
                    result,
                ))
            }
            ExprKind::Lam(b, d, t) | ExprKind::Pi(b, d, t) => {
                let (domain, dty) = self.check(d)?;
                let dsort = self.whnf(&dty)?;
                let Node::Sort(u) = dsort.0.as_ref() else {
                    return Err(Refusal::Check("binder domain is not a type".into()));
                };
                let index = u32::try_from(self.context.len()).map_err(|_| Refusal::Budget)?;
                self.context.push(domain.clone());
                self.context_values.push(None);
                // Kernel FVar ids used only as an input-opening adapter; stored
                // terms use context levels and never store raw FVars.
                let opened = t.instantiate(&Expr::fvar(crate::expr::FVarId(u64::from(index))));
                let result = self.check(&opened);
                self.context.pop();
                self.context_values.pop();
                let (body, bty) = result?;
                let body = body.abstract_local(index);
                let bty = bty.abstract_local(index);
                if matches!(raw.kind(), ExprKind::Lam(..)) {
                    Ok((
                        Term::new(Node::Lam(*b, domain.clone(), body)),
                        Term::new(Node::Pi(*b, domain, bty)),
                    ))
                } else {
                    let bsort = self.whnf(&bty)?;
                    let Node::Sort(v) = bsort.0.as_ref() else {
                        return Err(Refusal::Check("Pi codomain is not a type".into()));
                    };
                    Ok((
                        Term::new(Node::Pi(*b, domain, body)),
                        Term::new(Node::Sort(Level::imax(u.clone(), v.clone()))),
                    ))
                }
            }
            ExprKind::Let(n, d, v, b, _) => {
                let (d, dty) = self.check(d)?;
                let sort = self.whnf(&dty)?;
                if !matches!(sort.0.as_ref(), Node::Sort(_)) {
                    return Err(Refusal::Check("let annotation is not a type".into()));
                }
                let (v, vty) = self.check(v)?;
                if !self.conv(&vty, &d)? {
                    return Err(Refusal::Check("let value type".into()));
                }
                let index = u32::try_from(self.context.len()).map_err(|_| Refusal::Budget)?;
                self.context.push(d.clone());
                self.context_values.push(Some(v.clone()));
                let opened = b.instantiate(&Expr::fvar(crate::expr::FVarId(u64::from(index))));
                let result = self.check(&opened);
                self.context.pop();
                self.context_values.pop();
                let (body, ty) = result?;
                let body = body.abstract_local(index);
                let ty = ty.abstract_local(index).instantiate(&v);
                Ok((Term::new(Node::Let(n.clone(), d, v, body)), ty))
            }
            ExprKind::MData(_, e) => self.check(e),
            ExprKind::Lit(lit) => {
                let name = match lit {
                    crate::expr::Literal::Nat(_) => "Nat",
                    crate::expr::Literal::String(_) => "String",
                };
                if self.env.get_const(&Name::from_string(name)).is_none() {
                    return Err(self.hole("literal_type_absent", raw));
                }
                Ok((
                    Term::new(Node::Lit(lit.clone())),
                    Term::new(Node::Const(Name::from_string(name), vec![])),
                ))
            }
            ExprKind::Proj(n, i, e) => {
                let (e, _) = self.check(e)?;
                let ty = self.projection_type(n, *i, &e)?;
                Ok((Term::new(Node::Proj(n.clone(), *i, e)), ty))
            }
            _ => Err(self.hole("non_core_expression", raw)),
        }
    }
    fn constant_type(&mut self, n: &Name) -> Result<Term, Refusal> {
        if let Some(labelled) = self.labelled {
            if let Some((ty, _)) = labelled.entries.get(n) {
                return Ok(ty.clone());
            }
            if !self.group_names.contains(n) {
                self.reannotated_dependencies.insert(n.to_string());
            }
        }
        if let Some((ty, _)) = self.constants.get(n) {
            return Ok(ty.clone());
        }
        let raw = self
            .env
            .get_const(n)
            .map(|info| info.type_.clone())
            .ok_or_else(|| Refusal::Check(format!("unknown {n}")))?;
        // Constants are closed: never annotate an environment entry in a
        // caller's local context, where raw input FVar ids could be captured.
        let context = std::mem::take(&mut self.context);
        let values = std::mem::take(&mut self.context_values);
        let result = self.check_as(
            &raw,
            if self.group_names.contains(n) {
                "input_type"
            } else {
                "environment"
            },
        );
        self.context = context;
        self.context_values = values;
        let (ty, _) = result?;
        self.constants.insert(n.clone(), (ty.clone(), None));
        Ok(ty)
    }
    fn constant_value(&mut self, n: &Name, ls: &[Level]) -> Result<Option<Term>, Refusal> {
        let Some(info) = self.env.get_const(n).cloned() else {
            return Err(Refusal::Check(format!("unknown {n}")));
        };
        let Some(raw) = info.value else {
            return Ok(None);
        };
        if !matches!(info.kind, crate::env::ConstantKind::Definition) {
            return Ok(None);
        }
        if let Some(labelled) = self.labelled {
            if let Some((_, Some(body))) = labelled.entries.get(n) {
                return Ok(Some(body.instantiate_levels(&info.level_params, ls)));
            }
        }
        self.constant_type(n)?;
        let prior = self.constants.get(n).and_then(|(_, v)| v.clone());
        let body = if let Some(v) = prior {
            v
        } else {
            let context = std::mem::take(&mut self.context);
            let values = std::mem::take(&mut self.context_values);
            let result = self.check(&raw);
            self.context = context;
            self.context_values = values;
            let (v, ty) = result?;
            let declared = self.constant_type(n)?;
            // This check is separate from the kernel's own admission verdict.
            if !self.conv(&ty, &declared)? {
                return Err(Refusal::Check(format!("body type of {n}")));
            }
            if let Some(entry) = self.constants.get_mut(n) {
                entry.1 = Some(v.clone());
            }
            v
        };
        Ok(Some(body.instantiate_levels(&info.level_params, ls)))
    }
    /// Core WHNF, preserving labels during every step it implements. Unsupported
    /// recursor reductions refuse by source, never fall back to an erased term.
    pub fn whnf(&mut self, t: &Term) -> Result<Term, Refusal> {
        self.whnf_entry(t, false)
    }
    fn whnf_continue(&mut self, t: &Term) -> Result<Term, Refusal> {
        self.attempted_head_steps += 1;
        self.whnf_entry(t, true)
    }
    fn whnf_entry(&mut self, t: &Term, continuation: bool) -> Result<Term, Refusal> {
        self.enter(FrameKind::Whnf, continuation);
        self.built(t);
        let result = stack_safe(|| self.whnf_inner(t));
        if let Ok(term) = &result {
            self.built(term);
        }
        self.frames.pop();
        result
    }
    fn whnf_inner(&mut self, t: &Term) -> Result<Term, Refusal> {
        self.tick()?;
        match t.0.as_ref() {
            Node::App(f, a, label) => {
                if let Some((value, reduced)) = self.native_nat(t)? {
                    if reduced {
                        return self.whnf_continue(&value);
                    }
                    self.journal.push(Token::Stop);
                    return Ok(value);
                }
                let previous = self.retain_nat_function_head;
                self.retain_nat_function_head = true;
                let head_result = self.whnf(f);
                self.retain_nat_function_head = previous;
                let head = head_result?;
                if let Node::Lam(_, domain, body) = head.0.as_ref() {
                    let Label::Checked(d) = label else {
                        if let Label::Missing(source) = label {
                            let class = DomainClass::Missing(source.clone());
                            self.beta_classes.push(class.clone());
                            self.domain_problems.push(DomainProblem {
                                source: source.clone(),
                                term: t.erase().to_string(),
                                label: None,
                                domain: domain.erase().to_string(),
                                class,
                            });
                        }
                        return Err(Refusal::Check("missing application label".into()));
                    };
                    let head_start = self.attempted_head_steps;
                    let mark = self.journal.tokens.len();
                    self.journal.push(Token::Dom);
                    let class = if d.erased_eq(domain) {
                        self.journal.push(Token::Refl);
                        if d.before_levels() == domain.before_levels() {
                            DomainClass::Identical
                        } else {
                            DomainClass::LevelInstantiated
                        }
                    } else {
                        let start = self.journal.tokens.len();
                        match self.guard_conversion(d, domain, "beta") {
                            Ok(true) => DomainClass::Convertible {
                                steps: (self.journal.tokens.len() - start) as u64,
                            },
                            Ok(false) => {
                                self.journal.tokens.truncate(mark);
                                let class = DomainClass::Failed("DOM conversion".into());
                                self.beta_classes.push(class.clone());
                                self.domain_problems.push(DomainProblem {
                                    source: "beta".into(),
                                    term: t.erase().to_string(),
                                    label: Some(d.erase().to_string()),
                                    domain: domain.erase().to_string(),
                                    class,
                                });
                                return Err(Refusal::Check("DOM conversion".into()));
                            }
                            Err(e) => {
                                self.journal.tokens.truncate(mark);
                                return Err(e);
                            }
                        }
                    };
                    self.beta_classes.push(class);
                    self.beta_conversion_head_steps
                        .push(self.attempted_head_steps - head_start);
                    self.journal.push(Token::CoreL(1));
                    if t.minor_origin().is_some() {
                        let category = if d.erased_eq(domain) {
                            "identical"
                        } else if self.head_beta_label(d)? == domain.erase() {
                            "head_beta_label"
                        } else {
                            "other"
                        };
                        *self.minor_beta.entry(category.into()).or_default() += 1;
                    }
                    self.whnf_continue(&body.instantiate(a))
                } else {
                    let rebuilt =
                        Term::new(Node::App(head, a.clone(), label.clone())).with_origin_of(t);
                    if !rebuilt.erased_eq(t) {
                        if let Some((value, reduced)) = self.native_nat(&rebuilt)? {
                            if reduced {
                                return self.whnf_continue(&value);
                            }
                            self.journal.push(Token::Stop);
                            return Ok(value);
                        }
                    }
                    if let Some(value) = self.unfold_nat_application(&rebuilt)? {
                        return self.whnf_continue(&value);
                    }
                    if let Some(reduced) = self.quotient(&rebuilt)? {
                        return self.whnf_continue(&reduced);
                    }
                    if let Some(reduced) = self.iota(&rebuilt)? {
                        return self.whnf_continue(&reduced);
                    }
                    self.journal.push(Token::Stop);
                    Ok(rebuilt)
                }
            }
            Node::Proj(n, i, e) => {
                let value = self.whnf(e)?;
                let (head, args) = Self::spine(&value);
                if let Node::Const(ctor, _) = head.0.as_ref() {
                    if let Some(info) = self.env.get_constructor(ctor) {
                        if info.inductive_name == *n {
                            if let Some((field, _)) =
                                args.get(info.num_params as usize + *i as usize)
                            {
                                self.journal.push(Token::CoreL(1));
                                return self.whnf(field);
                            }
                        }
                    }
                }
                self.journal.push(Token::Stop);
                Ok(Term::new(Node::Proj(n.clone(), *i, value)))
            }
            Node::Local(i) => {
                if let Some(Some(value)) = self.context_values.get(*i as usize).cloned() {
                    self.journal.push(Token::CoreL(1));
                    self.whnf_continue(&value)
                } else {
                    self.journal.push(Token::Stop);
                    Ok(t.clone())
                }
            }
            Node::Let(_, _, v, b) => {
                self.journal.push(Token::CoreL(1));
                self.whnf_continue(&b.instantiate(v))
            }
            Node::Const(n, ls) => {
                if self.retain_nat_function_head && self.native_nat_name(t).is_some() {
                    self.journal.push(Token::Stop);
                    return Ok(t.clone());
                }
                if let Some(body) = self.constant_value(n, ls)? {
                    self.journal.push(Token::DeltaL);
                    self.whnf_continue(&body)
                } else {
                    self.journal.push(Token::Stop);
                    Ok(t.clone())
                }
            }
            _ => {
                self.journal.push(Token::Stop);
                Ok(t.clone())
            }
        }
    }
    /// Infer from labels, without re-checking application arguments. This is
    /// deliberately separate from raw-term checking above.
    pub fn infer_ann(&mut self, t: &Term) -> Result<Term, Refusal> {
        self.enter(FrameKind::Infer, false);
        self.visit(format!("derived/{}", self.infer_ann_source));
        self.built(t);
        let result = stack_safe(|| self.infer_ann_inner(t));
        if let Ok(ty) = &result {
            self.built(ty);
        }
        self.frames.pop();
        result
    }
    fn infer_ann_inner(&mut self, t: &Term) -> Result<Term, Refusal> {
        self.tick()?;
        match t.0.as_ref() {
            Node::Local(i) => self
                .context
                .get(*i as usize)
                .cloned()
                .ok_or_else(|| Refusal::Check("unknown local".into())),
            Node::Sort(l) => Ok(Term::new(Node::Sort(Level::succ(l.clone())))),
            Node::Const(n, ls) => {
                let ty = self.constant_type(n)?;
                let Some(info) = self.env.get_const(n) else {
                    return Err(Refusal::Check(format!("unknown {n}")));
                };
                Ok(ty.instantiate_levels(&info.level_params, ls))
            }
            Node::App(f, a, label) => {
                let ty = self.infer_ann(f)?;
                let pi = self.whnf(&ty)?;
                let Node::Pi(_, d, b) = pi.0.as_ref() else {
                    return Err(Refusal::Check("inferAnn function not Pi".into()));
                };
                self.infer_ann_comparisons += 1;
                *self
                    .infer_ann_by_source
                    .entry(self.infer_ann_source.to_string())
                    .or_default() += 1;
                let source = format!("inferAnn/{}", self.infer_ann_source);
                let class = self.classify_domain(label, d, &source)?;
                self.infer_ann_classes
                    .push((self.infer_ann_source.to_string(), class.clone()));
                if matches!(
                    class,
                    DomainClass::Identical | DomainClass::LevelInstantiated
                ) {
                    self.journal.push(Token::Refl);
                }
                if matches!(class, DomainClass::Failed(_) | DomainClass::Missing(_)) {
                    self.domain_problems.push(DomainProblem {
                        source: format!("inferAnn/{}", self.infer_ann_source),
                        term: t.erase().to_string(),
                        label: match label {
                            Label::Checked(label) => Some(label.erase().to_string()),
                            Label::Missing(_) => None,
                        },
                        domain: d.erase().to_string(),
                        class,
                    });
                    return Err(Refusal::Check("inferAnn domain".into()));
                }
                Ok(b.instantiate(a))
            }
            Node::Lam(b, d, body) | Node::Pi(b, d, body) => {
                let dty = self.infer_ann(d)?;
                let dsort = self.whnf(&dty)?;
                let Node::Sort(u) = dsort.0.as_ref() else {
                    return Err(Refusal::Check(
                        "inferAnn binder domain is not a type".into(),
                    ));
                };
                let i = u32::try_from(self.context.len()).map_err(|_| Refusal::Budget)?;
                self.context.push(d.clone());
                self.context_values.push(None);
                let inferred = self.infer_ann(&body.open(i));
                self.context.pop();
                self.context_values.pop();
                let inferred = inferred?;
                if matches!(t.0.as_ref(), Node::Lam(..)) {
                    Ok(Term::new(Node::Pi(
                        *b,
                        d.clone(),
                        inferred.abstract_local(i),
                    )))
                } else {
                    let sort = self.whnf(&inferred)?;
                    let Node::Sort(v) = sort.0.as_ref() else {
                        return Err(Refusal::Check("inferAnn Pi body is not a type".into()));
                    };
                    Ok(Term::new(Node::Sort(Level::imax(u.clone(), v.clone()))))
                }
            }
            Node::Let(_, ty, value, body) => {
                let tty = self.infer_ann(ty)?;
                let sort = self.whnf(&tty)?;
                if !matches!(sort.0.as_ref(), Node::Sort(_)) {
                    return Err(Refusal::Check("inferAnn let annotation".into()));
                }
                let i = u32::try_from(self.context.len()).map_err(|_| Refusal::Budget)?;
                self.context.push(ty.clone());
                self.context_values.push(Some(value.clone()));
                let result = self.infer_ann(&body.open(i));
                self.context.pop();
                self.context_values.pop();
                Ok(result?.abstract_local(i).instantiate(value))
            }
            Node::Lit(lit) => Ok(Term::new(Node::Const(
                Name::from_string(match lit {
                    crate::expr::Literal::Nat(_) => "Nat",
                    crate::expr::Literal::String(_) => "String",
                }),
                vec![],
            ))),
            Node::Proj(n, i, e) => self.projection_type(n, *i, e),
            Node::BVar(_) => Err(Refusal::Check("inferAnn loose bound variable".into())),
        }
    }
    /// Speculative conversion, with successful-path token rollback. This first
    /// core intentionally refuses missing rule families instead of delegating to
    /// an unchecked ordinary-kernel inference shortcut.
    pub fn conv(&mut self, a: &Term, b: &Term) -> Result<bool, Refusal> {
        let pair = (a.clone(), b.clone());
        if self.active_conversions.contains(&pair)
            || self
                .active_conversions
                .contains(&(pair.1.clone(), pair.0.clone()))
        {
            // Congruence of projections followed by structure eta can revisit
            // exactly the pair whose proof is still being searched for. This
            // branch has no finite certificate: fail it and try other rules.
            // This is a recursion guard, never an equality-result cache.
            self.conversion_cycles_cut += 1;
            return Ok(false);
        }
        self.active_conversions.insert(pair.clone());
        self.enter(FrameKind::Conv, false);
        self.built(a);
        self.built(b);
        let mark = self.journal.tokens.len();
        let result = stack_safe(|| self.conv_inner(a, b));
        if !matches!(result, Ok(true)) {
            self.journal.tokens.truncate(mark);
        }
        self.frames.pop();
        self.active_conversions.remove(&pair);
        result
    }
    fn head_beta_label(&mut self, label: &Term) -> Result<Expr, Refusal> {
        let mut raw = label.erase();
        loop {
            let head = raw.get_app_fn();
            let ExprKind::Lam(_, _, body) = head.kind() else {
                return Ok(raw);
            };
            let args: Vec<_> = raw.get_app_args().into_iter().cloned().collect();
            let Some(first) = args.first() else {
                return Ok(raw);
            };
            self.tick()?;
            let mut next = body.instantiate(first);
            for arg in args.into_iter().skip(1) {
                next = Expr::app(next, arg);
            }
            raw = next;
        }
    }
    fn spine(t: &Term) -> (Term, Vec<(Term, Label)>) {
        let mut head = t.clone();
        let mut args = Vec::new();
        while let Node::App(f, a, d) = head.0.as_ref() {
            args.push((a.clone(), d.clone()));
            head = f.clone();
        }
        args.reverse();
        (head, args)
    }
    fn reapply_extras(original: &Term, skip: usize, mut result: Term) -> Term {
        let mut nodes = Vec::new();
        let mut head = original;
        while let Node::App(function, argument, label) = head.0.as_ref() {
            nodes.push((head, argument, label));
            head = function;
        }
        // These are existing applications, not applications newly constructed
        // by the rule. Preserve their construction-head/minor provenance too.
        for (origin, argument, label) in nodes.into_iter().rev().skip(skip) {
            result = Term::new(Node::App(result, argument.clone(), label.clone()))
                .with_origin_of(origin);
        }
        result
    }
    fn projection_type(&mut self, n: &Name, index: u32, e: &Term) -> Result<Term, Refusal> {
        let ety = self.infer_ann(e)?;
        let ety = self.whnf(&ety)?;
        let (head, args) = Self::spine(&ety);
        let Node::Const(actual, levels) = head.0.as_ref() else {
            return Err(Refusal::Check("projection type is not an inductive".into()));
        };
        if actual != n {
            return Err(Refusal::Check("projection family mismatch".into()));
        }
        let ind = self
            .env
            .get_inductive(n)
            .cloned()
            .ok_or_else(|| Refusal::Check("unknown projection family".into()))?;
        if ind.constructor_names.len() != 1 {
            return Err(Refusal::Check("projection requires one constructor".into()));
        }
        let ctor_name = &ind.constructor_names[0];
        let ctor = self
            .env
            .get_constructor(ctor_name)
            .cloned()
            .ok_or_else(|| Refusal::Check("unknown structure constructor".into()))?;
        if index >= ctor.num_fields {
            return Err(Refusal::Check("projection index".into()));
        }
        let ty = self.constant_type(ctor_name)?;
        let mut ty = ty.instantiate_levels(&ctor.level_params, levels);
        for (argument, _) in args.iter().take(ctor.num_params as usize) {
            let pi = self.whnf(&ty)?;
            let Node::Pi(_, _, body) = pi.0.as_ref() else {
                return Err(Refusal::Check("constructor parameter telescope".into()));
            };
            ty = body.instantiate(argument);
        }
        for i in 0..=index {
            let pi = self.whnf(&ty)?;
            let Node::Pi(_, domain, body) = pi.0.as_ref() else {
                return Err(Refusal::Check("constructor field telescope".into()));
            };
            if i == index {
                return Ok(domain.clone());
            }
            ty = body.instantiate(&Term::new(Node::Proj(n.clone(), i, e.clone())));
        }
        Err(Refusal::Check("projection index".into()))
    }
    fn infer_for(&mut self, t: &Term, source: &'static str) -> Result<Term, Refusal> {
        let previous = self.infer_ann_source;
        self.infer_ann_source = source;
        let result = self.infer_ann(t);
        self.infer_ann_source = previous;
        result
    }
    fn apply(&mut self, f: Term, a: Term) -> Result<Term, Refusal> {
        let ty = self.infer_ann(&f)?;
        let pi = self.whnf(&ty)?;
        let Node::Pi(_, d, _) = pi.0.as_ref() else {
            return Err(Refusal::Check("generated application function type".into()));
        };
        let aty = self.infer_ann(&a)?;
        if !self.conv(&aty, d)? {
            return Err(Refusal::Check("generated application argument type".into()));
        }
        Ok(Term::new(Node::App(f, a, Label::Checked(d.clone()))))
    }
    fn walk_spine(
        &mut self,
        mut ty: Term,
        args: &[(Term, Label)],
        entry: &str,
        family: &str,
        target: &str,
        positions: &[String],
    ) -> Result<Term, Refusal> {
        let mark = self.journal.tokens.len();
        let frame_mark = self.frames.len();
        let mut all_identical = true;
        let mut last_domain = ty.clone();
        let result = (|| {
            for (position, (argument, label)) in args.iter().enumerate() {
                // Revision 2: the walk is recursive at each position. Keep its
                // frames live until the complete telescope has been traversed.
                self.enter(FrameKind::Walk, false);
                self.built(&ty);
                let Node::Pi(_, domain, body) = ty.0.as_ref() else {
                    return Err(self.hole("non_syntactic_spine_telescope", &ty.erase()));
                };
                last_domain = domain.clone();
                let start = self.journal.tokens.len();
                let head_start = self.attempted_head_steps;
                let source = format!("{entry}/{family}/{target}/{position}");
                let class = self.classify_domain(label, domain, &source)?;
                let identity = matches!(
                    class,
                    DomainClass::Identical | DomainClass::LevelInstantiated
                );
                all_identical &= identity;
                if identity {
                    self.journal.push(Token::Refl);
                }
                self.spine_comparisons.push(SpineComparison {
                    entry: entry.into(),
                    family: family.into(),
                    target: target.into(),
                    position_kind: positions
                        .get(position)
                        .cloned()
                        .unwrap_or_else(|| "field".into()),
                    position,
                    class: class.clone(),
                    conversion_tokens: (self.journal.tokens.len() - start) as u64,
                    conversion_head_steps: self.attempted_head_steps - head_start,
                });
                if matches!(class, DomainClass::Failed(_) | DomainClass::Missing(_)) {
                    self.domain_problems.push(DomainProblem {
                        source: format!("{entry}/{family}/{target}/{position}"),
                        term: argument.erase().to_string(),
                        label: match label {
                            Label::Checked(d) => Some(d.erase().to_string()),
                            Label::Missing(_) => None,
                        },
                        domain: domain.erase().to_string(),
                        class: class.clone(),
                    });
                    return Err(Refusal::Check(format!(
                        "{target} spine position {position}: {class:?}"
                    )));
                }
                ty = body.instantiate(argument);
                self.built(&ty);
            }
            Ok(last_domain)
        })();
        self.frames.truncate(frame_mark);
        if result.is_err() {
            self.journal.tokens.truncate(mark);
        } else if all_identical {
            self.journal.tokens.truncate(mark);
            self.journal.push(Token::SpineRefl(args.len() as u64));
        } else {
            self.journal
                .tokens
                .insert(mark, Token::SpineCerts(args.len() as u64));
        }
        result
    }
    fn classify_domain(
        &mut self,
        label: &Label,
        domain: &Term,
        source: &str,
    ) -> Result<DomainClass, Refusal> {
        let Label::Checked(d) = label else {
            if let Label::Missing(source) = label {
                return Ok(DomainClass::Missing(source.clone()));
            }
            return Err(Refusal::Check("major label".into()));
        };
        if d.erased_eq(domain) {
            return Ok(if d.before_levels() == domain.before_levels() {
                DomainClass::Identical
            } else {
                DomainClass::LevelInstantiated
            });
        }
        let start = self.journal.tokens.len();
        let equal = self.guard_conversion(d, domain, source)?;
        Ok(if equal {
            DomainClass::Convertible {
                steps: (self.journal.tokens.len() - start) as u64,
            }
        } else {
            DomainClass::Failed("stored domain conversion".into())
        })
    }
    fn literal_admitted(&self, literal: &crate::expr::Literal) -> bool {
        self.env.nat_literal_extension_canonical()
            && match literal {
                crate::expr::Literal::Nat(_) => true,
                crate::expr::Literal::String(_) => {
                    self.env
                        .get_const(&Name::from_string("String.ofList"))
                        .is_some()
                        && self
                            .env
                            .native_fold_authorized(&Name::from_string("Char.ofNat"))
                        && self
                            .env
                            .native_fold_authorized(&Name::from_string("String.ofList"))
                }
            }
    }
    /// Materialize literal sugar through the same canonical-definition gates
    /// as the ordinary kernel. Every newly constructed application is labelled
    /// by typed apply; existing labelled nodes are never erased and relabelled.
    pub fn expand_literal(&mut self, literal: &crate::expr::Literal) -> Result<Term, Refusal> {
        use crate::expr::Literal;
        let raw = Expr::from_kind(ExprKind::Lit(literal.clone()));
        if !self.env.nat_literal_extension_canonical() {
            return Err(self.hole("literal_Nat_extension_not_canonical", &raw));
        }
        match literal {
            Literal::Nat(n) => {
                *self.literal_expansions.entry("Nat".into()).or_default() += 1;
                if let Some(pred) = n.pred() {
                    self.apply(
                        Term::new(Node::Const(Name::from_string("Nat.succ"), vec![])),
                        Term::new(Node::Lit(Literal::Nat(pred))),
                    )
                } else {
                    Ok(Term::new(Node::Const(
                        Name::from_string("Nat.zero"),
                        vec![],
                    )))
                }
            }
            Literal::String(text) => {
                let of_list = Name::from_string("String.ofList");
                let char_of_nat = Name::from_string("Char.ofNat");
                if self.env.get_const(&of_list).is_none() {
                    return Err(self.hole("String_literal_ofList_missing_or_legacy_layout", &raw));
                }
                if !self.env.native_fold_authorized(&char_of_nat)
                    || !self.env.native_fold_authorized(&of_list)
                {
                    return Err(self.hole("String_literal_extension_not_canonical", &raw));
                }
                *self.literal_expansions.entry("String".into()).or_default() += 1;
                let char_type = Term::new(Node::Const(Name::from_string("Char"), vec![]));
                let mut list = self.apply(
                    Term::new(Node::Const(
                        Name::from_string("List.nil"),
                        vec![Level::zero()],
                    )),
                    char_type.clone(),
                )?;
                for c in text.chars().rev() {
                    self.tick()?;
                    let value = self.apply(
                        Term::new(Node::Const(char_of_nat.clone(), vec![])),
                        Term::new(Node::Lit(Literal::Nat(crate::expr::BigNat::Small(
                            u64::from(u32::from(c)),
                        )))),
                    )?;
                    let cons = self.apply(
                        Term::new(Node::Const(
                            Name::from_string("List.cons"),
                            vec![Level::zero()],
                        )),
                        char_type.clone(),
                    )?;
                    let cons = self.apply(cons, value)?;
                    list = self.apply(cons, list)?;
                }
                self.apply(Term::new(Node::Const(of_list, vec![])), list)
            }
        }
    }
    // These fourteen primitive Nat heads are an explicit extension of the
    // design Term. Use the existing kernel's admission and WHNF decisions;
    // return only atomic results, or the SAME labelled stuck application.
    fn native_nat_name(&self, t: &Term) -> Option<Name> {
        let raw = t.erase();
        let ExprKind::Const(name, levels) = raw.get_app_fn().kind() else {
            return None;
        };
        if !levels.is_empty()
            || !Environment::is_lean_kernel_nat_extension(name)
            || !self.env.nat_literal_extension_canonical()
        {
            return None;
        }
        let mut ty = &self.env.get_const(name)?.type_;
        let mut arity = 0usize;
        loop {
            match ty.kind() {
                ExprKind::MData(_, inner) => ty = inner,
                ExprKind::Pi(_, _, body) => {
                    arity += 1;
                    if arity > 2 {
                        return None;
                    }
                    ty = body;
                }
                _ => break,
            }
        }
        (arity == 2).then(|| name.clone())
    }
    fn application_nodes(t: &Term) -> (Term, Vec<(Term, Label, Term)>) {
        let mut head = t.clone();
        let mut nodes = Vec::new();
        while let Node::App(function, argument, label) = head.0.as_ref() {
            nodes.push((argument.clone(), label.clone(), head.clone()));
            head = function.clone();
        }
        nodes.reverse();
        (head, nodes)
    }
    fn rebuild_nodes(mut head: Term, nodes: &[(Term, Label, Term)]) -> Term {
        for (argument, label, old) in nodes {
            head = Term::new(Node::App(head, argument.clone(), label.clone())).with_origin_of(old);
        }
        head
    }
    fn native_nat(&mut self, t: &Term) -> Result<Option<(Term, bool)>, Refusal> {
        let Some(name) = self.native_nat_name(t) else {
            return Ok(None);
        };
        let (head, mut nodes) = Self::application_nodes(t);
        if nodes.len() < 2 {
            return Ok(None);
        }
        let mark = self.journal.tokens.len();
        for (argument, _, _) in nodes.iter_mut().take(2) {
            *argument = self.whnf(argument)?;
        }
        let prefix = Self::rebuild_nodes(head.clone(), &nodes[..2]);
        let raw = prefix.erase();
        let reduced = {
            let checker = self.context_checker()?;
            let result = checker.whnf(&raw);
            if checker.heartbeat_spent() {
                return Err(Refusal::Budget);
            }
            result
        };
        if reduced == raw {
            *self
                .native_nat_stops
                .entry(name.to_unambiguous_string())
                .or_default() += 1;
            return Ok(Some((Self::rebuild_nodes(head, &nodes), false)));
        }
        // A name alone never licenses a fold. The original kernel's canonical
        // definition/closure admission must hold. Its pure delta fallback is
        // replayed below instead, with the original labels, when it does not.
        if !self.env.native_fold_authorized(&name) {
            self.journal.tokens.truncate(mark);
            return Ok(None);
        }
        let value = match reduced.kind() {
            ExprKind::Lit(literal @ crate::expr::Literal::Nat(_)) => {
                Term::new(Node::Lit(literal.clone()))
            }
            ExprKind::Const(ctor, levels)
                if levels.is_empty()
                    && matches!(ctor.to_string().as_str(), "Bool.true" | "Bool.false") =>
            {
                Term::new(Node::Const(ctor.clone(), vec![]))
            }
            _ => {
                self.journal.tokens.truncate(mark);
                return Ok(None);
            }
        };
        let args: Vec<_> = nodes[..2]
            .iter()
            .map(|(a, d, _)| (a.clone(), d.clone()))
            .collect();
        let ty = self.constant_type(&name)?;
        self.walk_spine(
            ty,
            &args,
            "Nat_native",
            "Nat",
            "native",
            &["argument".into(), "argument".into()],
        )?;
        let nat = Term::new(Node::Const(Name::from_string("Nat"), vec![]));
        for (argument, _) in &args {
            let inferred = self.infer_for(argument, "NAT_NATIVE")?;
            if !self.conv(&inferred, &nat)? {
                return Err(Refusal::Check("native Nat operand type".into()));
            }
        }
        *self
            .native_nat_steps
            .entry(name.to_unambiguous_string())
            .or_default() += 1;
        self.journal.push(Token::CoreL(1));
        Ok(Some((Self::rebuild_nodes(value, &nodes[2..]), true)))
    }
    fn unfold_nat_application(&mut self, t: &Term) -> Result<Option<Term>, Refusal> {
        let Some(name) = self.native_nat_name(t) else {
            return Ok(None);
        };
        let (_, nodes) = Self::application_nodes(t);
        if nodes.len() < 2 {
            return Ok(None);
        }
        let Some(body) = self.constant_value(&name, &[])? else {
            return Ok(None);
        };
        self.journal.push(Token::DeltaL);
        Ok(Some(Self::rebuild_nodes(body, &nodes)))
    }
    fn quotient(&mut self, t: &Term) -> Result<Option<Term>, Refusal> {
        let (head, args) = Self::spine(t);
        let Node::Const(name, _) = head.0.as_ref() else {
            return Ok(None);
        };
        let Some(info) = self.env.get_quot(name) else {
            return Ok(None);
        };
        let arity = match info.kind {
            crate::quot::QuotKind::Lift => 6,
            crate::quot::QuotKind::Ind => 5,
            _ => return Ok(None),
        };
        if args.len() < arity {
            return Ok(None);
        }
        let major = self.whnf(&args[arity - 1].0)?;
        let (ctor, fields) = Self::spine(&major);
        let Node::Const(name, _) = ctor.0.as_ref() else {
            return Ok(None);
        };
        if !self
            .env
            .get_quot(name)
            .is_some_and(|q| q.kind == crate::quot::QuotKind::Mk)
            || fields.len() < 3
        {
            return Ok(None);
        }
        // Quotient reduction is outside the current design slice. Its newly
        // built f a is labelled by the same typed apply operation as inference;
        // no raw unlabelled Expr is substituted into the carrier.
        let mut result = self.apply(args[3].0.clone(), fields[2].0.clone())?;
        for (a, d) in args.iter().skip(arity) {
            result = Term::new(Node::App(result, a.clone(), d.clone()));
        }
        self.journal.push(Token::CoreL(1));
        Ok(Some(result))
    }
    fn iota(&mut self, t: &Term) -> Result<Option<Term>, Refusal> {
        use crate::inductive::RecursorArgOrder;
        let (head, args) = Self::spine(t);
        let Node::Const(name, levels) = head.0.as_ref() else {
            return Ok(None);
        };
        let Some(rec) = self.env.get_recursor(name).cloned() else {
            return Ok(None);
        };
        if self.env.get_const(name).is_some_and(|c| c.value.is_some()) {
            return Ok(None);
        }
        let pm = (rec.num_params + rec.num_motives) as usize;
        let major_index = match rec.arg_order {
            RecursorArgOrder::MajorAfterMinors => {
                pm + rec.num_minors as usize + rec.num_indices as usize
            }
            RecursorArgOrder::MajorAfterMotive => pm + rec.num_indices as usize,
        };
        let extras = major_index
            + 1
            + if matches!(rec.arg_order, RecursorArgOrder::MajorAfterMotive) {
                rec.num_minors as usize
            } else {
                0
            };
        if args.len() < extras {
            return Ok(None);
        }
        // The slice's Eq K rule is the design's direct index guard: do not
        // normalize the proof or infer its type in order to manufacture refl.
        if rec.is_k && name == &Name::from_string("Eq.rec") && major_index == 5 {
            let (major_head, _) = Self::spine(&args[major_index].0);
            let syntactic_ctor = matches!(major_head.0.as_ref(),Node::Const(n,_) if self.env.get_constructor(n).is_some());
            if !syntactic_ctor {
                let mark = self.journal.tokens.len();
                if self.guard_conversion(&args[4].0, &args[1].0, "K/Eq/index")? {
                    let index_certificate = self.journal.tokens.split_off(mark);
                    self.journal.push(Token::K);
                    let ty = self
                        .constant_type(name)?
                        .instantiate_levels(&rec.level_params, levels);
                    let positions: Vec<_> = [
                        "parameter",
                        "parameter",
                        "motive",
                        "minor",
                        "index",
                        "major",
                    ]
                    .into_iter()
                    .map(str::to_string)
                    .collect();
                    self.walk_spine(ty, &args[..=major_index], "K", "Eq", "recursor", &positions)?;
                    self.journal.tokens.extend(index_certificate);
                    if let Some(event) = self.spine_comparisons.last() {
                        self.k_classes
                            .push((name.to_unambiguous_string(), event.class.clone()));
                    }
                    if t.had_other_head(name) {
                        self.recursor_spines_other_head += 1;
                    }
                    let result = Self::reapply_extras(t, extras, args[3].0.clone());
                    self.journal.push(Token::CoreL(1));
                    return Ok(Some(result));
                }
                self.journal.tokens.truncate(mark);
            }
        }
        let major = &args[major_index].0;
        let mut value = major.clone();
        let mut k_used = false;
        let mut entry = "constructor_iota";
        if rec.is_k {
            let (mh, _) = Self::spine(major);
            if !matches!(mh.0.as_ref(),Node::Const(n,_) if self.env.get_constructor(n).is_some()) {
                let ty = self.infer_for(major, "K")?;
                let ty = self.whnf(&ty)?;
                let (th, ta) = Self::spine(&ty);
                if let Node::Const(family, type_levels) = th.0.as_ref() {
                    if family == &rec.inductive_name && rec.rules.len() == 1 {
                        let ctor_name = &rec.rules[0].constructor_name;
                        if let Some(ctor) = self.env.get_constructor(ctor_name).cloned() {
                            let arity = (ctor.num_params + ctor.num_fields) as usize;
                            if rec.num_params as usize <= arity && ta.len() >= arity {
                                let ctor_levels = if levels.len() > 1 {
                                    levels[1..].to_vec()
                                } else {
                                    type_levels.clone()
                                };
                                let mut ctor =
                                    Term::new(Node::Const(ctor_name.clone(), ctor_levels));
                                for (a, _) in ta.iter().take(arity) {
                                    ctor = self.apply(ctor, a.clone())?;
                                }
                                let ctor_type = self.infer_for(&ctor, "K")?;
                                if self.conv(&ty, &ctor_type)? {
                                    value = ctor;
                                    k_used = true;
                                }
                            }
                        }
                    }
                }
            }
        }
        value = self.whnf(&value)?;
        if let Node::Lit(literal) = value.0.as_ref() {
            if matches!(literal, crate::expr::Literal::String(_))
                && self
                    .env
                    .get_const(&Name::from_string("String.ofList"))
                    .is_none()
                && self
                    .env
                    .get_constructor(&Name::from_string("String.mk"))
                    .is_some()
            {
                return Err(self.hole(
                    "String_legacy_constructor_expansion_not_implemented",
                    &value.erase(),
                ));
            }
            entry = match literal {
                crate::expr::Literal::Nat(_) => "Nat_literal",
                crate::expr::Literal::String(_) => "String_literal",
            };
            if self.literal_admitted(literal) {
                let expanded = self.expand_literal(literal)?;
                value = if matches!(literal, crate::expr::Literal::String(_)) {
                    self.whnf(&expanded)?
                } else {
                    expanded
                };
            } else {
                *self
                    .literal_admission_skips
                    .entry(entry.into())
                    .or_default() += 1;
                entry = "constructor_iota";
            }
        }
        let (value_head, _) = Self::spine(&value);
        if !matches!(value_head.0.as_ref(),Node::Const(n,_) if self.env.get_constructor(n).is_some())
        {
            if let Some(expanded) = self.structure_eta(&value)? {
                if entry == "constructor_iota" {
                    entry = "structure_eta";
                }
                value = expanded;
            }
        }
        let (constructor, fields) = Self::spine(&value);
        let Node::Const(ctor_name, _) = constructor.0.as_ref() else {
            return Ok(None);
        };
        let Some(rule) = rec.rules.iter().find(|r| &r.constructor_name == ctor_name) else {
            return Ok(None);
        };
        if fields.len() < rule.num_fields as usize || levels.len() != rec.level_params.len() {
            return Ok(None);
        }
        let major_family = self
            .env
            .get_constructor(ctor_name)
            .map(|c| c.inductive_name.clone())
            .ok_or_else(|| Refusal::Check("major constructor family".into()))?;
        if k_used {
            entry = "K";
        }
        if t.had_other_head(name) {
            self.recursor_spines_other_head += 1;
        }
        self.journal
            .push(if k_used { Token::K } else { Token::Iota });
        let positions: Vec<_> = (0..=major_index)
            .map(|i| {
                if i < rec.num_params as usize {
                    "parameter"
                } else if i < pm {
                    "motive"
                } else if i == major_index {
                    "major"
                } else if matches!(rec.arg_order, RecursorArgOrder::MajorAfterMinors)
                    && i < pm + rec.num_minors as usize
                {
                    "minor"
                } else {
                    "index"
                }
                .to_string()
            })
            .collect();
        let rec_type = self
            .constant_type(name)?
            .instantiate_levels(&rec.level_params, levels);
        let major_domain = self.walk_spine(
            rec_type,
            &args[..=major_index],
            entry,
            &major_family.to_unambiguous_string(),
            "recursor",
            &positions,
        )?;
        if let Some(event) = self.spine_comparisons.last() {
            if k_used {
                self.k_classes
                    .push((name.to_unambiguous_string(), event.class.clone()));
            } else {
                self.iota_classes
                    .push((name.to_unambiguous_string(), event.class.clone()));
            }
        }
        let mut domain_head = &major_domain;
        while let Node::App(function, _, _) = domain_head.0.as_ref() {
            domain_head = function;
        }
        let expected_levels = match domain_head.0.as_ref() {
            Node::Const(family, levels) if family == &major_family => Some(levels.clone()),
            _ => None,
        };
        drop(major_domain);
        let Node::Const(_, ctor_levels) = constructor.0.as_ref() else {
            return Ok(None);
        };
        let ctor_info = self
            .env
            .get_constructor(ctor_name)
            .cloned()
            .ok_or_else(|| Refusal::Check("constructor metadata".into()))?;
        let ctor_const = self
            .env
            .get_const(ctor_name)
            .ok_or_else(|| Refusal::Check("constructor declaration".into()))?;
        let ctor_params = ctor_const.level_params.clone();
        if let Some(expected) = expected_levels {
            let kind = if &expected == ctor_levels {
                "identical"
            } else if expected.len() == ctor_levels.len()
                && expected
                    .iter()
                    .zip(ctor_levels)
                    .all(|(u, v)| self.levels_equal(u, v))
            {
                "level_equal"
            } else {
                "failed"
            };
            *self.constructor_levels.entry(kind.into()).or_default() += 1;
            if kind == "failed" {
                return Err(Refusal::Check(format!(
                    "constructor universe arguments at {name}: {ctor_name}; expected {expected:?}, actual {ctor_levels:?}; term {}",value.erase()
                )));
            }
        } else {
            *self
                .constructor_levels
                .entry("major_domain_head_unavailable".into())
                .or_default() += 1;
        }
        let ctor_type = self
            .constant_type(ctor_name)?
            .instantiate_levels(&ctor_params, ctor_levels);
        let positions: Vec<_> = (0..fields.len())
            .map(|i| {
                if i < ctor_info.num_params as usize {
                    "parameter".into()
                } else {
                    "field".into()
                }
            })
            .collect();
        let ctor_mark = self.journal.tokens.len();
        // The current IOTA rule charges I3 for every family, including Prop.
        // K still has c=0, so its constructor diagnostics are not charged.
        self.walk_spine(
            ctor_type,
            &fields,
            entry,
            &major_family.to_unambiguous_string(),
            "constructor",
            &positions,
        )?;
        if k_used {
            self.journal.tokens.truncate(ctor_mark);
        }
        let minors_start = if matches!(rec.arg_order, RecursorArgOrder::MajorAfterMinors) {
            pm
        } else {
            major_index + 1
        };
        let mut supplied: Vec<(Term, Label)> = args.iter().take(pm).cloned().collect();
        supplied.extend(
            args.iter()
                .skip(minors_start)
                .take(rec.num_minors as usize)
                .cloned(),
        );
        supplied.extend(
            fields
                .iter()
                .skip(fields.len() - rule.num_fields as usize)
                .cloned(),
        );
        let raw = rule
            .rhs
            .instantiate_level_params_direct(&rec.level_params, levels);
        if !matches!(raw.kind(), ExprKind::Lam(..)) {
            if k_used && rule.num_fields == 0 && rec.num_minors == 1 {
                let result = Self::reapply_extras(t, extras, args[minors_start].0.clone());
                self.journal.push(Token::CoreL(1));
                return Ok(Some(result));
            }
            return Err(self.hole("legacy_recursor_rhs", &raw));
        }
        let existing = self
            .labelled
            .and_then(|env| env.rules.get(&(name.clone(), ctor_name.clone())))
            .cloned();
        let mut rhs = if let Some(rhs) = existing {
            rhs.instantiate_levels(&rec.level_params, levels)
        } else {
            if self.labelled.is_some() {
                self.reannotated_dependencies
                    .insert(format!("{name}/rule/{ctor_name}"));
            }
            let context = std::mem::take(&mut self.context);
            let values = std::mem::take(&mut self.context_values);
            let checked = self.check(&raw);
            self.context = context;
            self.context_values = values;
            checked?
                .0
                .mark_minor_heads(&rec.name, rec.num_params + rec.num_motives, rec.num_minors)
        };
        if k_used {
            // The slice's K returns the minor directly. Retain the existing
            // generic-K synthesis extension without inventing IOTA betas.
            for (a, _) in supplied {
                if let Node::Lam(_, _, body) = rhs.0.as_ref() {
                    rhs = body.instantiate(&a);
                } else {
                    rhs = self.apply(rhs, a)?;
                }
            }
        } else {
            // Model-first Revision 4 returns this labelled spine. In
            // particular, retain the arguments' OLD labels: inferring new
            // labels from rhs would hide the very DOM comparisons C4 measures.
            // The normal head loop then guards every administrative beta.
            for (a, label) in supplied {
                rhs = Term::new(Node::App(rhs, a, label));
            }
        }
        rhs = Self::reapply_extras(t, extras, rhs);
        self.journal.push(Token::CoreL(1));
        Ok(Some(rhs))
    }
    // A negative experimental conversion is never reported as an R2 failure
    // until the existing kernel independently refuses the same pair in the
    // same local context. A kernel acceptance is an implementation coverage gap.
    fn structure_eta(&mut self, value: &Term) -> Result<Option<Term>, Refusal> {
        let (head, _) = Self::spine(value);
        if matches!(head.0.as_ref(),Node::Const(n,_) if self.env.get_constructor(n).is_some()) {
            return Ok(None);
        }
        let ty = self.infer_for(value, "STRUCT_ETA")?;
        let ty = self.whnf(&ty)?;
        let (head, args) = Self::spine(&ty);
        let Node::Const(family, levels) = head.0.as_ref() else {
            return Ok(None);
        };
        let Some(ind) = self.env.get_inductive(family).cloned() else {
            return Ok(None);
        };
        if ind.constructor_names.len() != 1 || ind.num_indices != 0 || ind.is_recursive {
            return Ok(None);
        }
        let Some(ctor) = self.env.get_constructor(&ind.constructor_names[0]).cloned() else {
            return Ok(None);
        };
        let mut expanded = Term::new(Node::Const(ctor.name.clone(), levels.clone()));
        for (argument, _) in args.iter().take(ctor.num_params as usize) {
            expanded = self.apply(expanded, argument.clone())?;
        }
        for i in 0..ctor.num_fields {
            expanded = self.apply(
                expanded,
                Term::new(Node::Proj(family.clone(), i, value.clone())),
            )?;
        }
        Ok(Some(expanded))
    }
    fn guard_conversion(&mut self, a: &Term, b: &Term, source: &str) -> Result<bool, Refusal> {
        // Observe the kernel even if the producer later reaches a certificate
        // gap or its own operation budget. Such a gap must not hide an oracle
        // comparison or be confused with the kernel refusing this domain pair.
        let ordinary = self.ordinary_conversion(a, b, source)?;
        if !ordinary {
            return Ok(false);
        }
        let traced = self.conv(a, b)?;
        if !traced {
            return Err(self.hole(
                "guard_conversion_rule_gap",
                &Expr::app(a.erase(), b.erase()),
            ));
        }
        Ok(true)
    }
    fn context_checker(&self) -> Result<crate::tc::TypeChecker<'a>, Refusal> {
        let mut context = crate::tc::LocalContext::new();
        for (i, ty) in self.context.iter().enumerate() {
            let id = crate::expr::FVarId(u64::try_from(i).map_err(|_| Refusal::Budget)?);
            if let Some(Some(value)) = self.context_values.get(i) {
                context.push_let_with_id(
                    id,
                    Name::from_string("trace_local"),
                    ty.erase(),
                    value.erase(),
                );
            } else {
                context.push_with_id(
                    id,
                    Name::from_string("trace_local"),
                    ty.erase(),
                    crate::expr::BinderData::default(),
                );
            }
        }
        Ok(crate::tc::TypeChecker::with_context(self.env, context))
    }
    fn ordinary_conversion(&mut self, a: &Term, b: &Term, source: &str) -> Result<bool, Refusal> {
        let mut checker = self.context_checker()?;
        checker.enable_heartbeat_profiler();
        let equal = checker.is_def_eq(&a.erase(), &b.erase());
        let budget_exhausted = checker.heartbeat_spent();
        let profile = checker
            .heartbeat_profile()
            .ok_or_else(|| Refusal::Check("existing-kernel conversion profiler absent".into()))?;
        self.oracle_conversions.push(OracleConversion {
            source: source.into(),
            equal,
            budget_exhausted,
            heartbeats: profile.total(),
            categories: profile
                .categories()
                .iter()
                .map(|entry| (entry.category.to_string(), entry.heartbeats))
                .collect(),
        });
        if budget_exhausted {
            return Err(Refusal::Budget);
        }
        Ok(equal)
    }
    fn levels_equal(&self, a: &Level, b: &Level) -> bool {
        crate::tc::TypeChecker::new(self.env)
            .is_def_eq(&Expr::sort(a.clone()), &Expr::sort(b.clone()))
    }
    fn structural(&mut self, a: &Term, b: &Term) -> Result<Option<bool>, Refusal> {
        match (a.0.as_ref(), b.0.as_ref()) {
            (Node::Sort(u), Node::Sort(v)) => {
                let equal = self.levels_equal(u, v);
                if equal {
                    self.journal.push(Token::Sort);
                }
                Ok(Some(equal))
            }
            (Node::Const(n, ls), Node::Const(m, rs)) if n == m && ls.len() == rs.len() => {
                let equal = ls.iter().zip(rs).all(|(u, v)| self.levels_equal(u, v));
                if equal {
                    self.journal.push(Token::Const);
                }
                Ok(Some(equal))
            }
            (Node::Proj(n, i, a), Node::Proj(m, j, b)) if n == m && i == j => {
                Ok(Some(self.conv(a, b)?))
            }
            (Node::App(f, a, _), Node::App(g, b, _)) => {
                self.journal.push(Token::App);
                Ok(Some(self.conv(f, g)? && self.conv(a, b)?))
            }
            (Node::Lam(_, d, t), Node::Lam(_, e, s)) | (Node::Pi(_, d, t), Node::Pi(_, e, s)) => {
                self.journal.push(if matches!(a.0.as_ref(), Node::Lam(..)) {
                    Token::Lam
                } else {
                    Token::Pi
                });
                if !self.conv(d, e)? {
                    return Ok(Some(false));
                }
                let i = u32::try_from(self.context.len()).map_err(|_| Refusal::Budget)?;
                self.context.push(d.clone());
                self.context_values.push(None);
                let result = self.conv(&t.open(i), &s.open(i));
                self.context.pop();
                self.context_values.pop();
                result.map(Some)
            }
            _ => Ok(None),
        }
    }
    fn eta(&mut self, lambda: &Term, other: &Term, right: bool) -> Result<bool, Refusal> {
        let ty = self.infer_for(other, "ETA")?;
        let ty = self.whnf(&ty)?;
        let Node::Pi(b, d, _) = ty.0.as_ref() else {
            return Ok(false);
        };
        self.journal
            .push(if right { Token::EtaR } else { Token::EtaL });
        let body = Term::new(Node::App(
            other.lift(1, 0),
            Term::new(Node::BVar(0)),
            Label::Checked(d.lift(1, 0)),
        ));
        let expanded = Term::new(Node::Lam(*b, d.clone(), body));
        self.conv(lambda, &expanded)
    }
    fn proof_irrel(&mut self, a: &Term, b: &Term) -> Result<bool, Refusal> {
        let a_type = self.infer_for(a, "IRREL")?;
        let sort = self.infer_for(&a_type, "IRREL")?;
        let sort = self.whnf(&sort)?;
        if !matches!(sort.0.as_ref(),Node::Sort(l) if l.is_zero()) {
            return Ok(false);
        }
        let b_type = self.infer_for(b, "IRREL")?;
        self.journal.push(Token::Irrel);
        self.conv(&a_type, &b_type)
    }
    fn conv_inner(&mut self, a: &Term, b: &Term) -> Result<bool, Refusal> {
        self.tick()?;
        if a.erased_eq(b) {
            self.journal.push(Token::Refl);
            return Ok(true);
        }
        let mark = self.journal.tokens.len();
        if matches!(self.structural(a, b)?, Some(true)) {
            return Ok(true);
        }
        self.journal.tokens.truncate(mark);
        let a = self.whnf(a)?;
        let b = self.whnf(b)?;
        if a.erased_eq(&b) {
            self.journal.push(Token::Refl);
            return Ok(true);
        }
        match (a.0.as_ref(), b.0.as_ref()) {
            (Node::Lit(crate::expr::Literal::Nat(_)), Node::Lit(crate::expr::Literal::Nat(_))) => {
                return Ok(false)
            }
            (
                Node::Lit(crate::expr::Literal::String(_)),
                Node::Lit(crate::expr::Literal::String(_)),
            ) => return Ok(false),
            (Node::Lit(literal), _) => {
                let expanded = self.expand_literal(literal)?;
                return self.conv(&expanded, &b);
            }
            (_, Node::Lit(_)) => return self.conv(&b, &a),
            _ => {}
        }
        let mark = self.journal.tokens.len();
        let structural = self.structural(&a, &b)?;
        if structural == Some(true) {
            return Ok(true);
        }
        self.journal.tokens.truncate(mark);
        if matches!(a.0.as_ref(), Node::Sort(_) | Node::Pi(..))
            && matches!(b.0.as_ref(), Node::Sort(_) | Node::Pi(..))
        {
            return Ok(false);
        }
        if matches!(a.0.as_ref(), Node::Lam(..)) && !matches!(b.0.as_ref(), Node::Lam(..)) {
            if self.eta(&a, &b, true)? {
                return Ok(true);
            }
            self.journal.tokens.truncate(mark);
        }
        if matches!(b.0.as_ref(), Node::Lam(..)) && !matches!(a.0.as_ref(), Node::Lam(..)) {
            if self.eta(&b, &a, false)? {
                return Ok(true);
            }
            self.journal.tokens.truncate(mark);
        }
        if self.proof_irrel(&a, &b)? {
            return Ok(true);
        }
        self.journal.tokens.truncate(mark);
        if let Some(expanded) = self.structure_eta(&a)? {
            if !expanded.erased_eq(&a) {
                if self.conv(&expanded, &b)? {
                    return Ok(true);
                }
                self.journal.tokens.truncate(mark);
            }
        }
        if let Some(expanded) = self.structure_eta(&b)? {
            if !expanded.erased_eq(&b) {
                if self.conv(&a, &expanded)? {
                    return Ok(true);
                }
                self.journal.tokens.truncate(mark);
            }
        }
        if self.ordinary_conversion(&a, &b, "conversion_rule_gap")? {
            return Err(self.hole("conversion_rule_gap", &Expr::app(a.erase(), b.erase())));
        }
        Ok(false)
    }
}
