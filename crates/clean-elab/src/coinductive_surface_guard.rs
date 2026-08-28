// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Guarded premises for the `coinductive` lowering — the "P under `∀`/`→`"
//! rung of the full-gfp program (named as the next rung by
//! `designs/2026-08-25-rank1-full-gfp-lowering.md`'s non-goals: the
//! Milner-style weak-bisimulation clause shape). Premise classification
//! ([`classify_premise`]) lives here with the guarded-clause envelope,
//! rendering and `F_mono` mapping; the parent module owns everything else.
//!
//! A premise may be a GUARDED clause
//!
//! ```text
//! ∀ b⃗, H₁ → … → Hₙ → C
//! ```
//!
//! where the binders `b⃗` are LEADING, explicit and explicitly typed with
//! `P`-free types; every hypothesis `Hᵢ` is `P`-FREE; and the conclusion
//! `C` is either the fully-applied recursive atom `P e⃗` (`e⃗` `P`-free) or
//! an `∃`-nest over a right-nested conjunction whose conjuncts are each
//! `P`-free or recursive atoms. `∃` is a POSITIVE former, so `P` under it
//! stays strictly positive — the `∃`-conclusion is exactly the weak
//! bisimulation clause `∀ x s', Step s x s' → ∃ t', Step t x t' ∧ P s' t'`,
//! and it is ADMITTED (in, not out) because the `F_mono` mapping it needs
//! is the machinery the Brick-2 disjunct `∃` already built:
//! `Exists.elim` / rebuild-with-the-SAME-witnesses / `Exists.intro`.
//!
//! `P` may therefore appear ONLY in the final conclusion — never left of an
//! arrow, never in a binder type: strict positivity is enforced by the
//! ENVELOPE, not discovered, and every violation refuses with a message
//! naming the negative / non-strictly-positive occurrence. A guarded clause
//! that is entirely `P`-free is a [`Premise::Plain`] side condition like
//! any other (guarded side conditions were always admitted that way).
//!
//! THE PARENTHESIZATION TAX: a guarded premise must be written in parens
//! (`| step : (∀ (q : St), Step s q → Sim q t) → Sim s t`) — bare leading
//! `∀`s of a constructor type are CONSTRUCTOR binders (the Brick-2 `∃`
//! lowering), unchanged.
//!
//! Generation impact (everything else is premise-shape-agnostic):
//!
//! * the functor body substitutes `P := R` at the conclusion atoms ONLY —
//!   the guard is carried verbatim ([`GuardedPremise::at_rel`]);
//! * `P.F_mono` maps `R ≤ S` UNDER the guard ([`GuardedPremise::mono_map`]):
//!   `fun b⃗ h⃗ => hle e⃗ (h b⃗ h⃗)` at an atom conclusion — monotonicity of
//!   `∀`/`→` in the positive position — and, at an `∃` conclusion,
//!   `Exists.elim` of the applied proof rebuilt with the SAME witnesses
//!   around the per-conjunct mapping (sound because the `∃` domains are
//!   `P`-free by the envelope, so an `R`-side witness inhabits the `S`-side
//!   domain unchanged);
//! * intro theorems and `P.cases` arms carry the guarded clause at `P`
//!   verbatim (hypothesis pass-through — no construction touches it), and
//!   `P.acc` / `P.coind_upto` route through `P.F_mono` generically — all
//!   four verified unchanged by the guarded-premise battery.

use super::{flatten_arrows, generate, mentions, strip_parens, target, HYP_G_PREFIX, HYP_LE};
use clean_parser::{Span, SurfaceBinder, SurfaceBinderInfo, SurfaceExpr};

// ── the premise taxonomy ─────────────────────────────────────────────────

/// One premise of a constructor.
pub(super) enum Premise {
    /// A fully-applied recursive occurrence `P e⃗` (arity n).
    Rec(Vec<SurfaceExpr>),
    /// A premise that does not mention `P` at all.
    Plain(SurfaceExpr),
    /// A guarded clause `∀ b⃗, H₁ → … → Hₙ → C` with `P` strictly positive
    /// in the conclusion (the "P under `∀`/`→`" rung; see the module doc).
    Guarded(GuardedPremise),
}

/// A validated guarded clause. Invariants (enforced by [`classify_premise`]):
/// binders explicit, explicitly typed, `P`-free-typed, pairwise distinct,
/// marker-free; hypotheses `P`-free; the conclusion mentions `P`.
pub(super) struct GuardedPremise {
    binders: Vec<SurfaceBinder>,
    hyps: Vec<SurfaceExpr>,
    concl: GuardedConcl,
}

/// The conclusion of a guarded clause — the only place `P` may occur.
enum GuardedConcl {
    /// The recursive atom `P e⃗` (`e⃗` `P`-free).
    Rec(Vec<SurfaceExpr>),
    /// `∃ y⃗, C₁ ∧ … ∧ Cⱼ` — a positive `∃`-nest over a right-nested
    /// conjunction; at least one conjunct is a recursive atom.
    Exists {
        binders: Vec<SurfaceBinder>,
        conjuncts: Vec<ExConjunct>,
    },
}

/// One conjunct under an `∃`-conclusion.
enum ExConjunct {
    /// The recursive atom `P e⃗`.
    Rec(Vec<SurfaceExpr>),
    /// A `P`-free proposition, carried verbatim.
    Plain(SurfaceExpr),
}

// ── classification ───────────────────────────────────────────────────────

/// Classify one premise of a constructor. `Err` carries the WHY — a full
/// reason clause the caller prefixes with the declaration/constructor
/// context — for every shape whose positivity is not established here.
pub(super) fn classify_premise(
    p: &SurfaceExpr,
    short: &str,
    params: &[String],
    arity: usize,
) -> Result<Premise, String> {
    let stripped = strip_parens(p);
    if let Some(args) = rec_atom(stripped, short, params, arity)? {
        return Ok(Premise::Rec(args));
    }
    if !mentions(p, short) {
        return Ok(Premise::Plain(p.clone()));
    }
    classify_guarded(stripped, short, params, arity)
}

/// Is `e` the fully-applied recursive atom `short p⃗ e₁ … e_arity` — the
/// declaration-parameter row EXACTLY as declared, then the index
/// arguments? A `short`-headed application that is NOT the well-formed
/// atom (wrong arity, a varied parameter position, named arguments,
/// `short` nested in an index argument) is an error, never a silent
/// fall-through. The returned vector is the INDEX arguments only: the
/// recursive substitution happens at `P p⃗`, so the functor's `R`
/// occurrences never mention the row.
fn rec_atom(
    e: &SurfaceExpr,
    short: &str,
    params: &[String],
    arity: usize,
) -> Result<Option<Vec<SurfaceExpr>>, String> {
    let SurfaceExpr::App(_, head, args) = e else {
        return Ok(None);
    };
    if !matches!(strip_parens(head), SurfaceExpr::Ident(_, id) if id == short) {
        return Ok(None);
    }
    if args.len() != params.len() + arity || args.iter().any(|a| a.name.is_some()) {
        let spelled = if params.is_empty() {
            format!("`{short} e₁ … e{arity}` with exactly {arity} positional argument(s)")
        } else {
            format!(
                "`{short} {} e₁ … e{arity}` with the declared parameter row \
                 then exactly {arity} positional index argument(s)",
                params.join(" ")
            )
        };
        return Err(format!(
            "a recursive occurrence of `{short}` must be FULLY APPLIED — \
             {spelled}; a partially-applied or named-argument occurrence \
             is refused because its positivity is not established here"
        ));
    }
    super::params::check_param_row(args, params, short)?;
    let idx_args = &args[params.len()..];
    if idx_args.iter().any(|a| mentions(&a.expr, short)) {
        return Err(format!(
            "a recursive occurrence `{short} e⃗` has an argument that itself \
             mentions `{short}` — a nested occurrence whose positivity is \
             not established here"
        ));
    }
    Ok(Some(idx_args.iter().map(|a| a.expr.clone()).collect()))
}

/// Which clause of a guarded premise a binder belongs to (for messages).
#[derive(Clone, Copy)]
enum BinderSite {
    Guard,
    Exists,
}

impl BinderSite {
    fn label(self) -> &'static str {
        match self {
            BinderSite::Guard => "guarded premise",
            BinderSite::Exists => "guarded premise's ∃-conclusion",
        }
    }
}

/// The binder envelope shared by the guard `∀` row and the `∃`-conclusion
/// nest. Guard binders must be explicitly typed (the generated `F_mono`
/// proof re-abstracts them; the declared type is also what the functor
/// carries); `∃` binders may be untyped — the domain is elaborator-inferred
/// inside the kernel-checked functor, and `F_mono` re-supplies the SAME
/// witness, so no type is ever reconstructed from here.
fn check_clause_binder(
    b: &SurfaceBinder,
    earlier: &[SurfaceBinder],
    short: &str,
    params: &[String],
    site: BinderSite,
) -> Result<(), String> {
    let where_ = site.label();
    if params.contains(&b.name) {
        return Err(format!(
            "a {where_} declares binder `{}`, which shadows the declaration \
             parameter of the same name; under the shadow a recursive \
             occurrence `{short} {} …` would no longer apply the FIXED \
             parameter row",
            b.name,
            params.join(" ")
        ));
    }
    if b.name == "_" {
        return Err(format!(
            "a {where_} declares an anonymous binder `_`; the generated \
             `F_mono` proof must re-supply every bound variable by NAME \
             (re-abstraction / `Exists.intro` witness)"
        ));
    }
    if b.info != SurfaceBinderInfo::Explicit {
        return Err(format!(
            "a {where_} declares binder `{}` as implicit/instance; only \
             explicit binders are supported under a guard",
            b.name
        ));
    }
    if b.default.is_some() {
        return Err(format!(
            "a {where_} declares binder `{}` with a default value, which \
             has no meaning under a guard",
            b.name
        ));
    }
    if b.name == short {
        return Err(format!(
            "a {where_} declares binder `{}` named after the predicate \
             itself; every occurrence of `{short}` in a premise must be the \
             recursive predicate, not a local",
            b.name
        ));
    }
    if b.name.contains("_coind") {
        return Err(format!(
            "a {where_} declares binder `{}`, which carries the `_coind` \
             marker reserved for generated binder names — it could be \
             captured inside the generated proofs",
            b.name
        ));
    }
    if earlier.iter().any(|e| e.name == b.name) {
        return Err(format!(
            "a {where_} declares binder `{}` twice; the inner occurrence \
             would shadow the outer one inside the generated proofs",
            b.name
        ));
    }
    match (site, b.ty.as_deref()) {
        (BinderSite::Guard, None) => Err(format!(
            "a guarded premise declares binder `{}` without a type; guard \
             binders must be explicitly typed (`∀ ({} : T), …`)",
            b.name, b.name
        )),
        (_, Some(ty)) if mentions(ty, short) => Err(format!(
            "the type of binder `{}` in a {where_} mentions `{short}` — a \
             binder-type occurrence is a negative/non-strictly-positive \
             hazard; binder types under a guard must be `{short}`-free",
            b.name
        )),
        _ => Ok(()),
    }
}

/// Classify a premise that mentions `P` and is not the flat recursive atom:
/// admit the guarded envelope of the module doc, refuse everything else by
/// name.
fn classify_guarded(
    p: &SurfaceExpr,
    short: &str,
    params: &[String],
    arity: usize,
) -> Result<Premise, String> {
    // Leading `∀` groups only — mirroring the constructor-binder peel.
    let mut binders: Vec<SurfaceBinder> = Vec::new();
    let mut chain = p;
    while let SurfaceExpr::Pi(_, bs, body) = chain {
        binders.extend(bs.iter().cloned());
        chain = strip_parens(body);
    }
    let Some((hyp_refs, concl)) = flatten_arrows(chain) else {
        return Err(format!(
            "a guarded premise mentioning `{short}` uses `∀` binders after \
             its first hypothesis arrow; only LEADING `∀` binders \
             (`∀ b⃗, H₁ → … → Hₙ → C`) are supported — a dependent \
             hypothesis telescope is refused rather than mis-lowered"
        ));
    };
    for (i, b) in binders.iter().enumerate() {
        check_clause_binder(b, &binders[..i], short, params, BinderSite::Guard)?;
    }
    // Strict positivity: a hypothesis is LEFT of an arrow — `P` there is a
    // negative occurrence, refused outright (including `P` nested anywhere
    // inside the hypothesis; `mentions` errs toward rejection).
    for h in &hyp_refs {
        if mentions(h, short) {
            return Err(format!(
                "a guarded premise mentions `{short}` in a hypothesis — \
                 LEFT of an arrow, a negative/non-strictly-positive \
                 occurrence; `{short}` may appear only in the guarded \
                 clause's final conclusion"
            ));
        }
    }
    let concl = classify_concl(
        concl,
        short,
        params,
        arity,
        binders.is_empty() && hyp_refs.is_empty(),
    )?;
    Ok(Premise::Guarded(GuardedPremise {
        binders,
        hyps: hyp_refs.into_iter().cloned().collect(),
        concl,
    }))
}

/// Classify the conclusion of a guarded clause (which mentions `P` — a
/// `P`-free conclusion makes the whole premise `P`-free, classified
/// [`Premise::Plain`] long before this point).
fn classify_concl(
    c: &SurfaceExpr,
    short: &str,
    params: &[String],
    arity: usize,
    premise_is_bare: bool,
) -> Result<GuardedConcl, String> {
    let c = strip_parens(c);
    if let Some(args) = rec_atom(c, short, params, arity)? {
        return Ok(GuardedConcl::Rec(args));
    }
    if let Some((binders, body)) = collect_exists(c)? {
        for (i, b) in binders.iter().enumerate() {
            check_clause_binder(b, &binders[..i], short, params, BinderSite::Exists)?;
        }
        let conjuncts = classify_ex_conjuncts(body, short, params, arity)?;
        // Defensive fail-closed: an all-Plain conjunction cannot reach here
        // (the premise would be `P`-free), but nothing below may rely on it.
        if !conjuncts.iter().any(|cj| matches!(cj, ExConjunct::Rec(_))) {
            return Err(format!(
                "the `∃`-conclusion of a guarded premise mentions `{short}` \
                 outside its conjuncts, which its positivity analysis does \
                 not cover"
            ));
        }
        return Ok(GuardedConcl::Exists { binders, conjuncts });
    }
    let subject = if premise_is_bare {
        "a premise"
    } else {
        "the conclusion of a guarded premise"
    };
    Err(format!(
        "{subject} mentions `{short}` but is neither the fully-applied \
         recursive atom `{short} e₁ … e{arity}` nor an `∃`-nest over a \
         conjunction of `{short}`-free propositions and recursive atoms; \
         its positivity is not established here, so it is refused rather \
         than mis-lowered"
    ))
}

/// Collect a (possibly nested) `∃` head: `Exists (fun y₁ => Exists (fun y₂
/// => … body))` — the exact desugaring of `∃ y₁ y₂ …, body`. Returns `None`
/// for a non-`∃` expression; a malformed `Exists` application (extra or
/// named arguments, a non-lambda or multi-binder-group predicate — shapes
/// the `∃` sugar never produces) is an error.
#[allow(clippy::type_complexity)]
fn collect_exists(e: &SurfaceExpr) -> Result<Option<(Vec<SurfaceBinder>, &SurfaceExpr)>, String> {
    let mut binders: Vec<SurfaceBinder> = Vec::new();
    let mut cur = e;
    while let SurfaceExpr::App(_, head, args) = cur {
        if !matches!(strip_parens(head), SurfaceExpr::Ident(_, id) if id == "Exists") {
            break;
        }
        if args.len() != 1 || args[0].name.is_some() {
            return Err("an `∃`-conclusion applies `Exists` outside the `∃ y, …` \
                 sugar (extra or named arguments); only the sugared form is \
                 analysed here"
                .to_string());
        }
        let SurfaceExpr::Lambda(_, bs, body) = strip_parens(&args[0].expr) else {
            return Err("an `∃`-conclusion applies `Exists` to a non-lambda \
                 predicate; only the `∃ y, …` sugar is analysed here"
                .to_string());
        };
        let [b] = bs.as_slice() else {
            return Err("an `∃`-conclusion applies `Exists` to a multi-binder \
                 lambda, which the `∃ y, …` sugar never produces"
                .to_string());
        };
        binders.push(b.clone());
        cur = strip_parens(body);
    }
    if binders.is_empty() {
        return Ok(None);
    }
    Ok(Some((binders, cur)))
}

/// Split the right-nested `∧` spine of an `∃`-conclusion body and classify
/// each conjunct: a recursive atom or a `P`-free proposition; anything else
/// refuses by name.
fn classify_ex_conjuncts(
    body: &SurfaceExpr,
    short: &str,
    params: &[String],
    arity: usize,
) -> Result<Vec<ExConjunct>, String> {
    let mut out = Vec::new();
    let mut cur = body;
    loop {
        if let SurfaceExpr::App(_, head, args) = cur {
            if matches!(strip_parens(head), SurfaceExpr::Ident(_, id) if id == "And")
                && args.len() == 2
                && args.iter().all(|a| a.name.is_none())
            {
                out.push(classify_ex_conjunct(&args[0].expr, short, params, arity)?);
                cur = strip_parens(&args[1].expr);
                continue;
            }
        }
        out.push(classify_ex_conjunct(cur, short, params, arity)?);
        return Ok(out);
    }
}

fn classify_ex_conjunct(
    e: &SurfaceExpr,
    short: &str,
    params: &[String],
    arity: usize,
) -> Result<ExConjunct, String> {
    let stripped = strip_parens(e);
    if let Some(args) = rec_atom(stripped, short, params, arity)? {
        return Ok(ExConjunct::Rec(args));
    }
    if !mentions(e, short) {
        return Ok(ExConjunct::Plain(e.clone()));
    }
    Err(format!(
        "a conjunct under the `∃`-conclusion of a guarded premise mentions \
         `{short}` but is not the fully-applied recursive atom \
         `{short} e₁ … e{arity}`; only `{short}`-free propositions and \
         recursive atoms may sit under the `∃`, so it is refused rather \
         than mis-lowered"
    ))
}

// ── the α-rename onto the shared index row ───────────────────────────────

impl GuardedPremise {
    /// Apply `validate`'s α-rename (constructor target variables → shared
    /// index row) component-wise, with the same fail-closed contract as
    /// [`target::rename_free`]: a guard or `∃` binder named after either
    /// side of the map would shadow/capture — refused with the same
    /// message shape.
    pub(super) fn renamed(&self, map: &[(String, String)]) -> Result<GuardedPremise, String> {
        let sub = |e: &SurfaceExpr| target::rename_free(e, map);
        let check = |bs: &[SurfaceBinder]| -> Result<(), String> {
            for b in bs {
                if map.iter().any(|(s, d)| *s == b.name || *d == b.name) {
                    return Err(format!(
                        "it binds `{}`, shadowing a variable of the α-rename \
                         onto the shared index row",
                        b.name
                    ));
                }
            }
            Ok(())
        };
        let sub_binders = |bs: &[SurfaceBinder]| -> Result<Vec<SurfaceBinder>, String> {
            check(bs)?;
            bs.iter()
                .map(|b| {
                    Ok(SurfaceBinder {
                        span: b.span,
                        name: b.name.clone(),
                        ty: match b.ty.as_deref() {
                            Some(t) => Some(Box::new(sub(t)?)),
                            None => None,
                        },
                        default: None,
                        info: b.info,
                    })
                })
                .collect()
        };
        let sub_all = |es: &[SurfaceExpr]| -> Result<Vec<SurfaceExpr>, String> {
            es.iter().map(&sub).collect()
        };
        Ok(GuardedPremise {
            binders: sub_binders(&self.binders)?,
            hyps: sub_all(&self.hyps)?,
            concl: match &self.concl {
                GuardedConcl::Rec(args) => GuardedConcl::Rec(sub_all(args)?),
                GuardedConcl::Exists { binders, conjuncts } => GuardedConcl::Exists {
                    binders: sub_binders(binders)?,
                    conjuncts: conjuncts
                        .iter()
                        .map(|c| {
                            Ok(match c {
                                ExConjunct::Rec(args) => ExConjunct::Rec(sub_all(args)?),
                                ExConjunct::Plain(e) => ExConjunct::Plain(sub(e)?),
                            })
                        })
                        .collect::<Result<Vec<_>, String>>()?,
                },
            },
        })
    }
}

// ── generation ───────────────────────────────────────────────────────────

impl ExConjunct {
    fn at_rel(&self, rel_head: &SurfaceExpr) -> SurfaceExpr {
        match self {
            ExConjunct::Rec(args) => generate::app(rel_head.clone(), args.clone()),
            ExConjunct::Plain(e) => e.clone(),
        }
    }
}

/// `∃ y⃗, body` — the parser's desugaring, rebuilt outermost-last.
fn exists_nest(binders: &[SurfaceBinder], body: SurfaceExpr) -> SurfaceExpr {
    binders.iter().rev().fold(body, |acc, b| {
        generate::napp(
            "Exists",
            vec![SurfaceExpr::Lambda(
                Span::dummy(),
                vec![b.clone()],
                Box::new(acc),
            )],
        )
    })
}

/// `hle e⃗ proof` — route one recursive atom through the `F_mono`
/// hypothesis.
fn le_map(args: &[SurfaceExpr], proof: SurfaceExpr) -> SurfaceExpr {
    let mut a = args.to_vec();
    a.push(proof);
    generate::napp(HYP_LE, a)
}

impl GuardedPremise {
    /// This premise as a functor-body conjunct, with the applied head
    /// `rel_head` at the conclusion's recursive atoms (the bare `R` inside
    /// the functor, the row-applied `P p⃗` at the declared premises); the
    /// guard (binders + hypotheses) is carried VERBATIM. At
    /// `rel_head := P p⃗` this is exactly the declared premise.
    pub(super) fn at_rel(&self, rel_head: &SurfaceExpr) -> SurfaceExpr {
        let concl = match &self.concl {
            GuardedConcl::Rec(args) => generate::app(rel_head.clone(), args.clone()),
            GuardedConcl::Exists { binders, conjuncts } => exists_nest(
                binders,
                generate::right_nest(
                    conjuncts.iter().map(|c| c.at_rel(rel_head)).collect(),
                    generate::and,
                ),
            ),
        };
        let chain = self
            .hyps
            .iter()
            .rev()
            .fold(concl, |acc, h| generate::arrow(h.clone(), acc));
        generate::forall_group(&self.binders, chain)
    }

    /// The `F_mono` image of this conjunct: re-abstract the guard, apply
    /// the `R`-side proof `h` under it, and map the conclusion —
    ///
    /// ```text
    /// fun b⃗ h⃗ => hle e⃗ (h b⃗ h⃗)                      (atom conclusion)
    /// fun b⃗ h⃗ => Exists.elim (h b⃗ h⃗) (fun y⃗ hex⃗ =>
    ///   Exists.intro y⃗ ⟨…, hle e⃗ hexᵢ, …⟩)           (∃ conclusion)
    /// ```
    ///
    /// — monotonicity of `∀`/`→`/`∃`/`∧` in the strictly-positive position.
    /// The `∃` nest is rebuilt with the SAME witnesses (sound: `∃` domains
    /// are `P`-free by the envelope). Hypothesis names carry the `_coind`
    /// marker, and guard/`∃` binder names may not, so re-abstraction cannot
    /// capture a generated name.
    ///
    /// MUTATION COVERAGE (measured 2026-08-26, both reverted):
    /// * guard re-abstraction dropped (return `mapped`, no `lam`): all
    ///   three guarded accept tests fail inside the CANDIDATE env —
    ///   `P.F_mono failed to elaborate/kernel-check (UnknownIdent q/r/x)`,
    ///   the declaration "REJECTED rather than partially registered";
    /// * `Exists.intro` re-nesting dropped (return `packed`): exactly the
    ///   ∃-conclusion test (`guarded_exists_wbisim`) fails — `WBisim.F_mono`
    ///   candidate kernel check, `TypeMismatch` with rigid-head `And` vs
    ///   `Exists` — while the ∃-free guarded tests stay green. Both nets
    ///   fire BEFORE anything registers.
    pub(super) fn mono_map(&self, h: SurfaceExpr) -> SurfaceExpr {
        let hyp_names: Vec<String> = (0..self.hyps.len())
            .map(|i| format!("{HYP_G_PREFIX}{i}"))
            .collect();
        let lam_refs: Vec<&str> = self
            .binders
            .iter()
            .map(|b| b.name.as_str())
            .chain(hyp_names.iter().map(String::as_str))
            .collect();
        let applied = generate::app(h, lam_refs.iter().map(|n| generate::ident(n)).collect());
        let mapped = match &self.concl {
            GuardedConcl::Rec(args) => le_map(args, applied),
            GuardedConcl::Exists { binders, conjuncts } => {
                let j = conjuncts.len();
                generate::exists_elim_nest(binders, applied, &|hc| {
                    let packed = generate::right_nest(
                        conjuncts
                            .iter()
                            .enumerate()
                            .map(|(c, cj)| {
                                let acc = generate::conjunct(hc.clone(), c, j);
                                match cj {
                                    ExConjunct::Rec(args) => le_map(args, acc),
                                    ExConjunct::Plain(_) => acc,
                                }
                            })
                            .collect(),
                        |a, b| generate::napp("And.intro", vec![a, b]),
                    );
                    binders.iter().rev().fold(packed, |acc, b| {
                        generate::napp("Exists.intro", vec![generate::ident(&b.name), acc])
                    })
                })
            }
        };
        generate::lam(&lam_refs, mapped)
    }
}
