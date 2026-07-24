// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! MAKE-IT-REAL — turn an ACTUAL `ty certify` verdict into a kernel-checked
//! Clean theorem (the source-fidelity step of the TY×Clean program; design
//! `designs/2026-06-20-ty-clean-unified-certifying-program.md` §4, §6 T·SEM,
//! §16.3).
//!
//! ## What this module does
//!
//! Given a real `ty.cert/v1` [`SafetyCertificate`] JSON (produced by
//! `ty certify`, e.g. on the `Accumulator` spec
//! `Init == x = 0`, `Next == x' = x + 1`, `Safety == x >= 0`), it:
//!
//! 1. **Deserializes** the certificate (vendored serde mirror of the fields we
//!    need: `spec_src`, `init`, `next`, `invariants`, `invariant_j_tla`,
//!    `var_sorts`, `ay_proof_obligations`). See [`TyCert`].
//! 2. **Re-encodes from `spec_src`** — NOT from any TY-lowered form. A small,
//!    self-contained tokenizer + recursive-descent parser
//!    ([`scalar`]) lifts the operator BODIES (`Init`/`Next`/`Safety`) straight
//!    out of the certificate's own spec text, and parses `invariant_j_tla` for
//!    `J`. So if you edit `spec_src`, the encoded predicates change — this is
//!    the source-fidelity discipline, made real (a [`test_source_fidelity`]
//!    asserts a perturbed `spec_src` yields a different `Init`).
//! 3. **Encodes** the parsed scalar fragment into CIC `Expr` over the
//!    [`crate::semantics`] model (`State := Nat`, `StatePred := State → Prop`,
//!    `Action := State → State → Prop`), reusing the semantics layer's
//!    `Nat`/`Eq`/`Nat.add`/`Nat.le` vocabulary.
//! 4. **Builds a kernel-checked `InductiveInvariantSound` instance** for THIS
//!    spec — `TY<Module>Safety : ∀ b, Runs Init Next b → Sat b (SemBox (Lift
//!    Safety))`, by applying the spec-generic keystone theorem
//!    [`crate::semantics::register_inductive_invariant_sound`] to the encoded
//!    `Init`/`Next`/`J`/`Safety` and the three obligation discharges.
//!
//! ## How the three obligations are discharged (HONEST accounting)
//!
//! The keystone takes three hypotheses: `Init⇒J`, `J∧Next⇒J'`, `J⇒Safety`.
//! We provide TWO products with DIFFERENT proof-depth:
//!
//! * [`register_ty_cert_safety_assumed`] — the obligations are **named
//!   Pi-hypotheses** (`hInit`/`hCons`/`hSafe`) on the resulting theorem. The
//!   `InductiveInvariantSound` *instance* (the induction over behaviours) is
//!   REAL and kernel-checked; the three VCs are honestly **trusted to AY's
//!   external Alethe re-check** (the cert carries strict-verified Alethe blobs;
//!   re-checking them in-kernel via clean-auto's Alethe→CIC LRA reconstruction
//!   is future work — see the proof-depth meter). Registers on a **bare**
//!   `Environment::new()`.
//!
//! * [`register_ty_cert_safety_closed`] — the obligations are **discharged
//!   constructively** for the `x >= 0` family: with `J s := Nat.le 0 s` over
//!   `State := Nat`, all three VCs hold by `Nat.zero_le` (`0 ≤ s` for every
//!   `Nat`). The result `TY<Module>SafetyClosed` is **fully closed and
//!   axiom-free** (`proof_quality == Constructive`). This needs `Nat.le` +
//!   `Nat.zero_le`, present on `Environment::with_prelude()`.
//!
//!   **LOUD semantic-fidelity row:** the closed discharge is honest *only*
//!   because we modelled the spec's `Int` variable as `Nat` (the keystone's
//!   fixed `State := Nat`). Over `Nat`, `x >= 0` is *trivially* true, so the
//!   safety content of THIS invariant is absorbed by the state model. That is
//!   sound for `Accumulator` (its reachable states are exactly the
//!   non-negatives) but it is an APPROXIMATION, surfaced by
//!   [`TyCert::fidelity_notes`], never hidden. A spec whose safety is NOT
//!   implied by non-negativity would need a richer `State` (roadmap: heterogeneous
//!   `State`, §16.5 corrections) and would NOT close this way — its obligations
//!   would stay Pi-bound (the `_assumed` product).
//!
//! Neither product adds any `Declaration::Axiom`; the axiom audit is unchanged.

use clean_kernel::env::{Declaration, EnvError, Environment};
use clean_kernel::expr::{BinderInfo, Expr};
use clean_kernel::level::Level;
use clean_kernel::name::Name;

use crate::semantics::{self, B};

// ════════════════════════════════════════════════════════════════════════════
// 1. Vendored certificate surface (serde mirror of ty.cert/v1)
// ════════════════════════════════════════════════════════════════════════════

/// One obligation's AY proof, as carried in the certificate. We keep only the
/// fields the Clean side reasons about; serde ignores the rest.
#[derive(Debug, Clone, serde::Deserialize)]
pub struct AyObligationProof {
    /// `"initiation"`, `"consecution"`, `"safety"`, or `"deadlock_freedom"`.
    pub name: String,
    /// Whether AY strict-checked the proof (`check_proof_strict` accepted it).
    #[serde(default)]
    pub strict_verified: bool,
    /// Rendered Alethe proof text (problem-scoped), for offline audit/re-check.
    #[serde(default)]
    pub alethe: String,
}

/// A vendored, READ-ONLY mirror of TY's `ty.cert/v1` `SafetyCertificate`
/// (`ty/crates/tla-check/src/cert.rs`). Only the fields the Clean re-encoder
/// uses are mirrored; unknown fields are ignored by serde.
#[derive(Debug, Clone, serde::Deserialize)]
pub struct TyCert {
    /// Schema tag (expected `ty.cert/v1`).
    pub schema: String,
    /// The verdict being certified (e.g. `inductive-safety-safe`).
    pub verdict: String,
    /// FULL spec source — we re-encode `Init`/`Next`/`Safety` from THIS.
    pub spec_src: String,
    /// `INIT` operator name.
    pub init: Option<String>,
    /// `NEXT` operator name.
    pub next: Option<String>,
    /// Configured safety invariants (operator names).
    #[serde(default)]
    pub invariants: Vec<String>,
    /// The proven inductive invariant `J`, as TLA+ text.
    pub invariant_j_tla: String,
    /// Inferred `(variable, sort)` signature.
    #[serde(default)]
    pub var_sorts: Vec<(String, String)>,
    /// Configured `CONSTANT` values (the cfg-bound constants, e.g.
    /// `MaxSeq = 6`). Absent on older 1-variable certs (serde default). The S4
    /// finite product ([`crate::finite`]) keys its enumeration on THESE values
    /// (certify exhaustively at the small bound), never on hardcoded defaults.
    #[serde(default)]
    pub constants: Vec<(String, i64)>,
    /// AY's own re-checkable proof for each obligation.
    #[serde(default)]
    pub ay_proof_obligations: Vec<AyObligationProof>,
}

impl TyCert {
    /// Parse a `ty.cert/v1` JSON blob.
    pub fn from_json(s: &str) -> Result<Self, String> {
        let c: TyCert = serde_json::from_str(s).map_err(|e| format!("cert parse: {e}"))?;
        if c.schema != "ty.cert/v1" {
            return Err(format!("unexpected schema {:?}", c.schema));
        }
        Ok(c)
    }

    /// The single state variable name (this brick handles 1-variable scalar
    /// specs). Errors if the signature is not exactly one variable.
    pub fn sole_var(&self) -> Result<&str, String> {
        match self.var_sorts.as_slice() {
            [(v, _)] => Ok(v.as_str()),
            other => Err(format!(
                "expected exactly one state variable, got {other:?}"
            )),
        }
    }

    /// The declared sort of the sole variable (e.g. `"Int"`).
    pub fn sole_sort(&self) -> Result<&str, String> {
        match self.var_sorts.as_slice() {
            [(_, s)] => Ok(s.as_str()),
            other => Err(format!(
                "expected exactly one state variable, got {other:?}"
            )),
        }
    }

    /// Whether every covered (non-structural) obligation was strict-verified by
    /// AY — the verdict's external acceptance basis (Leg D in the cert docs).
    pub fn all_obligations_ay_strict_verified(&self) -> bool {
        !self.ay_proof_obligations.is_empty()
            && self.ay_proof_obligations.iter().all(|o| o.strict_verified)
    }

    /// Honest semantic-fidelity notes for this certificate's Clean re-encoding.
    /// Returns the human-readable approximations that the kernel theorem does
    /// NOT capture (the "semantic-fidelity meter").
    pub fn fidelity_notes(&self) -> Vec<String> {
        let mut notes = Vec::new();
        if let Ok(sort) = self.sole_sort() {
            if sort == "Int" {
                notes.push(
                    "VAR x : Int is modelled as State := Nat (the keystone's fixed state \
                     type). SOUND for specs whose reachable states are non-negative \
                     (e.g. Accumulator); APPROXIMATE in general. Under Nat, `x >= 0` is \
                     trivially true, so this invariant's safety content is absorbed by \
                     the state model in the *closed* discharge."
                        .to_string(),
                );
            } else if sort != "Nat" {
                notes.push(format!(
                    "VAR sort {sort:?} modelled as Nat — fidelity unchecked for this sort."
                ));
            }
        }
        notes
    }
}

// ════════════════════════════════════════════════════════════════════════════
// 2. Source-fidelity scalar parser (tokenizer + recursive descent)
//
// A SELF-CONTAINED parser for the scalar arithmetic fragment of TLA+ that
// `ty certify` certifies (comparisons, +, =, /\, prime, identifiers, ints). It
// reads operator BODIES straight out of `spec_src`, so the encoding is driven
// by the certificate's own source text — the source-fidelity discipline.
// ════════════════════════════════════════════════════════════════════════════

/// The scalar fragment AST. Deliberately tiny: it covers exactly what a
/// 1-variable arithmetic safety spec (`Accumulator`-class) needs.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Scalar {
    /// Integer literal.
    Int(i64),
    /// A state variable read, `x`.
    Var(String),
    /// A primed variable read, `x'` (the next-state value).
    Prime(String),
    /// `a + b`.
    Add(Box<Scalar>, Box<Scalar>),
    /// `a = b` (equality on terms — used in Init/Next).
    Eq(Box<Scalar>, Box<Scalar>),
    /// `a >= b`.
    Ge(Box<Scalar>, Box<Scalar>),
    /// `a <= b`.
    Le(Box<Scalar>, Box<Scalar>),
    /// `a < b`.
    Lt(Box<Scalar>, Box<Scalar>),
    /// `a > b`.
    Gt(Box<Scalar>, Box<Scalar>),
    /// `a /\ b`.
    And(Box<Scalar>, Box<Scalar>),
}

mod lex {
    //! Self-contained tokenizer for the scalar fragment.

    #[derive(Debug, Clone, PartialEq, Eq)]
    pub enum Tok {
        Int(i64),
        Ident(String),
        Prime,  // '
        Plus,   // +
        Eq,     // =
        Ge,     // >=
        Le,     // <=
        Lt,     // <
        Gt,     // >
        And,    // /\
        LParen, // (
        RParen, // )
    }

    pub fn tokenize(s: &str) -> Result<Vec<Tok>, String> {
        let b = s.as_bytes();
        let mut i = 0;
        let mut out = Vec::new();
        while i < b.len() {
            let c = b[i];
            match c {
                _ if c.is_ascii_whitespace() => i += 1,
                b'+' => {
                    out.push(Tok::Plus);
                    i += 1;
                }
                b'\'' => {
                    out.push(Tok::Prime);
                    i += 1;
                }
                b'(' => {
                    out.push(Tok::LParen);
                    i += 1;
                }
                b')' => {
                    out.push(Tok::RParen);
                    i += 1;
                }
                b'=' => {
                    out.push(Tok::Eq);
                    i += 1;
                }
                b'>' => {
                    if i + 1 < b.len() && b[i + 1] == b'=' {
                        out.push(Tok::Ge);
                        i += 2;
                    } else {
                        out.push(Tok::Gt);
                        i += 1;
                    }
                }
                b'<' => {
                    if i + 1 < b.len() && b[i + 1] == b'=' {
                        out.push(Tok::Le);
                        i += 2;
                    } else {
                        out.push(Tok::Lt);
                        i += 1;
                    }
                }
                b'/' => {
                    if i + 1 < b.len() && b[i + 1] == b'\\' {
                        out.push(Tok::And);
                        i += 2;
                    } else {
                        return Err(format!("unexpected '/' at {i}"));
                    }
                }
                _ if c.is_ascii_digit() => {
                    let start = i;
                    while i < b.len() && b[i].is_ascii_digit() {
                        i += 1;
                    }
                    let n: i64 = s[start..i].parse().map_err(|e| format!("bad int: {e}"))?;
                    out.push(Tok::Int(n));
                }
                _ if c.is_ascii_alphabetic() || c == b'_' => {
                    let start = i;
                    while i < b.len() && (b[i].is_ascii_alphanumeric() || b[i] == b'_') {
                        i += 1;
                    }
                    out.push(Tok::Ident(s[start..i].to_string()));
                }
                _ => return Err(format!("unexpected char {:?} at {i}", c as char)),
            }
        }
        Ok(out)
    }
}

/// Parse the scalar fragment of a TLA+ expression. `vars` is the set of state
/// variables (so `x` becomes [`Scalar::Var`], a primed `x'` becomes
/// [`Scalar::Prime`]).
pub fn parse_scalar(src: &str) -> Result<Scalar, String> {
    let toks = lex::tokenize(src)?;
    let mut p = Parser {
        toks: &toks,
        pos: 0,
    };
    let e = p.parse_and()?;
    if p.pos != p.toks.len() {
        return Err(format!("trailing tokens after {:?}", e));
    }
    Ok(e)
}

struct Parser<'a> {
    toks: &'a [lex::Tok],
    pos: usize,
}

impl<'a> Parser<'a> {
    fn peek(&self) -> Option<&lex::Tok> {
        self.toks.get(self.pos)
    }
    fn bump(&mut self) -> Option<&lex::Tok> {
        let t = self.toks.get(self.pos);
        if t.is_some() {
            self.pos += 1;
        }
        t
    }

    /// `and := cmp ('/\' cmp)*`  (left-assoc).
    fn parse_and(&mut self) -> Result<Scalar, String> {
        let mut lhs = self.parse_cmp()?;
        while matches!(self.peek(), Some(lex::Tok::And)) {
            self.bump();
            let rhs = self.parse_cmp()?;
            lhs = Scalar::And(Box::new(lhs), Box::new(rhs));
        }
        Ok(lhs)
    }

    /// `cmp := add (relop add)?`  (non-chaining — TLA+ relops don't chain).
    fn parse_cmp(&mut self) -> Result<Scalar, String> {
        let lhs = self.parse_add()?;
        let op = match self.peek() {
            Some(lex::Tok::Eq) => Some(0),
            Some(lex::Tok::Ge) => Some(1),
            Some(lex::Tok::Le) => Some(2),
            Some(lex::Tok::Lt) => Some(3),
            Some(lex::Tok::Gt) => Some(4),
            _ => None,
        };
        match op {
            None => Ok(lhs),
            Some(k) => {
                self.bump();
                let rhs = self.parse_add()?;
                let (l, r) = (Box::new(lhs), Box::new(rhs));
                Ok(match k {
                    0 => Scalar::Eq(l, r),
                    1 => Scalar::Ge(l, r),
                    2 => Scalar::Le(l, r),
                    3 => Scalar::Lt(l, r),
                    _ => Scalar::Gt(l, r),
                })
            }
        }
    }

    /// `add := atom ('+' atom)*`  (left-assoc).
    fn parse_add(&mut self) -> Result<Scalar, String> {
        let mut lhs = self.parse_atom()?;
        while matches!(self.peek(), Some(lex::Tok::Plus)) {
            self.bump();
            let rhs = self.parse_atom()?;
            lhs = Scalar::Add(Box::new(lhs), Box::new(rhs));
        }
        Ok(lhs)
    }

    /// `atom := INT | IDENT "'"? | '(' and ')'`.
    fn parse_atom(&mut self) -> Result<Scalar, String> {
        match self.bump().cloned() {
            Some(lex::Tok::Int(n)) => Ok(Scalar::Int(n)),
            Some(lex::Tok::Ident(name)) => {
                if matches!(self.peek(), Some(lex::Tok::Prime)) {
                    self.bump();
                    Ok(Scalar::Prime(name))
                } else {
                    Ok(Scalar::Var(name))
                }
            }
            Some(lex::Tok::LParen) => {
                let e = self.parse_and()?;
                match self.bump() {
                    Some(lex::Tok::RParen) => Ok(e),
                    other => Err(format!("expected ')', got {other:?}")),
                }
            }
            other => Err(format!("expected atom, got {other:?}")),
        }
    }
}

/// Extract the BODY of operator `name` from a TLA+ module source, i.e. the text
/// after `name ==` up to end-of-line / next definition. This is the
/// source-fidelity entry point: it reads the spec's own text.
pub fn operator_body<'a>(spec_src: &'a str, name: &str) -> Result<&'a str, String> {
    for line in spec_src.lines() {
        let line = line.trim();
        // Match `name ==` (with the `==` separated by whitespace or directly).
        if let Some(rest) = line.strip_prefix(name) {
            let rest = rest.trim_start();
            if let Some(body) = rest.strip_prefix("==") {
                return Ok(body.trim());
            }
        }
    }
    Err(format!("operator {name:?} not found in spec_src"))
}

// ════════════════════════════════════════════════════════════════════════════
// 3. Encode the scalar fragment into CIC over `State := Nat`
// ════════════════════════════════════════════════════════════════════════════

fn c(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

/// `@Eq.{1} Nat a b`.
fn eq_nat(a: Expr, b: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [c("Nat"), a, b],
    )
}

/// `Nat.le a b`.
fn nat_le(a: Expr, b: Expr) -> Expr {
    Expr::apps(c("Nat.le"), [a, b])
}

/// `And p q`.
fn and(p: Expr, q: Expr) -> Expr {
    Expr::apps(c("And"), [p, q])
}

/// Encode a scalar TERM (`Int`/`Var`/`Prime`/`Add`) to a `Nat`-valued `Expr`,
/// given the de-Bruijn-free FVars for the current and next state variable
/// values (`cur`, `nxt`). A literal `n >= 0` becomes the `Nat` numeral;
/// `n < 0` is rejected (out of the `Nat` fragment).
fn encode_term(e: &Scalar, var: &str, cur: &Expr, nxt: &Expr) -> Result<Expr, String> {
    match e {
        Scalar::Int(n) => {
            if *n < 0 {
                return Err(format!("negative literal {n} out of Nat fragment"));
            }
            // Build the `Nat` numeral as iterated `Nat.succ` over `Nat.zero`.
            let mut acc = c("Nat.zero");
            for _ in 0..*n {
                acc = Expr::app(c("Nat.succ"), acc);
            }
            Ok(acc)
        }
        Scalar::Var(v) if v == var => Ok(cur.clone()),
        Scalar::Prime(v) if v == var => Ok(nxt.clone()),
        Scalar::Var(v) | Scalar::Prime(v) => {
            Err(format!("unknown variable {v:?} (sole var is {var:?})"))
        }
        Scalar::Add(a, b) => Ok(Expr::apps(
            c("Nat.add"),
            [
                encode_term(a, var, cur, nxt)?,
                encode_term(b, var, cur, nxt)?,
            ],
        )),
        other => Err(format!("not a scalar term: {other:?}")),
    }
}

/// Encode a scalar FORMULA (comparisons / conjunctions) to a `Prop`-valued
/// `Expr` over the given `cur`/`nxt` state-value FVars.
fn encode_formula(e: &Scalar, var: &str, cur: &Expr, nxt: &Expr) -> Result<Expr, String> {
    let term = |t: &Scalar| encode_term(t, var, cur, nxt);
    match e {
        Scalar::Eq(a, b) => Ok(eq_nat(term(a)?, term(b)?)),
        Scalar::Ge(a, b) => Ok(nat_le(term(b)?, term(a)?)), // a >= b  ≡  b ≤ a
        Scalar::Le(a, b) => Ok(nat_le(term(a)?, term(b)?)),
        Scalar::Lt(a, b) => Ok(nat_le(Expr::app(c("Nat.succ"), term(a)?), term(b)?)), // a < b ≡ succ a ≤ b
        Scalar::Gt(a, b) => Ok(nat_le(Expr::app(c("Nat.succ"), term(b)?), term(a)?)),
        Scalar::And(a, b) => Ok(and(
            encode_formula(a, var, cur, nxt)?,
            encode_formula(b, var, cur, nxt)?,
        )),
        other => Err(format!("not a scalar formula: {other:?}")),
    }
}

/// Encode a *state predicate* `P(x)` (no primes) into a `StatePred := Nat →
/// Prop` CIC term, abstracting the state variable into a `λ s`.
fn encode_state_pred(e: &Scalar, var: &str) -> Result<Expr, String> {
    let mut bld = B::new();
    let (s_id, s) = bld.fresh();
    let body = encode_formula(e, var, &s, &s /* no primes expected */)?;
    Ok(bld.lam(s_id, BinderInfo::Default, c("Nat"), body))
}

/// Encode an *action* `A(x, x')` (may use primes) into an `Action := Nat → Nat
/// → Prop` CIC term, abstracting current then next into `λ s s'`.
fn encode_action(e: &Scalar, var: &str) -> Result<Expr, String> {
    let mut bld = B::new();
    let (s_id, s) = bld.fresh();
    let (sp_id, sp) = bld.fresh();
    let body = encode_formula(e, var, &s, &sp)?;
    let inner = bld.lam(sp_id, BinderInfo::Default, c("Nat"), body);
    Ok(bld.lam(s_id, BinderInfo::Default, c("Nat"), inner))
}

/// The four encoded predicates for a certificate: `Init`/`Next`/`Safety`/`J`,
/// all over `State := Nat`. `Init`/`Safety`/`J` are `StatePred`; `Next` is an
/// `Action`.
pub struct Encoded {
    pub init: Expr,
    pub next: Expr,
    pub safety: Expr,
    pub j: Expr,
    /// The parsed `J` formula (for the closed discharge to recognise `x >= 0`).
    pub j_scalar: Scalar,
    pub var: String,
}

/// Re-encode the certificate's `Init`/`Next`/`Safety`/`J` FROM `spec_src`
/// (source-fidelity). The operator names come from the cert's `init`/`next`/
/// `invariants`; the bodies and `J` come from the spec text / `invariant_j_tla`.
pub fn encode_cert(cert: &TyCert) -> Result<Encoded, String> {
    let var = cert.sole_var()?.to_string();
    let init_name = cert.init.as_deref().ok_or("cert has no INIT")?;
    let next_name = cert.next.as_deref().ok_or("cert has no NEXT")?;
    let safety_name = cert
        .invariants
        .first()
        .map(String::as_str)
        .ok_or("cert has no INVARIANT")?;

    let init_body = operator_body(&cert.spec_src, init_name)?;
    let next_body = operator_body(&cert.spec_src, next_name)?;
    let safety_body = operator_body(&cert.spec_src, safety_name)?;

    let init_s = parse_scalar(init_body)?;
    let next_s = parse_scalar(next_body)?;
    let safety_s = parse_scalar(safety_body)?;
    let j_s = parse_scalar(&cert.invariant_j_tla)?;

    Ok(Encoded {
        init: encode_state_pred(&init_s, &var)?,
        next: encode_action(&next_s, &var)?,
        safety: encode_state_pred(&safety_s, &var)?,
        j: encode_state_pred(&j_s, &var)?,
        j_scalar: j_s,
        var,
    })
}

// ════════════════════════════════════════════════════════════════════════════
// 4. Build the kernel-checked InductiveInvariantSound instance
// ════════════════════════════════════════════════════════════════════════════

const INDUCTIVE_SOUND: &str = "TLAsem.InductiveInvariantSound";

/// `∀ s, Init s → J s` — the initiation VC type.
fn h_init_ty(init: &Expr, j: &Expr) -> Expr {
    let mut b = B::new();
    let (s_id, s) = b.fresh();
    let imp = Expr::arrow(
        Expr::app(init.clone(), s.clone()),
        Expr::app(j.clone(), s.clone()),
    );
    b.pi(s_id, BinderInfo::Default, c("Nat"), imp)
}

/// `∀ s s', J s → Next s s' → J s'` — the consecution VC type.
fn h_cons_ty(next: &Expr, j: &Expr) -> Expr {
    let mut b = B::new();
    let (s_id, s) = b.fresh();
    let (sp_id, sp) = b.fresh();
    let next_ss = Expr::apps(next.clone(), [s.clone(), sp.clone()]);
    let inner = Expr::arrow(
        Expr::app(j.clone(), s.clone()),
        Expr::arrow(next_ss, Expr::app(j.clone(), sp.clone())),
    );
    let inner = b.pi(sp_id, BinderInfo::Default, c("Nat"), inner);
    b.pi(s_id, BinderInfo::Default, c("Nat"), inner)
}

/// `∀ s, J s → Safety s` — the safety VC type.
fn h_safe_ty(j: &Expr, safety: &Expr) -> Expr {
    let mut b = B::new();
    let (s_id, s) = b.fresh();
    let imp = Expr::arrow(
        Expr::app(j.clone(), s.clone()),
        Expr::app(safety.clone(), s.clone()),
    );
    b.pi(s_id, BinderInfo::Default, c("Nat"), imp)
}

/// The conclusion `∀ b, Runs Init Next b → Sat b (SemBox (Lift Safety))`.
///
/// PUBLIC because it is the α-comparison anchor of the Certified gate: a
/// recheck must compare a fetched declaration's `type_` α-exactly against THIS
/// independently recomputed conclusion. That single check rejects (a) the
/// `_assumed` product (its type carries three extra leading Pi-hypotheses),
/// (b) a name-squatted declaration of any other statement, and (c) a
/// wrong-statement mint. `ProofQuality::Constructive` does NOT discriminate the
/// `_assumed` product (a lambda over named hypotheses is Constructive) — the
/// TYPE is the only sound discriminator.
pub fn conclusion_ty(init: &Expr, next: &Expr, safety: &Expr) -> Expr {
    let mut b = B::new();
    let (bvar_id, bvar) = b.fresh();
    let behavior_ty = Expr::arrow(c("Nat"), c("Nat"));
    let runs = Expr::apps(c("TLAsem.Runs"), [init.clone(), next.clone(), bvar.clone()]);
    let lift_safety = Expr::app(c("TLAsem.Lift"), safety.clone());
    let box_lift = Expr::app(c("TLAsem.SemBox"), lift_safety);
    let sat = Expr::apps(c("TLAsem.Sat"), [bvar.clone(), box_lift]);
    let imp = Expr::arrow(runs, sat);
    b.pi(bvar_id, BinderInfo::Default, behavior_ty, imp)
}

/// Run the finite lane's blessed-`TLAsem.*` integrity check, mapped into
/// [`EnvError`] for the `_assumed` product's signature. A mismatch surfaces as
/// [`EnvError::InitializationConflict`] on the squatted name.
fn verify_tlasem_or_env_error(env: &Environment) -> Result<(), EnvError> {
    crate::finite::verify_tlasem_integrity(env).map_err(|e| match e {
        crate::finite::FiniteError::VocabularySquatted { name } => {
            EnvError::InitializationConflict {
                name: Name::from_string(&name),
                detail: "blessed TLAsem vocabulary is bound to a DIFFERENT definition \
                         (name-squat); refusing to state a theorem against it"
                    .into(),
            }
        }
        other => EnvError::InitializationConflict {
            name: Name::from_string("TLAsem"),
            detail: format!("TLAsem integrity check failed: {other}"),
        },
    })
}

/// Apply the keystone `InductiveInvariantSound` to the encoded predicates and
/// three discharges; the result has type [`conclusion_ty`].
///
/// BINDER-ORDER NOTE (bug fixed 2026-07-19): the keystone's implicit telescope
/// is `{Init} {Next} {Safety} {J}` (outermost→innermost — see the `pi` wrap
/// order in `semantics::register_inductive_invariant_sound`), so the explicit
/// application order is `init, next, SAFETY, J`. The previous code applied
/// `j` before `safety`; the swap was invisible on the Accumulator fixture
/// because there `J ≡ Safety` (both `x >= 0`), and it FAILED CLOSED (kernel
/// type error, never a wrong theorem) on any cert with `J ≠ Safety`.
fn instance_proof(enc: &Encoded, h_init: Expr, h_cons: Expr, h_safe: Expr) -> Expr {
    Expr::apps(
        c(INDUCTIVE_SOUND),
        [
            enc.init.clone(),
            enc.next.clone(),
            enc.safety.clone(),
            enc.j.clone(),
            h_init,
            h_cons,
            h_safe,
        ],
    )
}

/// Register the **`_assumed`** product: the `InductiveInvariantSound` instance
/// with the three obligations as NAMED Pi-hypotheses. Registers on a bare
/// `Environment::new()` (only `Nat`/`Eq`/`And`/`Nat.le` needed — `Nat.le` is
/// brought in by `init_le`).
///
/// Theorem type:
/// ```text
/// TY<Module>Safety :
///   (∀ s, Init s → J s) →
///   (∀ s s', J s → Next s s' → J s') →
///   (∀ s, J s → Safety s) →
///   ∀ b, Runs Init Next b → Sat b (SemBox (Lift Safety))
/// ```
/// where `Init`/`Next`/`Safety`/`J` are the CONCRETE encodings of THIS spec.
pub fn register_ty_cert_safety_assumed(
    env: &mut Environment,
    thm_name: &str,
    enc: &Encoded,
) -> Result<(), EnvError> {
    semantics::register_inductive_invariant_sound(env)?;
    // TLAsem INTEGRITY (defense-in-depth): the registration above is
    // idempotent (skip-if-exists), so on an adversarially pre-populated env a
    // squatted `TLAsem.Runs`/`Sat`/keystone would change the MEANING of the
    // statement below while still α-matching `conclusion_ty` (constants
    // compare by NAME). Verify the vocabulary against the freshly rebuilt
    // blessed module — the same check the finite lane runs.
    verify_tlasem_or_env_error(env)?;
    // `Nat.le` lives behind `init_le` (the `LE` machinery). `init_le` is `pub`.
    env.init_le().ok();

    // NAME-SQUAT HARDENING (blueprint S4): a pre-existing declaration under
    // this name is an ERROR, never a silent skip. The old skip-if-exists let a
    // squatter pre-register ANY statement under the product name and have this
    // call rubber-stamp it with `Ok(())`.
    let name = Name::from_string(thm_name);
    if env.get_const(&name).is_some() {
        return Err(EnvError::DuplicateName(name));
    }

    let h_init_t = h_init_ty(&enc.init, &enc.j);
    let h_cons_t = h_cons_ty(&enc.next, &enc.j);
    let h_safe_t = h_safe_ty(&enc.j, &enc.safety);
    let concl = conclusion_ty(&enc.init, &enc.next, &enc.safety);

    // type := hInit → hCons → hSafe → concl
    let mut tb = B::new();
    let (hi_id, _hi) = tb.fresh();
    let (hc_id, _hc) = tb.fresh();
    let (hs_id, _hs) = tb.fresh();
    let mut ty = concl.clone();
    ty = tb.pi(hs_id, BinderInfo::Default, h_safe_t.clone(), ty);
    ty = tb.pi(hc_id, BinderInfo::Default, h_cons_t.clone(), ty);
    ty = tb.pi(hi_id, BinderInfo::Default, h_init_t.clone(), ty);
    let ty = tb.finish(ty);

    // value := λ hInit hCons hSafe, InductiveInvariantSound init next j safety hInit hCons hSafe
    let mut vb = B::new();
    let (vhi_id, vhi) = vb.fresh();
    let (vhc_id, vhc) = vb.fresh();
    let (vhs_id, vhs) = vb.fresh();
    let body = instance_proof(enc, vhi, vhc, vhs);
    let mut v = vb.lam(vhs_id, BinderInfo::Default, h_safe_t, body);
    v = vb.lam(vhc_id, BinderInfo::Default, h_cons_t, v);
    v = vb.lam(vhi_id, BinderInfo::Default, h_init_t, v);
    let v = vb.finish(v);

    env.add_decl(Declaration::Theorem {
        name,
        level_params: vec![],
        type_: ty,
        value: v,
    })
}

/// Register the **`_closed`** product: a FULLY CLOSED, axiom-free theorem for
/// the `x >= 0`-family invariant, discharging the three obligations
/// constructively over `State := Nat` via `Nat.zero_le`.
///
/// Requires `Nat.le` + `Nat.zero_le : ∀ n, Nat.le Nat.zero n` (present on
/// `Environment::with_prelude()`). Errors (does NOT register) if `J` is not the
/// recognised `var >= 0` shape — so the closed product is offered ONLY when the
/// `Nat` model makes it honest.
///
/// Theorem type (no hypotheses left):
/// ```text
/// TY<Module>SafetyClosed :
///   ∀ b, Runs Init Next b → Sat b (SemBox (Lift Safety))
/// ```
pub fn register_ty_cert_safety_closed(
    env: &mut Environment,
    thm_name: &str,
    enc: &Encoded,
) -> Result<(), String> {
    // Recognise `J == (var >= 0)`  (i.e. `Scalar::Ge(Var var, Int 0)`).
    match &enc.j_scalar {
        Scalar::Ge(l, r)
            if matches!(&**l, Scalar::Var(v) if *v == enc.var)
                && matches!(&**r, Scalar::Int(0)) => {}
        other => {
            return Err(format!(
                "closed discharge only handles `{} >= 0`-shaped J; got {:?}",
                enc.var, other
            ))
        }
    }
    if env.get_const(&Name::from_string("Nat.zero_le")).is_none() {
        return Err("Nat.zero_le not in env (build with Environment::with_prelude())".into());
    }

    semantics::register_inductive_invariant_sound(env).map_err(|e| format!("{e:?}"))?;
    // TLAsem INTEGRITY — see `register_ty_cert_safety_assumed`.
    crate::finite::verify_tlasem_integrity(env).map_err(|e| format!("TLAsem integrity: {e}"))?;

    // NAME-SQUAT HARDENING (blueprint S4): error on collision, never skip —
    // see `register_ty_cert_safety_assumed`.
    let name = Name::from_string(thm_name);
    if env.get_const(&name).is_some() {
        return Err(format!(
            "name collision: {name} already declared (refusing to skip)"
        ));
    }

    // `Nat.zero_le : ∀ (n : Nat), Nat.le Nat.zero n`.
    let zero_le = c("Nat.zero_le");

    // hSafe : ∀ s, J s → Safety s. Here J ≡ Safety (both `var >= 0`), so the
    // discharge is the identity — but we build it generically as
    //   λ s (h : J s), h     (relies on J and Safety being def-eq, which they
    //                          are: both encode `Nat.le 0 s`).
    let h_safe = {
        let mut b = B::new();
        let (s_id, s) = b.fresh();
        let (h_id, h) = b.fresh();
        let j_s = Expr::app(enc.j.clone(), s.clone());
        let inner = b.lam(h_id, BinderInfo::Default, j_s, h);
        b.finish(b.lam(s_id, BinderInfo::Default, c("Nat"), inner))
    };

    // hInit : ∀ s, Init s → J s.  J s ≡ Nat.le 0 s, so `λ s _, Nat.zero_le s`.
    let h_init = {
        let mut b = B::new();
        let (s_id, s) = b.fresh();
        let (h_id, _h) = b.fresh();
        let init_s = Expr::app(enc.init.clone(), s.clone());
        let proof = Expr::app(zero_le.clone(), s.clone());
        let inner = b.lam(h_id, BinderInfo::Default, init_s, proof);
        b.finish(b.lam(s_id, BinderInfo::Default, c("Nat"), inner))
    };

    // hCons : ∀ s s', J s → Next s s' → J s'.  J s' ≡ Nat.le 0 s', so
    //   λ s s' _ _, Nat.zero_le s'.
    let h_cons = {
        let mut b = B::new();
        let (s_id, s) = b.fresh();
        let (sp_id, sp) = b.fresh();
        let (hj_id, _hj) = b.fresh();
        let (hn_id, _hn) = b.fresh();
        let j_s = Expr::app(enc.j.clone(), s.clone());
        let next_ss = Expr::apps(enc.next.clone(), [s.clone(), sp.clone()]);
        let proof = Expr::app(zero_le.clone(), sp.clone());
        let l4 = b.lam(hn_id, BinderInfo::Default, next_ss, proof);
        let l3 = b.lam(hj_id, BinderInfo::Default, j_s, l4);
        let l2 = b.lam(sp_id, BinderInfo::Default, c("Nat"), l3);
        b.finish(b.lam(s_id, BinderInfo::Default, c("Nat"), l2))
    };

    let value = instance_proof(enc, h_init, h_cons, h_safe);
    let ty = conclusion_ty(&enc.init, &enc.next, &enc.safety);

    env.add_decl(Declaration::Theorem {
        name,
        level_params: vec![],
        type_: ty,
        value,
    })
    .map_err(|e| format!("{e:?}"))
}

// ════════════════════════════════════════════════════════════════════════════
// Unit tests — the parser, the encoder, and the kernel-accepted instances
// ════════════════════════════════════════════════════════════════════════════

#[cfg(test)]
mod tests {
    use super::*;

    const ACC_SRC: &str = "---- MODULE Accumulator ----\n\
                           EXTENDS Integers\n\
                           VARIABLE x\n\
                           Init == x = 0\n\
                           Next == x' = x + 1\n\
                           Safety == x >= 0\n\
                           ====\n";

    fn acc_cert() -> TyCert {
        TyCert {
            schema: "ty.cert/v1".into(),
            verdict: "inductive-safety-safe".into(),
            spec_src: ACC_SRC.into(),
            init: Some("Init".into()),
            next: Some("Next".into()),
            invariants: vec!["Safety".into()],
            invariant_j_tla: "x >= 0".into(),
            var_sorts: vec![("x".into(), "Int".into())],
            constants: vec![],
            ay_proof_obligations: vec![],
        }
    }

    #[test]
    fn parser_handles_the_accumulator_fragment() {
        assert_eq!(
            parse_scalar("x = 0").unwrap(),
            Scalar::Eq(Box::new(Scalar::Var("x".into())), Box::new(Scalar::Int(0)))
        );
        assert_eq!(
            parse_scalar("x' = x + 1").unwrap(),
            Scalar::Eq(
                Box::new(Scalar::Prime("x".into())),
                Box::new(Scalar::Add(
                    Box::new(Scalar::Var("x".into())),
                    Box::new(Scalar::Int(1))
                ))
            )
        );
        assert_eq!(
            parse_scalar("x >= 0").unwrap(),
            Scalar::Ge(Box::new(Scalar::Var("x".into())), Box::new(Scalar::Int(0)))
        );
        // conjunction + precedence
        assert_eq!(
            parse_scalar("x < 5 /\\ x' = x + 1").unwrap(),
            Scalar::And(
                Box::new(Scalar::Lt(
                    Box::new(Scalar::Var("x".into())),
                    Box::new(Scalar::Int(5))
                )),
                Box::new(Scalar::Eq(
                    Box::new(Scalar::Prime("x".into())),
                    Box::new(Scalar::Add(
                        Box::new(Scalar::Var("x".into())),
                        Box::new(Scalar::Int(1))
                    ))
                ))
            )
        );
    }

    #[test]
    fn operator_body_reads_spec_src() {
        assert_eq!(operator_body(ACC_SRC, "Init").unwrap(), "x = 0");
        assert_eq!(operator_body(ACC_SRC, "Next").unwrap(), "x' = x + 1");
        assert_eq!(operator_body(ACC_SRC, "Safety").unwrap(), "x >= 0");
        assert!(operator_body(ACC_SRC, "Nope").is_err());
    }

    #[test]
    fn encode_cert_succeeds_and_is_source_driven() {
        let cert = acc_cert();
        let enc = encode_cert(&cert).expect("encode");
        assert_eq!(enc.var, "x");
        // J is the recognised `x >= 0` shape.
        assert!(matches!(&enc.j_scalar, Scalar::Ge(..)));

        // Source-fidelity: perturb the Next body.
        let mut c2 = cert.clone();
        c2.spec_src = c2.spec_src.replace("x' = x + 1", "x' = x + 2");
        let enc2 = encode_cert(&c2).expect("encode perturbed");
        assert_ne!(format!("{:?}", enc.next), format!("{:?}", enc2.next));
    }

    #[test]
    fn assumed_instance_kernel_checks_on_bare_env() {
        let enc = encode_cert(&acc_cert()).expect("encode");
        let mut env = Environment::new();
        register_ty_cert_safety_assumed(&mut env, "TYAccSafety_unit", &enc)
            .expect("assumed instance registers + kernel-checks");
        assert!(env
            .get_const(&Name::from_string("TYAccSafety_unit"))
            .is_some());
        // NAME-SQUAT HARDENING: re-registration under an existing name is an
        // ERROR (the old silent skip was the squat vector — blueprint S4).
        let again = register_ty_cert_safety_assumed(&mut env, "TYAccSafety_unit", &enc);
        assert!(
            matches!(again, Err(EnvError::DuplicateName(_))),
            "collision must error, not silently skip: {again:?}"
        );
    }

    #[test]
    fn closed_registration_errors_on_name_collision() {
        // Pre-squat the name with an unrelated declaration; the closed product
        // must ERROR instead of silently accepting the squatted declaration.
        let enc = encode_cert(&acc_cert()).expect("encode");
        let mut env = Environment::with_prelude();
        register_ty_cert_safety_closed(&mut env, "TYAccSquatTarget", &enc)
            .expect("first registration succeeds");
        let again = register_ty_cert_safety_closed(&mut env, "TYAccSquatTarget", &enc);
        assert!(
            again.is_err(),
            "collision must error, not silently skip: {again:?}"
        );
    }

    #[test]
    fn assumed_registers_when_j_differs_from_safety() {
        // Regression for the keystone binder-order fix: the keystone telescope
        // is {Init}{Next}{Safety}{J}. With J ≠ Safety (here Safety is a
        // CONJUNCTION while J is a bare `x >= 0`) the old `j`-before-`safety`
        // application failed the kernel type-check; the fixed order registers.
        let mut cert = acc_cert();
        cert.spec_src = cert
            .spec_src
            .replace("Safety == x >= 0", "Safety == x >= 0 /\\ x >= 0");
        let enc = encode_cert(&cert).expect("encode");
        assert_ne!(
            format!("{:?}", enc.j),
            format!("{:?}", enc.safety),
            "test premise: J and Safety must be distinct encodings"
        );
        let mut env = Environment::new();
        register_ty_cert_safety_assumed(&mut env, "TYAccSafety_jneq", &enc)
            .expect("assumed instance must register when J differs from Safety");
    }

    #[test]
    fn closed_discharge_refuses_non_geq_zero_j() {
        // If J is not `x >= 0`-shaped, the closed product must REFUSE (sound:
        // it does not claim a discharge it cannot honestly make over Nat).
        let mut cert = acc_cert();
        cert.invariant_j_tla = "x <= 5".into();
        let enc = encode_cert(&cert).expect("encode");
        let mut env = Environment::with_prelude();
        let r = register_ty_cert_safety_closed(&mut env, "TYAccSafety_bad", &enc);
        assert!(r.is_err(), "closed discharge must refuse non-(>=0) J");
        assert!(env
            .get_const(&Name::from_string("TYAccSafety_bad"))
            .is_none());
    }

    #[test]
    fn assumed_and_closed_refuse_squatted_tlasem_keystone() {
        // The 1-variable products build on the IDEMPOTENT TLAsem registration
        // (skip-if-exists), so a pre-squatted keystone under the blessed NAME
        // would change the MEANING of the registered statement while still
        // α-matching `conclusion_ty`. Both products must refuse via the same
        // integrity check the finite lane runs.
        let enc = encode_cert(&acc_cert()).expect("encode");
        let mut env = Environment::with_prelude();
        let nat_c = c("Nat");
        let zero = Expr::nat_lit(0);
        let eq00 = Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
            [nat_c.clone(), zero.clone(), zero.clone()],
        );
        env.add_decl(Declaration::Theorem {
            name: Name::from_string("TLAsem.InductiveInvariantSound"),
            level_params: vec![],
            type_: eq00,
            value: Expr::apps(
                Expr::const_(
                    Name::from_string("Eq.refl"),
                    vec![Level::succ(Level::zero())],
                ),
                [nat_c, zero],
            ),
        })
        .expect("squatted keystone registers as a plain theorem");

        let mut env_a = env.clone();
        let r = register_ty_cert_safety_assumed(&mut env_a, "TYSquatAssumed", &enc);
        assert!(
            matches!(r, Err(EnvError::InitializationConflict { .. })),
            "assumed must refuse a squatted keystone: {r:?}"
        );
        assert!(env_a
            .get_const(&Name::from_string("TYSquatAssumed"))
            .is_none());

        let r2 = register_ty_cert_safety_closed(&mut env, "TYSquatClosed", &enc);
        assert!(
            r2.is_err(),
            "closed must refuse a squatted keystone: {r2:?}"
        );
        assert!(env.get_const(&Name::from_string("TYSquatClosed")).is_none());
    }

    #[test]
    fn negative_literal_is_rejected() {
        // The Nat fragment cannot represent negative literals; encoding must
        // FAIL CLOSED rather than silently misencode (soundness).
        let s = c("Nat.zero");
        assert!(
            encode_term(&Scalar::Int(-1), "x", &s, &s).is_err(),
            "a negative literal is outside the Nat fragment and must be rejected"
        );
    }
}
