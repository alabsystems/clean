// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tokenizer + recursive-descent parser for the S4 finite fragment of TLA+.
//!
//! Grammar (blueprint S4 / surface_grammar item 3): quantifier-free arith/bool
//! formulas plus `∀` over explicit finite `a..b` domains, IF-THEN-ELSE terms,
//! function-valued comprehension / `EXCEPT` / access for `Fin n → Bool`
//! (Tier-0) state fields, `UNCHANGED`, and primed assignments. Multi-line,
//! bullet-listed operator bodies (`/\`-prefixed continuation lines — the exact
//! `trust_model!` emission shape) are supported by [`operator_table`], which
//! preserves TLA+ bullet-list grouping by parenthesizing each item; ambiguous
//! unparenthesized `/\`–`\/` mixing is refused by [`parse_fragment`].
//!
//! This parser is SOURCE-FIDELITY infrastructure: it reads operator bodies
//! straight out of the certificate's own `spec_src`, so perturbing the spec
//! text changes the parsed machine (asserted by the battery).

/// The finite-fragment AST. Untyped at parse time; [`crate::finite::machine`]
/// type-checks against the variable manifest during evaluation/compilation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Tx {
    /// Integer literal (non-negative in the fragment; negativity fails closed
    /// downstream).
    Num(i64),
    /// `TRUE` / `FALSE`.
    BoolLit(bool),
    /// Identifier: state variable, `CONSTANT`, operator reference, or bound
    /// binder variable — resolved downstream.
    Ident(String),
    /// Primed read `v'` (next-state value; only legal as an update LHS).
    Prime(String),
    /// `a + b`.
    Add(Box<Tx>, Box<Tx>),
    /// `a - b` (TLA+ Int minus; Nat-truncation divergence fails closed).
    Sub(Box<Tx>, Box<Tx>),
    /// `IF c THEN a ELSE b`.
    Ite(Box<Tx>, Box<Tx>, Box<Tx>),
    /// `a = b`.
    Eq(Box<Tx>, Box<Tx>),
    /// `a # b` (inequality).
    Neq(Box<Tx>, Box<Tx>),
    /// `a <= b` (also spelled `=<`).
    Le(Box<Tx>, Box<Tx>),
    /// `a < b`.
    Lt(Box<Tx>, Box<Tx>),
    /// `a >= b`.
    Ge(Box<Tx>, Box<Tx>),
    /// `a > b`.
    Gt(Box<Tx>, Box<Tx>),
    /// `a /\ b`.
    And(Box<Tx>, Box<Tx>),
    /// `a \/ b`.
    Or(Box<Tx>, Box<Tx>),
    /// `~a`.
    Not(Box<Tx>),
    /// `a <=> b`.
    Iff(Box<Tx>, Box<Tx>),
    /// `f[e]` — function-variable access.
    FnAccess(String, Box<Tx>),
    /// `[x \in lo..hi |-> body]` — function comprehension.
    Comprehension {
        /// Bound variable name.
        binder: String,
        /// Domain lower bound (constant expression).
        lo: Box<Tx>,
        /// Domain upper bound (constant expression).
        hi: Box<Tx>,
        /// Per-index body (may read `binder`).
        body: Box<Tx>,
    },
    /// `[f EXCEPT ![i] = v]` — pointwise function update.
    Except {
        /// The function variable being updated.
        base: String,
        /// Updated index (arbitrary arithmetic expression).
        index: Box<Tx>,
        /// New value at the index.
        value: Box<Tx>,
    },
    /// `\A x \in lo..hi : body` — bounded universal quantifier.
    Forall {
        /// Bound variable name.
        binder: String,
        /// Domain lower bound (constant expression).
        lo: Box<Tx>,
        /// Domain upper bound (constant expression).
        hi: Box<Tx>,
        /// Quantified body.
        body: Box<Tx>,
    },
    /// `UNCHANGED <<a, b>>` / `UNCHANGED a`.
    Unchanged(Vec<String>),
}

impl Tx {
    /// Whether any primed read occurs anywhere in this expression.
    pub fn has_prime(&self) -> bool {
        match self {
            Tx::Prime(_) => true,
            Tx::Num(_) | Tx::BoolLit(_) | Tx::Ident(_) | Tx::Unchanged(_) => false,
            Tx::Add(a, b)
            | Tx::Sub(a, b)
            | Tx::Eq(a, b)
            | Tx::Neq(a, b)
            | Tx::Le(a, b)
            | Tx::Lt(a, b)
            | Tx::Ge(a, b)
            | Tx::Gt(a, b)
            | Tx::And(a, b)
            | Tx::Or(a, b)
            | Tx::Iff(a, b) => a.has_prime() || b.has_prime(),
            Tx::Not(a) => a.has_prime(),
            Tx::Ite(c, t, e) => c.has_prime() || t.has_prime() || e.has_prime(),
            Tx::FnAccess(_, i) => i.has_prime(),
            Tx::Comprehension { lo, hi, body, .. } | Tx::Forall { lo, hi, body, .. } => {
                lo.has_prime() || hi.has_prime() || body.has_prime()
            }
            Tx::Except { index, value, .. } => index.has_prime() || value.has_prime(),
        }
    }

    /// Split a top-level right-or-left-nested conjunction into its conjuncts.
    pub fn split_and(&self) -> Vec<&Tx> {
        match self {
            Tx::And(a, b) => {
                let mut v = a.split_and();
                v.extend(b.split_and());
                v
            }
            other => vec![other],
        }
    }

    /// Split a top-level disjunction into its disjuncts.
    pub fn split_or(&self) -> Vec<&Tx> {
        match self {
            Tx::Or(a, b) => {
                let mut v = a.split_or();
                v.extend(b.split_or());
                v
            }
            other => vec![other],
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum Tok {
    Num(i64),
    Ident(String),
    KwIf,
    KwThen,
    KwElse,
    KwTrue,
    KwFalse,
    KwUnchanged,
    KwExcept,
    Plus,
    Minus,
    Prime,
    Eq,
    Neq,
    Le,
    Lt,
    Ge,
    Gt,
    Iff,
    And,
    Or,
    Not,
    LPar,
    RPar,
    LBrack,
    RBrack,
    LTup,
    RTup,
    Comma,
    Colon,
    Bang,
    DotDot,
    MapsTo,
    Forall,
    In,
}

fn tokenize(s: &str) -> Result<Vec<Tok>, String> {
    let b = s.as_bytes();
    let mut i = 0;
    let mut out = Vec::new();
    while i < b.len() {
        let rest = &s[i..];
        let c = b[i];
        if c.is_ascii_whitespace() {
            i += 1;
            continue;
        }
        // Multi-char operators, longest first.
        if rest.starts_with("<=>") {
            out.push(Tok::Iff);
            i += 3;
            continue;
        }
        if rest.starts_with("|->") {
            out.push(Tok::MapsTo);
            i += 3;
            continue;
        }
        if rest.starts_with("<<") {
            out.push(Tok::LTup);
            i += 2;
            continue;
        }
        if rest.starts_with(">>") {
            out.push(Tok::RTup);
            i += 2;
            continue;
        }
        if rest.starts_with("<=") || rest.starts_with("=<") {
            out.push(Tok::Le);
            i += 2;
            continue;
        }
        if rest.starts_with(">=") {
            out.push(Tok::Ge);
            i += 2;
            continue;
        }
        if rest.starts_with("..") {
            out.push(Tok::DotDot);
            i += 2;
            continue;
        }
        if rest.starts_with("/\\") {
            out.push(Tok::And);
            i += 2;
            continue;
        }
        if rest.starts_with("\\/") {
            out.push(Tok::Or);
            i += 2;
            continue;
        }
        if c == b'\\' {
            // Backslash keyword: \A, \in.
            let start = i + 1;
            let mut j = start;
            while j < b.len() && b[j].is_ascii_alphabetic() {
                j += 1;
            }
            match &s[start..j] {
                "A" => out.push(Tok::Forall),
                "in" => out.push(Tok::In),
                kw => return Err(format!("unknown backslash keyword \\{kw}")),
            }
            i = j;
            continue;
        }
        match c {
            b'+' => {
                out.push(Tok::Plus);
                i += 1;
            }
            b'-' => {
                out.push(Tok::Minus);
                i += 1;
            }
            b'\'' => {
                out.push(Tok::Prime);
                i += 1;
            }
            b'=' => {
                out.push(Tok::Eq);
                i += 1;
            }
            b'#' => {
                out.push(Tok::Neq);
                i += 1;
            }
            b'<' => {
                out.push(Tok::Lt);
                i += 1;
            }
            b'>' => {
                out.push(Tok::Gt);
                i += 1;
            }
            b'~' => {
                out.push(Tok::Not);
                i += 1;
            }
            b'(' => {
                out.push(Tok::LPar);
                i += 1;
            }
            b')' => {
                out.push(Tok::RPar);
                i += 1;
            }
            b'[' => {
                out.push(Tok::LBrack);
                i += 1;
            }
            b']' => {
                out.push(Tok::RBrack);
                i += 1;
            }
            b',' => {
                out.push(Tok::Comma);
                i += 1;
            }
            b':' => {
                out.push(Tok::Colon);
                i += 1;
            }
            b'!' => {
                out.push(Tok::Bang);
                i += 1;
            }
            _ if c.is_ascii_digit() => {
                let start = i;
                while i < b.len() && b[i].is_ascii_digit() {
                    i += 1;
                }
                let n: i64 = s[start..i]
                    .parse()
                    .map_err(|e| format!("bad integer literal: {e}"))?;
                out.push(Tok::Num(n));
            }
            _ if c.is_ascii_alphabetic() || c == b'_' => {
                let start = i;
                while i < b.len() && (b[i].is_ascii_alphanumeric() || b[i] == b'_') {
                    i += 1;
                }
                out.push(match &s[start..i] {
                    "IF" => Tok::KwIf,
                    "THEN" => Tok::KwThen,
                    "ELSE" => Tok::KwElse,
                    "TRUE" => Tok::KwTrue,
                    "FALSE" => Tok::KwFalse,
                    "UNCHANGED" => Tok::KwUnchanged,
                    "EXCEPT" => Tok::KwExcept,
                    id => Tok::Ident(id.to_string()),
                });
            }
            _ => return Err(format!("unexpected character {:?} at byte {i}", c as char)),
        }
    }
    Ok(out)
}

/// Parse one finite-fragment expression. Tolerates a single LEADING `/\` or
/// `\/` bullet (a one-item bullet list on a single source line).
///
/// FAIL-CLOSED GUARD: an unparenthesized top-level mix of `/\` and `\/` is
/// refused. TLA+ gives conjunction and disjunction CONFLICTING precedence
/// (SANY rejects the unparenthesized mix outright), so any such token stream
/// reaching this parser is not legal single-line TLA+ — it can only arise
/// from text mangling (e.g. naive line-joining of a bullet list), and parsing
/// it with this grammar's fixed precedence would silently REGROUP the spec: a
/// false-accept vector against `spec_src`.
pub fn parse_fragment(src: &str) -> Result<Tx, String> {
    let toks = tokenize(src)?;
    let start = usize::from(matches!(toks.first(), Some(Tok::And | Tok::Or)));
    check_no_mixed_toplevel(&toks[start..])?;
    let mut p = P {
        toks: &toks,
        pos: start,
    };
    let e = p.expr()?;
    if p.pos != p.toks.len() {
        return Err(format!(
            "trailing tokens after expression: {:?}",
            &p.toks[p.pos..]
        ));
    }
    Ok(e)
}

/// Refuse SANY-illegal unparenthesized `/\`–`\/` mixing at the top level.
/// Delimited contexts do not count: parentheses, brackets, tuples, and the
/// `IF … THEN … ELSE` guard+THEN span (both are bounded on the right by
/// `ELSE`; the ELSE arm itself extends rightward at top level).
fn check_no_mixed_toplevel(toks: &[Tok]) -> Result<(), String> {
    let mut depth: i64 = 0;
    let (mut has_and, mut has_or) = (false, false);
    for t in toks {
        match t {
            Tok::LPar | Tok::LBrack | Tok::LTup | Tok::KwIf => depth += 1,
            Tok::RPar | Tok::RBrack | Tok::RTup | Tok::KwElse => depth -= 1,
            Tok::And if depth == 0 => has_and = true,
            Tok::Or if depth == 0 => has_or = true,
            _ => {}
        }
    }
    if has_and && has_or {
        return Err(
            "unparenthesized `/\\`–`\\/` mix at the top level: TLA+ gives them \
             conflicting precedence (SANY rejects this); parenthesize one side \
             (fail closed — refusing to regroup by fixed precedence)"
                .into(),
        );
    }
    Ok(())
}

struct P<'a> {
    toks: &'a [Tok],
    pos: usize,
}

impl<'a> P<'a> {
    fn peek(&self) -> Option<&Tok> {
        self.toks.get(self.pos)
    }
    fn bump(&mut self) -> Option<Tok> {
        let t = self.toks.get(self.pos).cloned();
        if t.is_some() {
            self.pos += 1;
        }
        t
    }
    fn expect(&mut self, t: &Tok, ctx: &str) -> Result<(), String> {
        match self.bump() {
            Some(got) if got == *t => Ok(()),
            other => Err(format!("{ctx}: expected {t:?}, got {other:?}")),
        }
    }
    fn expect_ident(&mut self, ctx: &str) -> Result<String, String> {
        match self.bump() {
            Some(Tok::Ident(s)) => Ok(s),
            other => Err(format!("{ctx}: expected identifier, got {other:?}")),
        }
    }

    /// `expr := '\A' x '\in' add '..' add ':' expr | iff`.
    fn expr(&mut self) -> Result<Tx, String> {
        if matches!(self.peek(), Some(Tok::Forall)) {
            self.bump();
            let binder = self.expect_ident("\\A binder")?;
            self.expect(&Tok::In, "\\A domain")?;
            let lo = self.add()?;
            self.expect(&Tok::DotDot, "\\A domain")?;
            let hi = self.add()?;
            self.expect(&Tok::Colon, "\\A body")?;
            let body = self.expr()?;
            return Ok(Tx::Forall {
                binder,
                lo: Box::new(lo),
                hi: Box::new(hi),
                body: Box::new(body),
            });
        }
        self.iff()
    }

    fn iff(&mut self) -> Result<Tx, String> {
        let mut lhs = self.or()?;
        while matches!(self.peek(), Some(Tok::Iff)) {
            self.bump();
            let rhs = self.or()?;
            lhs = Tx::Iff(Box::new(lhs), Box::new(rhs));
        }
        Ok(lhs)
    }

    fn or(&mut self) -> Result<Tx, String> {
        let mut lhs = self.and()?;
        while matches!(self.peek(), Some(Tok::Or)) {
            self.bump();
            let rhs = self.and()?;
            lhs = Tx::Or(Box::new(lhs), Box::new(rhs));
        }
        Ok(lhs)
    }

    fn and(&mut self) -> Result<Tx, String> {
        let mut lhs = self.not()?;
        while matches!(self.peek(), Some(Tok::And)) {
            self.bump();
            let rhs = self.not()?;
            lhs = Tx::And(Box::new(lhs), Box::new(rhs));
        }
        Ok(lhs)
    }

    fn not(&mut self) -> Result<Tx, String> {
        if matches!(self.peek(), Some(Tok::Not)) {
            self.bump();
            return Ok(Tx::Not(Box::new(self.not()?)));
        }
        self.cmp()
    }

    /// `cmp := add (relop add)?` (non-chaining, TLA+ style).
    fn cmp(&mut self) -> Result<Tx, String> {
        let lhs = self.add()?;
        let mk: Option<fn(Box<Tx>, Box<Tx>) -> Tx> = match self.peek() {
            Some(Tok::Eq) => Some(Tx::Eq),
            Some(Tok::Neq) => Some(Tx::Neq),
            Some(Tok::Le) => Some(Tx::Le),
            Some(Tok::Lt) => Some(Tx::Lt),
            Some(Tok::Ge) => Some(Tx::Ge),
            Some(Tok::Gt) => Some(Tx::Gt),
            _ => None,
        };
        match mk {
            None => Ok(lhs),
            Some(f) => {
                self.bump();
                let rhs = self.add()?;
                Ok(f(Box::new(lhs), Box::new(rhs)))
            }
        }
    }

    fn add(&mut self) -> Result<Tx, String> {
        let mut lhs = self.postfix()?;
        loop {
            match self.peek() {
                Some(Tok::Plus) => {
                    self.bump();
                    let rhs = self.postfix()?;
                    lhs = Tx::Add(Box::new(lhs), Box::new(rhs));
                }
                Some(Tok::Minus) => {
                    self.bump();
                    let rhs = self.postfix()?;
                    lhs = Tx::Sub(Box::new(lhs), Box::new(rhs));
                }
                _ => return Ok(lhs),
            }
        }
    }

    /// `postfix := atom ('[' expr ']' | "'")*`.
    fn postfix(&mut self) -> Result<Tx, String> {
        let mut e = self.atom()?;
        loop {
            match self.peek() {
                Some(Tok::LBrack) => {
                    let Tx::Ident(name) = e else {
                        return Err(format!("function access on a non-identifier: {e:?}"));
                    };
                    self.bump();
                    let idx = self.expr()?;
                    self.expect(&Tok::RBrack, "function access")?;
                    e = Tx::FnAccess(name, Box::new(idx));
                }
                Some(Tok::Prime) => {
                    let Tx::Ident(name) = e else {
                        return Err(format!("prime on a non-identifier: {e:?}"));
                    };
                    self.bump();
                    e = Tx::Prime(name);
                }
                _ => return Ok(e),
            }
        }
    }

    fn atom(&mut self) -> Result<Tx, String> {
        match self.bump() {
            Some(Tok::Num(n)) => Ok(Tx::Num(n)),
            Some(Tok::KwTrue) => Ok(Tx::BoolLit(true)),
            Some(Tok::KwFalse) => Ok(Tx::BoolLit(false)),
            Some(Tok::Ident(id)) => Ok(Tx::Ident(id)),
            Some(Tok::KwIf) => {
                let c = self.expr()?;
                self.expect(&Tok::KwThen, "IF")?;
                let t = self.expr()?;
                self.expect(&Tok::KwElse, "IF")?;
                let e = self.expr()?;
                Ok(Tx::Ite(Box::new(c), Box::new(t), Box::new(e)))
            }
            Some(Tok::KwUnchanged) => {
                if matches!(self.peek(), Some(Tok::LTup)) {
                    self.bump();
                    let mut vars = vec![self.expect_ident("UNCHANGED tuple")?];
                    while matches!(self.peek(), Some(Tok::Comma)) {
                        self.bump();
                        vars.push(self.expect_ident("UNCHANGED tuple")?);
                    }
                    self.expect(&Tok::RTup, "UNCHANGED tuple")?;
                    Ok(Tx::Unchanged(vars))
                } else {
                    Ok(Tx::Unchanged(vec![self.expect_ident("UNCHANGED")?]))
                }
            }
            Some(Tok::LPar) => {
                let e = self.expr()?;
                self.expect(&Tok::RPar, "parenthesized expression")?;
                Ok(e)
            }
            Some(Tok::LBrack) => {
                // `[x \in lo..hi |-> body]` or `[f EXCEPT ![i] = v]`.
                let head = self.expect_ident("function form")?;
                match self.peek() {
                    Some(Tok::In) => {
                        self.bump();
                        let lo = self.add()?;
                        self.expect(&Tok::DotDot, "comprehension domain")?;
                        let hi = self.add()?;
                        self.expect(&Tok::MapsTo, "comprehension")?;
                        let body = self.expr()?;
                        self.expect(&Tok::RBrack, "comprehension")?;
                        Ok(Tx::Comprehension {
                            binder: head,
                            lo: Box::new(lo),
                            hi: Box::new(hi),
                            body: Box::new(body),
                        })
                    }
                    Some(Tok::KwExcept) => {
                        self.bump();
                        self.expect(&Tok::Bang, "EXCEPT")?;
                        self.expect(&Tok::LBrack, "EXCEPT index")?;
                        let index = self.expr()?;
                        self.expect(&Tok::RBrack, "EXCEPT index")?;
                        self.expect(&Tok::Eq, "EXCEPT value")?;
                        let value = self.expr()?;
                        self.expect(&Tok::RBrack, "EXCEPT")?;
                        Ok(Tx::Except {
                            base: head,
                            index: Box::new(index),
                            value: Box::new(value),
                        })
                    }
                    other => Err(format!("unsupported [..] form after {head:?}: {other:?}")),
                }
            }
            other => Err(format!("expected atom, got {other:?}")),
        }
    }
}

/// Extract every `Name == body` operator definition from a TLA+ module source,
/// with MULTI-LINE bodies (continuation lines = anything that is not a new
/// definition, a module separator, or a header keyword line).
///
/// BULLET FIDELITY: `/\`- or `\/`-bulleted continuation shapes (the exact
/// `trust_model!` emission shape) are reconstructed with TLA+ bullet-list
/// grouping — bullets aligned at one column form a list, each item extends
/// through the more-indented lines below it, items are rendered PARENTHESIZED
/// and joined with the bullet operator. So a looser operator inside one item
/// (`\/`, `<=>`, a `\A` body) can never swallow or regroup a sibling bullet:
/// `/\ x = 0 \/ x = 5` + `/\ x' = x + 1` renders as
/// `(x = 0 \/ x = 5) /\ (x' = x + 1)`, never as an `\/` that captures the
/// update. Non-bulleted continuation lines are joined with a space (ordinary
/// TLA+ line continuation, which never regroups).
///
/// Errors (fail closed): a DUPLICATE operator definition (real TLA+ rejects
/// redefinition; silently letting the last `Safety ==` win would redefine the
/// invariant), misaligned/mixed bullets at one column, dedents below the
/// bullet column, and empty bullet items.
pub fn operator_table(spec_src: &str) -> Result<Vec<(String, String)>, String> {
    let mut out: Vec<(String, String)> = Vec::new();
    // (name, body segments as (column, text)) of the operator being collected.
    let mut current: Option<(String, Vec<(usize, String)>)> = None;

    fn flush(
        current: &mut Option<(String, Vec<(usize, String)>)>,
        out: &mut Vec<(String, String)>,
    ) -> Result<(), String> {
        if let Some((name, segs)) = current.take() {
            if out.iter().any(|(n, _)| *n == name) {
                return Err(format!(
                    "duplicate definition of operator {name} (TLA+ forbids \
                     redefinition; refusing the last-one-wins ambiguity)"
                ));
            }
            let body = render_body(&segs).map_err(|e| format!("operator {name}: {e}"))?;
            out.push((name, body));
        }
        Ok(())
    }

    for raw in spec_src.lines() {
        let line = raw.trim();
        let indent = raw.len() - raw.trim_start().len();
        if line.starts_with("----") || line.starts_with("====") {
            flush(&mut current, &mut out)?;
            continue;
        }
        let is_header = line.starts_with("EXTENDS")
            || line.starts_with("CONSTANTS")
            || line.starts_with("CONSTANT")
            || line.starts_with("VARIABLES")
            || line.starts_with("VARIABLE")
            || line.starts_with("MODULE");
        if is_header {
            flush(&mut current, &mut out)?;
            continue;
        }
        // A definition start is `ident == rest` (ident directly at line head).
        let def_start = line.split_once("==").and_then(|(head, rest)| {
            let name = head.trim();
            let valid = !name.is_empty()
                && name
                    .chars()
                    .all(|ch| ch.is_ascii_alphanumeric() || ch == '_')
                && !rest.starts_with('=');
            valid.then(|| (name.to_string(), rest.trim().to_string()))
        });
        if let Some((name, first)) = def_start {
            flush(&mut current, &mut out)?;
            let mut segs = Vec::new();
            if !first.is_empty() {
                // Column of the body text within the raw line (for bullet
                // alignment against continuation lines).
                let col = raw
                    .find("==")
                    .map(|i| {
                        let after = &raw[i + 2..];
                        i + 2 + (after.len() - after.trim_start().len())
                    })
                    .unwrap_or(indent);
                segs.push((col, first));
            }
            current = Some((name, segs));
        } else if let Some((_, segs)) = current.as_mut() {
            if !line.is_empty() {
                segs.push((indent, line.to_string()));
            }
        }
    }
    flush(&mut current, &mut out)?;
    Ok(out)
}

/// The bullet token opening `s`, if any.
fn bullet_of(s: &str) -> Option<&'static str> {
    if s.starts_with("/\\") {
        Some("/\\")
    } else if s.starts_with("\\/") {
        Some("\\/")
    } else {
        None
    }
}

/// Render a multi-segment operator body to one parse-ready line, preserving
/// TLA+ bullet-list grouping (see [`operator_table`]). Recursive: each bullet
/// item's own segments are rendered by the same rules (nested bullet lists at
/// deeper columns included), then parenthesized.
fn render_body(segs: &[(usize, String)]) -> Result<String, String> {
    if segs.is_empty() {
        return Err("empty operator body".into());
    }
    if segs.len() == 1 {
        return Ok(segs[0].1.clone());
    }
    let bcol = segs[0].0;
    let Some(bullet) = bullet_of(&segs[0].1) else {
        // Ordinary TLA+ line continuation — joining never regroups. (An
        // ambiguous `/\`–`\/` mix in the joined text is refused by
        // `parse_fragment`'s unparenthesized-mixing guard.)
        return Ok(segs
            .iter()
            .map(|(_, t)| t.as_str())
            .collect::<Vec<_>>()
            .join(" "));
    };
    let mut items: Vec<Vec<(usize, String)>> = Vec::new();
    for (col, text) in segs {
        if *col == bcol && bullet_of(text) == Some(bullet) {
            // A new item: the text after the bullet token.
            let rest = &text[2..];
            let ws = rest.len() - rest.trim_start().len();
            let rest = rest.trim_start();
            let mut item = Vec::new();
            if !rest.is_empty() {
                item.push((col + 2 + ws, rest.to_string()));
            }
            items.push(item);
        } else if *col == bcol {
            return Err(format!(
                "line at the bullet column does not start with `{bullet}`: \
                 {text:?} (mixed or misaligned bullets — fail closed; \
                 parenthesize to disambiguate)"
            ));
        } else if *col < bcol {
            return Err(format!(
                "continuation line dedents below the bullet column: {text:?} \
                 (fail closed; align or parenthesize)"
            ));
        } else {
            items
                .last_mut()
                .expect("the first segment opened an item")
                .push((*col, text.clone()));
        }
    }
    let mut rendered = Vec::with_capacity(items.len());
    for item in &items {
        let r = render_body(item).map_err(|e| format!("in a `{bullet}` bullet item: {e}"))?;
        rendered.push(format!("({r})"));
    }
    Ok(rendered.join(&format!(" {bullet} ")))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parser_ring_push_action_parses() {
        let t = parse_fragment(
            "seq <= MaxSeq - 1 /\\ seq' = seq + 1 /\\ lo' = (IF (seq + 1) - lo + 1 > Cap THEN lo + 1 ELSE lo)",
        )
        .expect("parse Push");
        let conj = t.split_and();
        assert_eq!(conj.len(), 3);
        assert!(!conj[0].has_prime());
        assert!(conj[1].has_prime() && conj[2].has_prime());
    }

    #[test]
    fn test_parser_bulleted_multiline_body_joins() {
        let src = "---- MODULE M ----\nVARIABLES a, b\nInit ==\n  /\\ a = 0\n  /\\ b = 1\nNext == a' = a /\\ UNCHANGED b\n====\n";
        let table = operator_table(src).expect("table");
        let init = &table.iter().find(|(n, _)| n == "Init").expect("Init").1;
        let t = parse_fragment(init).expect("parse bulleted Init");
        assert_eq!(t.split_and().len(), 2);
    }

    #[test]
    fn test_bullet_items_keep_their_grouping() {
        // REGRESSION (false-accept vector): a disjunctive guard on one bullet
        // line must NOT capture the update on the next bullet line. The bullet
        // items are parenthesized, so the guard stays a guard.
        let src = "---- MODULE M ----\nVARIABLE x\nAct ==\n  /\\ x = 0 \\/ x = 5\n  /\\ x' = x + 1\n====\n";
        let table = operator_table(src).expect("table");
        let act = &table.iter().find(|(n, _)| n == "Act").expect("Act").1;
        assert_eq!(act, "(x = 0 \\/ x = 5) /\\ (x' = x + 1)");
        let t = parse_fragment(act).expect("parse");
        assert_eq!(t.split_or().len(), 1, "top level must stay a conjunction");
        let conj = t.split_and();
        assert_eq!(conj.len(), 2);
        assert!(matches!(conj[0], Tx::Or(..)), "guard keeps its disjunction");
        assert!(conj[1].has_prime(), "update survives as a sibling conjunct");
    }

    #[test]
    fn test_forall_bullet_item_does_not_swallow_siblings() {
        // REGRESSION: a `\A` bullet item used to swallow every later bullet
        // into its quantified body. Parenthesized items keep `Q` a sibling.
        let src = "---- MODULE M ----\nVARIABLES x, y\nInv ==\n  /\\ \\A n \\in 1..2 : x <= n\n  /\\ y = 0\n====\n";
        let table = operator_table(src).expect("table");
        let inv = &table.iter().find(|(n, _)| n == "Inv").expect("Inv").1;
        let t = parse_fragment(inv).expect("parse");
        let conj = t.split_and();
        assert_eq!(conj.len(), 2, "the forall must not swallow `y = 0`");
        assert!(matches!(conj[0], Tx::Forall { .. }));
        assert!(matches!(conj[1], Tx::Eq(..)));
    }

    #[test]
    fn test_nested_bullets_render_recursively() {
        let src = "---- MODULE M ----\nVARIABLE x\nNext ==\n  \\/ /\\ x = 0\n     /\\ x' = 1\n  \\/ /\\ x = 1\n     /\\ x' = 0\n====\n";
        let table = operator_table(src).expect("table");
        let next = &table.iter().find(|(n, _)| n == "Next").expect("Next").1;
        assert_eq!(next, "((x = 0) /\\ (x' = 1)) \\/ ((x = 1) /\\ (x' = 0))");
        let t = parse_fragment(next).expect("parse");
        assert_eq!(t.split_or().len(), 2, "two guarded-assignment branches");
    }

    #[test]
    fn test_operator_table_rejects_duplicate_definitions() {
        // Real TLA+ rejects redefinition; last-one-wins would silently
        // redefine the invariant.
        let src = "---- MODULE M ----\nVARIABLE x\nSafety == x >= 0\nSafety == x <= 5\n====\n";
        let err = operator_table(src).expect_err("duplicate Safety must be refused");
        assert!(err.contains("duplicate"), "got {err}");
    }

    #[test]
    fn test_operator_table_rejects_misaligned_bullets() {
        // A `\/` at the `/\` bullet column is a mixed/misaligned list — fail
        // closed instead of guessing a grouping.
        let src = "---- MODULE M ----\nVARIABLE x\nAct ==\n  /\\ x = 0\n  \\/ x = 1\n====\n";
        assert!(operator_table(src).is_err());
        // A dedent below the bullet column likewise.
        let src2 = "---- MODULE M ----\nVARIABLE x\nAct ==\n    /\\ x = 0\n  x = 1\n====\n";
        assert!(operator_table(src2).is_err());
    }

    #[test]
    fn test_parser_refuses_unparenthesized_and_or_mix() {
        // SANY-illegal on a single line; silently regrouping by precedence was
        // the false-accept vector.
        assert!(parse_fragment("x = 0 \\/ x = 5 /\\ x' = x + 1").is_err());
        assert!(parse_fragment("/\\ x = 0 \\/ x = 5 /\\ x' = x + 1").is_err());
        // Parenthesized forms are fine.
        assert!(parse_fragment("(x = 0 \\/ x = 5) /\\ x' = x + 1").is_ok());
        assert!(parse_fragment("x = 0 \\/ (x = 5 /\\ x' = x + 1)").is_ok());
        // IF…THEN…ELSE delimits its guard+THEN span (no parens needed).
        assert!(parse_fragment("a = 1 \\/ b = IF c = 0 /\\ d = 0 THEN 1 ELSE 0").is_ok());
    }

    #[test]
    fn test_parser_evict_full_shapes_parse() {
        let live = "(IF e THEN [n \\in 1..MaxSeq |-> IF n = seq + 1 THEN TRUE ELSE (live[n] /\\ n # lo)] ELSE [live EXCEPT ![seq + 1] = TRUE])";
        assert!(parse_fragment(live).is_ok(), "fn-update shapes must parse");
        let inv = "\\A n \\in 1..MaxSeq : live[n] <=> (lo <= n /\\ n <= seq)";
        let t = parse_fragment(inv).expect("forall/iff parses");
        assert!(matches!(t, Tx::Forall { .. }));
    }

    #[test]
    fn test_parser_unchanged_tuple_and_disjunctive_guard() {
        let t = parse_fragment(
            "(Buggy = 1 \\/ lo <= cursor + 1) /\\ cursor' = seq /\\ UNCHANGED <<seq, lo>>",
        )
        .expect("parse");
        let conj = t.split_and();
        assert_eq!(conj.len(), 3);
        assert!(matches!(conj[0], Tx::Or(..)));
        assert!(matches!(conj[2], Tx::Unchanged(v) if v == &["seq".to_string(), "lo".to_string()]));
    }

    #[test]
    fn test_parser_rejects_garbage() {
        assert!(parse_fragment("seq $ 1").is_err());
        assert!(parse_fragment("IF a THEN b").is_err());
        assert!(parse_fragment("").is_err());
    }
}
