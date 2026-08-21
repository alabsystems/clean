// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Function/interface parsing for reader B.

use super::{
    EmittedError, ParamSlot, Reader, Sx, CALLING_CONVS, CLAUSE_KINDS, LINKAGES, SELF_FUNC_INDEX,
};

impl Reader {
    pub(super) fn run(&mut self, text: &str) -> Result<Sx, EmittedError> {
        let mut entry: Option<u32> = None;
        let mut params: Vec<Sx> = Vec::new();
        let mut blocks: Vec<Sx> = Vec::new();
        let mut cur: Option<(u32, Vec<Sx>, Vec<Sx>)> = None;
        let mut seen_header = false;
        let mut closed = false;

        for (i, raw) in text.lines().enumerate() {
            self.line = i + 1;
            // EVERYTHING AFTER THE CLOSING BRACE IS REFUSED.
            //
            // This used to be a bare `break`, and the `break` was an erasure
            // nobody had written down — the exact shape this reader's own
            // blind-slot ledger exists to stop. Measured 2026-08-20: a text
            // carrying `m::f` followed by a whole second function `m::g`
            // projected to the SAME core module as `m::f` alone, and so did the
            // same text followed by a `global` declaration, a `file` table, or
            // arbitrary prose. Worse, a `}` appearing MID-BODY truncated the
            // body and dropped every instruction after it in silence.
            //
            // That last one is why this is a refusal and not a validation of
            // the tail: the completeness argument the ledger rests on is that
            // both readers are TOTAL-OR-REFUSING, so a field can only be erased
            // by a line somebody wrote to erase it. A reader that stops early
            // and ignores the remainder is not total over its own input, and no
            // enumeration of erasures can cover what it drops.
            if closed {
                if !raw.trim().is_empty() {
                    return Err(self.syn(format!(
                        "`{}` follows the body's closing brace. This reader projects ONE function \
                         and would drop it unread; a fixture that carries a second function, a \
                         module table or anything else is not the one-body artifact the chain's \
                         tag table describes",
                        raw.trim()
                    )));
                }
                continue;
            }
            let (code, clauses) = strip_comment(raw);
            for (kind, content) in clauses {
                if !CLAUSE_KINDS.contains(&kind) {
                    return Err(self.syn(format!(
                        "annotation clause `; #{kind}` is not one of the {} kinds this reader \
                         knows to be inert ({CLAUSE_KINDS:?}). Erasing an unknown annotation is \
                         how a trust-bearing field goes missing in silence; add it to \
                         CLAUSE_KINDS with a stated reason, or read it.",
                        CLAUSE_KINDS.len()
                    )));
                }
                // `#producer` is the ONE allowed kind whose content is read.
                // The other four carry debug info (`loc`, `scope`, `names`) or
                // a claim ABOUT the body (`proof`); this one names WHO COMPILED
                // IT, and a lane whose whole subject is which compiler emitted
                // this body cannot erase that and call the erasure inert.
                if kind == "producer" {
                    let token = content.trim_start_matches(':').trim().to_string();
                    if token.is_empty() {
                        return Err(self.syn("`; #producer:` names no producer"));
                    }
                    if self.producer.replace(token).is_some() {
                        return Err(self.syn(
                            "the body carries two `; #producer:` clauses; which one produced it \
                             would be a choice this reader is not entitled to make",
                        ));
                    }
                }
                self.clauses.insert(kind.to_string());
            }
            let line = code.trim();
            if line.is_empty() {
                continue;
            }
            if !seen_header {
                self.header(line)?;
                seen_header = true;
                continue;
            }
            if line == "}" {
                closed = true;
                continue;
            }
            if let Some(rest) = line.strip_suffix(':') {
                if let Some(b) = rest.strip_prefix("bb") {
                    if let Some((id, ps, nodes)) = cur.take() {
                        blocks.push(block(id, ps, nodes));
                    }
                    let (id, ps) = self.block_header(b)?;
                    if entry.is_none() {
                        entry = Some(id);
                        self.entry = Some(id);
                        params = ps;
                        cur = Some((id, Vec::new(), Vec::new()));
                    } else {
                        cur = Some((id, ps, Vec::new()));
                    }
                    continue;
                }
            }
            let Some((_, _, nodes)) = cur.as_mut() else {
                return Err(self.syn("an instruction before any block header"));
            };
            let n = self.node(line)?;
            nodes.push(n);
        }
        if let Some((id, ps, nodes)) = cur.take() {
            blocks.push(block(id, ps, nodes));
        }
        let entry = entry.ok_or_else(|| self.syn("no block in the body"))?;
        if !closed {
            return Err(self.syn(
                "the body has no closing brace. `Display for Function` always emits one, so text \
                 that runs out without it is a TRUNCATED artifact — and reading a truncated body \
                 as a complete one is the same erasure as ignoring a tail, from the other end",
            ));
        }
        Ok(Sx::tag(
            "module",
            vec![
                Sx::tag(
                    "funcs",
                    vec![Sx::tag(
                        "func",
                        vec![
                            // The function's OWN index. One namespace with the
                            // callee ids by construction — see the module docs
                            // and `func_index` below.
                            Sx::a(SELF_FUNC_INDEX.to_string()),
                            Sx::tag("params", params),
                            Sx::tag("entry", vec![Sx::a(entry.to_string())]),
                            Sx::tag("blocks", blocks),
                        ],
                    )],
                ),
                Sx::tag("globals", vec![]),
            ],
        ))
    }

    /// `[<linkage> ][<conv> ]fn @<name>(functy.<N>) {` — the function's
    /// LINKAGE, its CALLING CONVENTION, its NAME and the index of its entry in
    /// the whole-crate function-type table.
    ///
    /// # Absence is a value
    ///
    /// trust-ir's printer suppresses each of the first two when it holds its
    /// default (`Display for Function`: `if self.linkage != Linkage::External`,
    /// `if self.calling_conv != CallingConv::C`), and its parser restores the
    /// default on absence (`try_parse_calling_conv` returns `CallingConv::C`
    /// when no keyword is there). So a header that prints no linkage token says
    /// `external`, not "unknown" — and this reader has to say the same thing,
    /// or the two ends of the round trip disagree about what silence means.
    ///
    /// # What this replaced, and why the replacement is not cosmetic
    ///
    /// Until 2026-08-20 this was `line.strip_prefix("rustcc fn @")`, and
    /// `data/crystal_mint_blind_slots.json` recorded calling convention and
    /// linkage as PERMANENTLY BLIND — *"the producer prints neither, so no text
    /// reader CAN witness either."* That was false: `rustcc` **is** the calling
    /// convention, printed because it is not the default. The literal prefix
    /// was therefore pinning both slots by accident, at the cost of a reader
    /// that refused `ccc fn @m::f` with "expected the `rustcc fn @…` header
    /// first" — a message that names the shape and not the slot, and that the
    /// first chain on an `internal`-linkage body would have been "fixed" by
    /// loosening. Reading them is what makes the pin survive that.
    fn header(&mut self, line: &str) -> Result<(), EmittedError> {
        let mut rest = line.trim();
        // Exactly two optional keywords, in the printer's order, each matched
        // against a CLOSED list. An unknown leading token is not skipped — it
        // falls through to the `fn @` check and is refused, so a linkage or
        // convention trust-ir grows later cannot be read as "no token".
        for (list, slot) in [
            (&LINKAGES[..], &mut self.linkage),
            (&CALLING_CONVS[..], &mut self.calling_conv),
        ] {
            if let Some((tok, tail)) = rest.split_once(' ') {
                if let Some(found) = list.iter().find(|k| **k == tok) {
                    *slot = (*found).to_string();
                    rest = tail.trim_start();
                }
            }
        }
        let rest = rest.strip_prefix("fn @").ok_or_else(|| {
            self.syn(format!(
                "expected a `[<linkage> ][<conv> ]fn @…` header, found `{line}`. The linkage \
                 keywords are {LINKAGES:?} and the calling conventions {CALLING_CONVS:?}; each is \
                 printed only when it is NOT the default, so an unknown leading token is refused \
                 rather than skipped"
            ))
        })?;
        let rest = rest.trim_end().strip_suffix('{').unwrap_or(rest).trim_end();
        let (name, functy) = rest.rsplit_once("(functy.").ok_or_else(|| {
            self.syn("the header must name the function's signature as `(functy.N)`")
        })?;
        let functy = functy
            .strip_suffix(')')
            .ok_or_else(|| self.syn("unbalanced `(functy.N)` in the header"))?;
        self.functy = functy
            .parse()
            .map_err(|_| self.syn(format!("`functy.{functy}` is not a number")))?;
        if name.is_empty() {
            return Err(self.syn("the header names no function"));
        }
        self.fn_name = name.to_string();
        Ok(())
    }

    /// `0(%0: ptr, %1: u32)` or `0` — the id, the parameter SSA ids, and each
    /// parameter's TYPE.
    ///
    /// The type is not in the returned core form — Clean's `IRFunc` and
    /// `IRBlock` have nowhere to put one — but it is recorded, because
    /// `bb0(%0: ptr)` and `bb0(%0: Rc<enum.13>)` are a `&CleanMode` and an
    /// `Rc<CleanMode>` and the entry `load` reads the discriminant in one and
    /// the refcount header in the other. See [`super::super::interface`].
    fn block_header(&mut self, s: &str) -> Result<(u32, Vec<Sx>), EmittedError> {
        let (idtxt, rest) = match s.find('(') {
            Some(p) => (&s[..p], &s[p..]),
            None => (s, ""),
        };
        let id: u32 = idtxt
            .parse()
            .map_err(|_| self.syn(format!("block id `{idtxt}` is not a number")))?;
        let mut ps = Vec::new();
        if !rest.is_empty() {
            let inner = rest
                .strip_prefix('(')
                .and_then(|x| x.strip_suffix(')'))
                .ok_or_else(|| self.syn("unbalanced block parameter list"))?;
            for (index, p) in split_top(inner)
                .into_iter()
                .map(str::trim)
                .filter(|p| !p.is_empty())
                .enumerate()
            {
                let (name, ty) = p.split_once(':').ok_or_else(|| {
                    self.syn(format!(
                        "block parameter `{p}` carries no `: <type>`. trust-ir's printer always \
                         emits one, and a parameter read without its type is the `param-type` \
                         blind slot"
                    ))
                })?;
                let ssa = self.val(name)?;
                let ty = ty.trim();
                if ty.is_empty() {
                    return Err(self.syn(format!("block parameter `{p}` has an empty type")));
                }
                ps.push(Sx::a(ssa.to_string()));
                self.param_slots.push(ParamSlot {
                    block: id,
                    index: u32::try_from(index).unwrap_or(u32::MAX),
                    ssa,
                    ty: ty.to_string(),
                });
            }
        }
        Ok((id, ps))
    }
}

fn block(id: u32, params: Vec<Sx>, nodes: Vec<Sx>) -> Sx {
    Sx::tag(
        "block",
        vec![
            Sx::a(id.to_string()),
            Sx::tag("params", params),
            Sx::tag("nodes", nodes),
        ],
    )
}

/// Split a printed line into its code and the KINDS of trailing `; #…` clause
/// the producer appended.
///
/// The kinds are returned rather than discarded so the caller can check them
/// against [`CLAUSE_KINDS`]. Dropping the clause is right; dropping it without
/// looking at what it said is how an annotation that turns out to matter gets
/// erased in silence.
fn strip_comment(line: &str) -> (&str, Vec<(&str, &str)>) {
    match line.find("  ; #") {
        Some(p) => (&line[..p], clause_kinds(&line[p..])),
        None => (line, Vec::new()),
    }
}

/// The identifier after each `; #` in a comment run.
fn clause_kinds(comment: &str) -> Vec<(&str, &str)> {
    comment
        .split("; #")
        .skip(1)
        .map(|seg| {
            let end = seg
                .find(|c: char| !c.is_ascii_alphanumeric() && c != '_')
                .unwrap_or(seg.len());
            seg.split_at(end)
        })
        .collect()
}

/// Split a comma-separated list at TOP-LEVEL commas only.
///
/// A printed `trust_ir::Ty` can contain commas of its own — `(u8, u8)` for a
/// tuple, `set<ty.3, u8>` for a set — so splitting a block-parameter list on
/// every comma would cut one type in half and read one parameter as two. It did
/// not bite while the type was being thrown away; it would the moment it is
/// read.
fn split_top(s: &str) -> Vec<&str> {
    let mut out = Vec::new();
    let mut depth = 0i32;
    let mut start = 0usize;
    for (i, c) in s.char_indices() {
        match c {
            '(' | '<' | '[' => depth += 1,
            ')' | '>' | ']' => depth -= 1,
            ',' if depth == 0 => {
                out.push(&s[start..i]);
                start = i + 1;
            }
            _ => {}
        }
    }
    out.push(&s[start..]);
    out
}
