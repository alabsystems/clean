// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! sertop subprocess driver (pipe protocol, never interactive).
//!
//! One command per line on stdin; answers stream back as single-line
//! `(Answer <tag> ...)` / `(Feedback ...)` sexps (sertop assigns tags in
//! command order, mirrored by a local counter). A dedicated reader thread
//! feeds a channel so every wait carries a timeout; on timeout the caller
//! kills the process and respawns (Drop kills the child).

use std::io::{BufRead, BufReader, Write};
use std::path::Path;
use std::process::{Child, ChildStdin, Command, Stdio};
use std::sync::mpsc::{self, Receiver, RecvTimeoutError};
use std::time::Duration;

use thiserror::Error;

use crate::sexp_io::{parse_sexp_utf8, quote_string};
use clean_mathverse::coq::alpha::Sexp;

/// Errors from driving the sertop subprocess.
#[derive(Debug, Error)]
pub enum SertopErr {
    #[error("sertop answer timed out after {0:?}")]
    Timeout(Duration),
    #[error("sertop stream closed unexpectedly")]
    Closed,
    #[error("sertop io: {0}")]
    Io(#[from] std::io::Error),
    #[error("coq exception: {0}")]
    Exn(String),
}

/// Everything sertop produced for one command.
#[derive(Debug, Default)]
pub struct CmdOutput {
    /// Payload answers (the sexp text between the tag and the closing paren).
    pub payloads: Vec<String>,
    /// Raw feedback lines seen while the command was in flight.
    pub feedback: Vec<String>,
    /// First `CoqExn` payload, if any.
    pub exn: Option<String>,
}

/// Result of a `Definition` / `TypeOf` query, pre-classified.
#[derive(Debug)]
pub enum QueryObj {
    /// `(CoqConstr <term>)` — an elaborated kernel term.
    Constr(Sexp),
    /// `(CoqMInd ...)` — mutual inductive payload (items after the head).
    MInd(Vec<Sexp>),
    /// Query completed with an empty `ObjList`.
    Empty,
    /// Query raised a `CoqExn` (e.g. name is not a constant).
    Exn(String),
    /// Some other object kind we do not consume.
    Other(String),
}

pub struct Sertop {
    child: Child,
    stdin: ChildStdin,
    rx: Receiver<String>,
    next_tag: u64,
    timeout: Duration,
}

impl Sertop {
    /// Spawn `sertop --printer=sertop` with piped stdio.
    pub fn spawn(path: &Path, timeout: Duration) -> Result<Self, SertopErr> {
        let mut child = Command::new(path)
            .arg("--printer=sertop")
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::null())
            .spawn()?;
        let stdin = child.stdin.take().ok_or(SertopErr::Closed)?;
        let stdout = child.stdout.take().ok_or(SertopErr::Closed)?;
        let (tx, rx) = mpsc::channel::<String>();
        std::thread::spawn(move || {
            // Answers can be multi-MB single lines; BufReader::read_line
            // grows the buffer as needed (no fixed-line-length assumption).
            let mut reader = BufReader::with_capacity(1 << 20, stdout);
            let mut line = String::new();
            loop {
                line.clear();
                match reader.read_line(&mut line) {
                    Ok(0) | Err(_) => break,
                    Ok(_) => {
                        if tx.send(line.trim_end().to_string()).is_err() {
                            break;
                        }
                    }
                }
            }
        });
        Ok(Self {
            child,
            stdin,
            rx,
            next_tag: 0,
            timeout,
        })
    }

    /// Send one command line and collect everything up to its `Completed`.
    pub fn command(&mut self, cmd: &str) -> Result<CmdOutput, SertopErr> {
        let tag = self.next_tag;
        self.next_tag += 1;
        writeln!(self.stdin, "{cmd}")?;
        self.stdin.flush()?;
        let mut out = CmdOutput::default();
        loop {
            let line = self.rx.recv_timeout(self.timeout).map_err(|e| match e {
                RecvTimeoutError::Timeout => SertopErr::Timeout(self.timeout),
                RecvTimeoutError::Disconnected => SertopErr::Closed,
            })?;
            if line.starts_with("(Feedback") {
                out.feedback.push(line);
                continue;
            }
            let Some((t, body)) = parse_answer(&line) else {
                continue;
            };
            if t != tag {
                continue; // stale answer from a pre-timeout command
            }
            match body {
                AnswerBody::Ack => {}
                AnswerBody::Completed => return Ok(out),
                AnswerBody::Exn(s) => {
                    if out.exn.is_none() {
                        out.exn = Some(s);
                    }
                }
                AnswerBody::Payload(p) => out.payloads.push(p),
            }
        }
    }

    /// `(Add () "Require Import <module>.")` + `(Exec <last-sid>)` — the
    /// historical loading form. A notation-grammar clash during the Import
    /// (e.g. `mathcomp.algebra.poly`'s "Egramcoq.NotationLevelMismatch",
    /// `presentation`'s custom-entry double registration) raises here; the
    /// caller must NOT retry in the same process — the failed Import leaves
    /// grammar side-effects half-applied — but respawn and use
    /// [`Self::require_plain`] (see `Session::client`).
    pub fn require(&mut self, module: &str) -> Result<(), SertopErr> {
        self.require_stmt(&format!("Require Import {module}."))
    }

    /// Plain `Require` (no Import): loads the module without importing its
    /// notations into scope. Sufficient for the dump — every query is by
    /// fully-qualified name and `Print Module` lists names — and immune to
    /// notation-grammar clashes that break `Require Import`.
    pub fn require_plain(&mut self, module: &str) -> Result<(), SertopErr> {
        self.require_stmt(&format!("Require {module}."))
    }

    /// Execute state-changing vernacular (`Set Printing All.` etc.) through
    /// the same `Add` + `Exec` protocol as module loading — a `(Query ()
    /// (Vernac ...))` runs in a QUERY context whose side effects do not
    /// reliably persist in the document state.
    pub fn execute(&mut self, stmt: &str) -> Result<(), SertopErr> {
        self.require_stmt(stmt)
    }

    fn require_stmt(&mut self, stmt: &str) -> Result<(), SertopErr> {
        let add = format!("(Add () {})", quote_string(stmt));
        let out = self.command(&add)?;
        if let Some(e) = out.exn {
            return Err(SertopErr::Exn(e));
        }
        let last_sid = out
            .payloads
            .iter()
            .filter_map(|p| {
                let rest = p.strip_prefix("(Added ")?;
                let digits: String = rest.chars().take_while(char::is_ascii_digit).collect();
                digits.parse::<u64>().ok()
            })
            .max()
            .ok_or_else(|| SertopErr::Exn("Add returned no sentence id".to_string()))?;
        let out = self.command(&format!("(Exec {last_sid})"))?;
        if let Some(e) = out.exn {
            return Err(SertopErr::Exn(e));
        }
        Ok(())
    }

    /// Run `(Query () (<kind> "<name>"))` and classify the first object.
    pub fn query_obj(&mut self, kind: &str, name: &str) -> Result<QueryObj, SertopErr> {
        let cmd = format!("(Query () ({kind} {}))", quote_string(name));
        let out = self.command(&cmd)?;
        if let Some(e) = out.exn {
            return Ok(QueryObj::Exn(e));
        }
        let Some(payload) = out.payloads.first() else {
            return Ok(QueryObj::Empty);
        };
        let Ok(sx) = parse_sexp_utf8(payload) else {
            return Ok(QueryObj::Other("unparseable-answer".to_string()));
        };
        let Sexp::List(items) = &sx else {
            return Ok(QueryObj::Other("non-list-answer".to_string()));
        };
        if !matches!(items.first(), Some(Sexp::Atom(h)) if h == "ObjList") {
            return Ok(QueryObj::Other("non-objlist-answer".to_string()));
        }
        let Some(Sexp::List(objs)) = items.get(1) else {
            return Ok(QueryObj::Empty);
        };
        let Some(Sexp::List(obj)) = objs.first() else {
            return Ok(QueryObj::Empty);
        };
        match obj.first() {
            Some(Sexp::Atom(h)) if h == "CoqConstr" => match obj.get(1) {
                Some(term) => Ok(QueryObj::Constr(term.clone())),
                None => Ok(QueryObj::Other("CoqConstr-empty".to_string())),
            },
            Some(Sexp::Atom(h)) if h == "CoqMInd" => Ok(QueryObj::MInd(obj[1..].to_vec())),
            Some(Sexp::Atom(h)) => Ok(QueryObj::Other(h.clone())),
            _ => Ok(QueryObj::Other("headless-object".to_string())),
        }
    }
}

impl Drop for Sertop {
    fn drop(&mut self) {
        let _ = self.child.kill();
        let _ = self.child.wait();
    }
}

enum AnswerBody {
    Ack,
    Completed,
    Exn(String),
    Payload(String),
}

/// Parse `(Answer <tag> <body>)` framing without a full sexp parse.
fn parse_answer(line: &str) -> Option<(u64, AnswerBody)> {
    let rest = line.strip_prefix("(Answer")?.trim_start();
    let digits_end = rest.find(|c: char| !c.is_ascii_digit())?;
    let tag: u64 = rest[..digits_end].parse().ok()?;
    let body = rest[digits_end..].strip_suffix(')')?.trim();
    let body = match body {
        "Ack" => AnswerBody::Ack,
        "Completed" => AnswerBody::Completed,
        b if b.starts_with("(CoqExn") => AnswerBody::Exn(b.to_string()),
        b => AnswerBody::Payload(b.to_string()),
    };
    Some((tag, body))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_answer_framing_variants() {
        let (t, b) = parse_answer("(Answer 0 Ack)").expect("ack should parse");
        assert!(matches!(b, AnswerBody::Ack));
        assert_eq!(t, 0);
        let (t, b) = parse_answer("(Answer 12 Completed)").expect("completed should parse");
        assert!(matches!(b, AnswerBody::Completed));
        assert_eq!(t, 12);
        let (_, b) = parse_answer("(Answer 2(ObjList((CoqConstr(Sort Set)))))")
            .expect("payload should parse");
        match b {
            AnswerBody::Payload(p) => assert_eq!(p, "(ObjList((CoqConstr(Sort Set))))"),
            _ => panic!("expected payload"),
        }
        let (_, b) = parse_answer("(Answer 3(CoqExn((loc())(exn X))))").expect("exn should parse");
        assert!(matches!(b, AnswerBody::Exn(_)));
    }
}
