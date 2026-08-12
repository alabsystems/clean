// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Per-module dump pipeline: enumerate via `Print Module`, classify every
//! candidate by live `Definition`/`TypeOf` queries, append importer forms,
//! validate through the real importer, and write the sidecar.

use std::collections::HashSet;
use std::path::Path;
use std::time::Duration;

use anyhow::{bail, Context, Result};

use clean_mathverse::coq::alpha::{CoqImporter, Sexp};
use clean_mathverse::shard::ShardWriter;

use crate::listing::{self, Candidate};
use crate::recon::{self, is_path_atom, DumpNameIndex, FormEntry, NameScope, RunOverlay};
use crate::report::{Counts, ModuleMeta, SkipEntry, Toolchain, ValidateStats};
use crate::sertop::{QueryObj, Sertop, SertopErr};
use crate::sexp_io::quote_string;
use crate::{emit, report};

/// Give up on a module's remaining names after this many CONSECUTIVE
/// failed candidates (each failure = one sertop restart). A single poison
/// declaration (a term sertop crashes or times out printing) costs one
/// restart and one counted skip — the module CONTINUES with the next name.
/// Only an unbroken run of failures this long (the module environment itself
/// is broken — e.g. `require` fails on every respawn) abandons the tail.
/// The historical global cap of 3 condemned entire module tails to
/// "sertop-restarts-exhausted" collateral skips: one poison name in
/// mathcomp's `order` abandoned ~1,700 dumpable declarations.
const MAX_CONSECUTIVE_FAILURES: u32 = 20;

/// Absolute safety net on restarts per module (each restart re-spawns
/// sertop and re-`require`s the module — expensive but bounded by the
/// number of genuinely-poison declarations, which measurement shows is
/// small). Prevents a pathological module from thrashing forever.
const MAX_TOTAL_RESTARTS: u32 = 500;

pub struct DumpConfig {
    pub sertop_path: std::path::PathBuf,
    pub timeout: Duration,
    pub validate: bool,
    pub toolchain: Toolchain,
}

/// Lazily-(re)spawned sertop session bound to one module.
struct Session<'a> {
    cfg: &'a DumpConfig,
    module: &'a str,
    client: Option<Sertop>,
    restarts: u32,
    /// Once `Require Import <module>` has raised a notation-grammar clash
    /// (poly's "NotationLevelMismatch", presentation's custom-entry double
    /// registration), every (re)spawn loads with plain `Require` instead —
    /// in a FRESH process, since the failed Import leaves grammar
    /// side-effects half-applied in the old one.
    plain_require: bool,
}

impl Session<'_> {
    fn client(&mut self) -> Result<&mut Sertop, SertopErr> {
        if self.client.is_none() {
            let mut c = Sertop::spawn(&self.cfg.sertop_path, self.cfg.timeout)?;
            if self.plain_require {
                c.require_plain(self.module)?;
            } else {
                match c.require(self.module) {
                    Ok(()) => {}
                    Err(SertopErr::Exn(_)) => {
                        // Notation-grammar clash during Import: retry from a
                        // clean process with plain `Require` (fully-qualified
                        // queries do not need the notations in scope).
                        drop(c);
                        self.plain_require = true;
                        c = Sertop::spawn(&self.cfg.sertop_path, self.cfg.timeout)?;
                        c.require_plain(self.module)?;
                    }
                    Err(e) => return Err(e),
                }
            }
            self.client = Some(c);
        }
        match self.client.as_mut() {
            Some(c) => Ok(c),
            None => Err(SertopErr::Closed),
        }
    }

    /// Kill the current process (after a timeout/stream error).
    fn reset(&mut self) {
        self.client = None; // Drop kills the child
        self.restarts += 1;
    }
}

/// Dump one module end-to-end; writes `<sexp_path>` and `<meta_path>`.
pub fn dump_module(
    cfg: &DumpConfig,
    module: &str,
    sexp_path: &Path,
    meta_path: &Path,
) -> Result<ModuleMeta> {
    let mut session = Session {
        cfg,
        module,
        client: None,
        restarts: 0,
        plain_require: false,
    };
    let mut counts = Counts::default();

    // Enumerate declarations via `Print Module`, recursing into bodyless
    // nested modules (Print Module does not expand them — verified live on
    // Coq.Arith.PeanoNat, whose `Module Nat` prints as a name-only line).
    let mut candidates: Vec<Candidate> = Vec::new();
    let mut submodules: Vec<String> = Vec::new();
    let mut to_print: Vec<String> = vec![module.to_string()];
    let mut printed: HashSet<String> = HashSet::new();
    while let Some(path) = to_print.pop() {
        if !printed.insert(path.clone()) {
            continue;
        }
        let text = match print_module(&mut session, &path) {
            Ok(t) => t,
            Err(e) => {
                if path == module {
                    // The root module must enumerate; fail the whole dump.
                    return Err(e.context(format!("Print Module {module}")));
                }
                counts.skipped.push(SkipEntry {
                    name: path.clone(),
                    reason: format!("print-submodule-failed: {e:#}"),
                });
                continue;
            }
        };
        let parsed = listing::parse_module_listing(&text, &path);
        candidates.extend(parsed.candidates);
        // Functor modules: members are functor-scoped (`MPbound`), never
        // global kernel constants — one counted skip per functor, not one
        // failed query per member.
        for f in parsed.functors {
            counts.skipped.push(SkipEntry {
                name: f,
                reason: "functor-module: members are functor-scoped (MPbound), \
                         not global kernel constants"
                    .to_string(),
            });
        }
        for sm in parsed.submodules {
            submodules.push(sm.clone());
            to_print.push(sm);
        }
    }

    let ts = report::unix_ts();
    let mut buf = String::new();
    buf.push_str("; mathverse coq dump v1 (importer forms: CoqConstant/CoqAxiom/CoqInductive)\n");
    buf.push_str(&format!("; module: {module}\n"));
    buf.push_str(&format!(
        "; toolchain: coq {} / sertop {}\n; generated-unix-ts: {ts}\n",
        cfg.toolchain.coq, cfg.toolchain.serapi
    ));

    let mut minds_seen: HashSet<String> = HashSet::new();
    let mut names_seen: HashSet<String> = HashSet::new();
    let mut exhausted = false;
    let mut consecutive_failures: u32 = 0;
    // Cross-module name index for the salvage's constant-atom arity
    // resolution. Loaded lazily on the FIRST salvage that needs it (a
    // sequential scan of the output directory's dumps), so crash-free
    // modules never pay for it.
    let out_dir = sexp_path.parent().unwrap_or_else(|| Path::new("."));
    let name_index: std::cell::OnceCell<DumpNameIndex> = std::cell::OnceCell::new();
    // Crash-salvaged names queued for the END-OF-MODULE reconstruction phase
    // (see `run_reconstruction`): the full-parts retry runs after the main
    // loop so it can resolve pretty-printed references against EVERYTHING the
    // module emitted (mathcomp's crash families print in reverse dependency
    // order — `ClosedField.class_of` references `Field.class_of` before the
    // latter's own candidate is reached).
    let mut recon_retries: Vec<ReconRetry> = Vec::new();
    for cand in &candidates {
        if !names_seen.insert(cand.qualified.clone()) {
            continue;
        }
        if exhausted {
            counts.skipped.push(SkipEntry {
                name: cand.qualified.clone(),
                reason: "sertop-restarts-exhausted".to_string(),
            });
            continue;
        }
        let buf_len_before = buf.len();
        match dump_candidate(&mut session, cand, &mut minds_seen, &mut buf, &mut counts) {
            Ok(()) => {
                consecutive_failures = 0;
            }
            Err(e) => {
                session.reset();
                // POISON-VALUE SALVAGE: sertop 8.20 SEGFAULTS serializing the
                // raw Constr of some giant Hierarchy-Builder terms (the value
                // pretty-prints fine; the sexp serializer dies mid-answer,
                // measured exit 139). The TYPE often still serializes — emit a
                // statement-only `CoqAxiom` so downstream references RESOLVE
                // (an absent declaration taints every dependent at verify
                // time; the missing `Finite.class_of`-family Hierarchy-Builder
                // RECORDS alone chained ~15k mathcomp failures). Honest
                // accounting: counted as an axiom plus a note; never a value
                // claim. Guarded on ZERO EMISSION so far for this candidate —
                // exact, unlike the earlier keyword-hint gate: a crash after a
                // partial (CoqInductive …) write is never papered over with a
                // same-named axiom next to a partial block, while a crash in
                // the very first query (where inductive-shaped candidates die
                // serializing the MInd answer) salvages the small arity type.
                let mut retry_kind: Option<ReconKind> = None;
                let salvaged = buf.len() == buf_len_before
                    && matches!(
                        salvage_type_only(
                            &mut session,
                            cand,
                            &mut buf,
                            &mut counts,
                            name_index.get_or_init(|| DumpNameIndex::load(out_dir)),
                            &mut retry_kind,
                        ),
                        Ok(true)
                    );
                if buf.len() == buf_len_before || salvaged {
                    if let Some(kind) = retry_kind {
                        recon_retries.push(ReconRetry {
                            name: cand.qualified.clone(),
                            kind,
                        });
                    }
                }
                if salvaged {
                    consecutive_failures = 0;
                } else {
                    counts.skipped.push(SkipEntry {
                        name: cand.qualified.clone(),
                        reason: format!("{e}"),
                    });
                    // The salvage attempt may itself have crashed the fresh
                    // session; reset again so the next candidate respawns.
                    session.reset();
                    consecutive_failures += 1;
                    if consecutive_failures >= MAX_CONSECUTIVE_FAILURES
                        || session.restarts > MAX_TOTAL_RESTARTS
                    {
                        // Mark the remainder explicitly; never drop names silently.
                        exhausted = true;
                    }
                }
            }
        }
    }

    if !recon_retries.is_empty() {
        run_reconstruction(
            &mut session,
            &recon_retries,
            name_index.get_or_init(|| DumpNameIndex::load(out_dir)),
            &mut buf,
            &mut counts,
        );
    }

    std::fs::write(sexp_path, &buf).with_context(|| format!("writing {}", sexp_path.display()))?;

    // Honest coverage measure: replay the dump through the real importer.
    let validate = if cfg.validate {
        Some(run_validation(&buf)?)
    } else {
        None
    };

    let meta = ModuleMeta {
        module: module.to_string(),
        toolchain: cfg.toolchain.clone(),
        counts,
        submodules,
        validate,
        generated_unix_ts: ts,
    };
    std::fs::write(meta_path, serde_json::to_string_pretty(&meta)?)
        .with_context(|| format!("writing {}", meta_path.display()))?;
    Ok(meta)
}

/// Run `Print Module <path>.` and return the Notice plain text; restarts the
/// session once on a sertop-level failure before giving up.
fn print_module(session: &mut Session<'_>, path: &str) -> Result<String> {
    let cmd = format!(
        "(Query () (Vernac {}))",
        quote_string(&format!("Print Module {path}."))
    );
    let mut last_err: Option<anyhow::Error> = None;
    for _ in 0..2 {
        let client = match session.client() {
            Ok(c) => c,
            Err(e) => {
                last_err = Some(anyhow::anyhow!("sertop session: {e}"));
                session.reset();
                continue;
            }
        };
        match client.command(&cmd) {
            Ok(out) => {
                if let Some(e) = out.exn {
                    bail!("raised: {e}");
                }
                return listing::extract_message_str(&out.feedback)
                    .with_context(|| format!("Print Module {path} produced no Notice text"));
            }
            Err(e) => {
                last_err = Some(anyhow::anyhow!("{e}"));
                session.reset();
            }
        }
    }
    Err(last_err.unwrap_or_else(|| anyhow::anyhow!("unreachable: no attempt made")))
}

/// Classify one candidate by live queries and append its importer form(s).
fn dump_candidate(
    session: &mut Session<'_>,
    cand: &Candidate,
    minds_seen: &mut HashSet<String>,
    buf: &mut String,
    counts: &mut Counts,
) -> Result<(), SertopErr> {
    let name = cand.qualified.as_str();
    match session.client()?.query_obj("Definition", name)? {
        QueryObj::Constr(value) => match session.client()?.query_obj("TypeOf", name)? {
            QueryObj::Constr(ty) => {
                // Instantiated-module (functor-application) members are dumped
                // VALUE-BEARING but tagged `Speculative` (the Option-B
                // re-land): the ~22 that verify KV stay KV, and a member the
                // Clean kernel cannot reduce through falls to a CLEAN type-only
                // axiom instead of the masked-failure taint the earlier
                // bare-value-bearing enumeration hit (−885 at corpus scale).
                if cand.speculative {
                    buf.push_str(&emit::render_constant_speculative(name, &ty, &value));
                } else {
                    buf.push_str(&emit::render_constant(name, &ty, &value));
                }
                counts.constants += 1;
                counts.with_value += 1;
                Ok(())
            }
            _ => {
                counts.skipped.push(SkipEntry {
                    name: name.to_string(),
                    reason: format!("typeof-failed ({})", cand.keyword),
                });
                Ok(())
            }
        },
        QueryObj::MInd(objs) => dump_inductive(session, cand, &objs, minds_seen, buf, counts),
        definition_failure @ (QueryObj::Empty | QueryObj::Exn(_) | QueryObj::Other(_)) => {
            let definition_reason = match definition_failure {
                QueryObj::Empty => "empty definition answer".to_string(),
                QueryObj::Exn(reason) => format!("definition exception: {reason}"),
                QueryObj::Other(kind) => format!("unsupported definition answer: {kind}"),
                QueryObj::Constr(_) | QueryObj::MInd(_) => unreachable!(),
            };
            // No definition object: a genuine axiom/parameter (or a
            // section-discharged alias). TypeOf decides; statement-only.
            match session.client()?.query_obj("TypeOf", name)? {
                QueryObj::Constr(ty) => {
                    buf.push_str(&emit::render_axiom(name, &ty));
                    counts.axioms += 1;
                    Ok(())
                }
                _ => {
                    counts.skipped.push(SkipEntry {
                        name: name.to_string(),
                        reason: format!(
                            "no-definition-no-typeof ({}; {definition_reason})",
                            cand.keyword
                        ),
                    });
                    Ok(())
                }
            }
        }
    }
}

/// Poison-value salvage (see the dump loop): after a `Definition` query
/// crashed sertop, ask a FRESH session for the TYPE alone and emit a
/// statement-only `CoqAxiom` when it serializes. Returns `Ok(true)` on an
/// emission, `Ok(false)` when the type query answered but with no usable
/// Constr (caller records the original skip), `Err` when the type query
/// crashed the session too (the type shares the poison subterm).
///
/// `retry` reports what the END-OF-MODULE reconstruction phase should attempt
/// for this name (see `run_reconstruction`): `Constant` when the type query
/// itself is poisoned (a `Proj`-laced type the `Check` pretty-print can still
/// recover), `Inductive` when `TypeOf` answered EMPTY (the record/inductive
/// shape whose MInd payload crashed — reconstructible from parts).
fn salvage_type_only(
    session: &mut Session<'_>,
    cand: &Candidate,
    buf: &mut String,
    counts: &mut Counts,
    index: &DumpNameIndex,
    retry: &mut Option<ReconKind>,
) -> Result<bool, SertopErr> {
    let name = cand.qualified.as_str();
    // Default set BEFORE the query: a crash below leaves the constant retry.
    *retry = Some(ReconKind::Constant);
    match session.client()?.query_obj("TypeOf", name)? {
        QueryObj::Constr(ty) => {
            // Full real type emitted — nothing left to recover. The inline
            // StandIn marker records that this axiom stands in for a value
            // the Coq kernel checked (see `emit::render_axiom_standin`).
            *retry = None;
            buf.push_str(&emit::render_axiom_standin(name, &ty));
            counts.axioms += 1;
            counts.notes.push(format!(
                "{name}: value raw-Constr serialization crashed sertop; \
                 emitted statement-only axiom (type serialized)"
            ));
            Ok(true)
        }
        // `TypeOf` answers EMPTY for inductive-shaped names (records/
        // inductives whose giant MInd answer crashed the Definition query —
        // the Hierarchy-Builder `class_of`/`type` records that chained ~15k
        // mathcomp failures). The vernac `Check <name>.` still pretty-prints
        // the ARITY, and record arities are simple non-dependent telescopes
        // over sorts and other already-dumped types (`Type -> Type`,
        // `ssralg.GRing.Ring.type -> Type -> Type`): parse that shape and
        // emit a statement-only axiom so downstream REFERENCES resolve. A
        // dependent that projects/matches on the record still fails (cleanly
        // — the stand-in is value-less), but plain type references verify.
        // Either way the name queues for the RECONSTRUCTION phase, which
        // tries to recover the REAL inductive (ctor + kernel recursor) from
        // parts once the whole module has emitted.
        QueryObj::Empty => {
            *retry = Some(ReconKind::Inductive);
            match check_sort_arrow_arity(session, name, index)? {
                Some(arity) => {
                    // Inline StandIn marker: a record/inductive with real
                    // checked structure in Coq, salvaged type-only.
                    buf.push_str(&emit::render_axiom_standin(name, &arity));
                    counts.axioms += 1;
                    counts.notes.push(format!(
                        "{name}: MInd serialization crashed sertop; emitted \
                         statement-only axiom from the `Check` sort-arrow arity"
                    ));
                    Ok(true)
                }
                None => Ok(false),
            }
        }
        _ => {
            *retry = None; // the name is not a plain constant/inductive
            Ok(false)
        }
    }
}

// ---------------------------------------------------------------------------
// End-of-module RECONSTRUCTION phase: real inductives (and Proj-laced
// constant types) recovered from pretty-printed parts.
// ---------------------------------------------------------------------------

/// What the reconstruction phase should attempt for a crash-salvaged name.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ReconKind {
    /// `TypeOf` answered EMPTY: an inductive/record whose MInd payload
    /// crashed the serializer — reconstruct the REAL inductive from parts.
    Inductive,
    /// `TypeOf` itself crashed (a `Proj`-laced type): recover a statement-
    /// only axiom from the flagged `Check` pretty-print.
    Constant,
}

/// A crash-salvaged name queued for the reconstruction phase.
struct ReconRetry {
    name: String,
    kind: ReconKind,
}

/// Reconstruction driver: FIXPOINT retry over the module's crash-salvaged
/// names, run AFTER the main dump loop.
///
/// Why a fixpoint at end-of-module: mathcomp's crash families enumerate in
/// REVERSE dependency order (`ClosedField.class_of` before `Field.class_of`),
/// and a pretty-print-parsed reference bakes in the referenced name's CURRENT
/// kind (stand-in constant vs real inductive). Each attempt therefore DEFERS
/// while its text references a still-pending sibling, and each pass emits the
/// families whose references are final — one dependency-chain level per pass;
/// a pass without progress stops (cycles and unrecoverable names fail closed,
/// keeping their inline type-only stand-ins).
///
/// Emissions APPEND to the dump: a reconstructed family's earlier type-only
/// `CoqAxiom` stand-in stays in place. The two never collide — the inductive
/// defines the `<name>.0` spelling family, the axiom defines `<name>` — and
/// dependent references choose by kind (`(Ind ...)` lowers to `<name>.0`,
/// `(Const ...)` to `<name>`), so raw dependents that were dumped against
/// either kind keep resolving. The kernel replay arbitrates every
/// reconstruction at verify time (a wrong part falls back to the checked
/// family stand-in — exactly today's behavior).
fn run_reconstruction(
    session: &mut Session<'_>,
    retries: &[ReconRetry],
    file_index: &DumpNameIndex,
    buf: &mut String,
    counts: &mut Counts,
) {
    let mut overlay: RunOverlay = recon::scan_buffer(buf);
    let mut pending: Vec<&ReconRetry> = retries.iter().collect();
    loop {
        let pending_names: HashSet<&str> = pending.iter().map(|r| r.name.as_str()).collect();
        let mut progressed = false;
        let mut still: Vec<&ReconRetry> = Vec::new();
        for retry in pending {
            if session.restarts > MAX_TOTAL_RESTARTS {
                still.push(retry);
                continue;
            }
            let outcome = match retry.kind {
                ReconKind::Inductive => try_reconstruct_inductive(
                    session,
                    &retry.name,
                    file_index,
                    &mut overlay,
                    &pending_names,
                    buf,
                    counts,
                ),
                ReconKind::Constant => try_reconstruct_constant(
                    session,
                    &retry.name,
                    file_index,
                    &mut overlay,
                    &pending_names,
                    buf,
                    counts,
                ),
            };
            match outcome {
                Ok(true) => progressed = true,
                Ok(false) => still.push(retry),
                Err(_) => {
                    // The probe crashed the session; respawn for the next one.
                    session.reset();
                    still.push(retry);
                }
            }
        }
        pending = still;
        if !progressed || pending.is_empty() {
            break;
        }
    }
    for retry in pending {
        counts.notes.push(format!(
            "{}: reconstruction-from-parts failed (fail closed; the inline \
             type-only stand-in, if any, is kept)",
            retry.name
        ));
    }
}

/// Reconstruct one crashed inductive from parts: ctor names + parameter count
/// from `Print`, arity + ctor types from raw `TypeOf` where it serializes
/// (real universe payloads) else from the flagged `Check` pretty-print parsed
/// into the importer dialect. Every unrecognized shape returns `Ok(false)`
/// (the family keeps its stand-in); `Err` = the session died (caller resets).
#[allow(clippy::too_many_arguments)]
fn try_reconstruct_inductive(
    session: &mut Session<'_>,
    name: &str,
    file_index: &DumpNameIndex,
    overlay: &mut RunOverlay,
    pending: &HashSet<&str>,
    buf: &mut String,
    counts: &mut Counts,
) -> Result<bool, SertopErr> {
    let Some(print_text) = query_vernac_notice(session, &format!("Print {name}."))? else {
        return Ok(false);
    };
    let Some(header) = recon::parse_print_inductive(&print_text) else {
        return Ok(false);
    };
    if name != header.short_name && !name.ends_with(&format!(".{}", header.short_name)) {
        return Ok(false); // Print answered about something else entirely
    }
    // Arity: parse the flagged `Check` type. Defer while it references a
    // still-pending sibling (its kind is not final yet).
    set_pp_flags(session)?;
    let Some(arity_text) = check_type_text(session, name)? else {
        return Ok(false);
    };
    let arity = {
        let scope = NameScope {
            file: file_index,
            run: overlay,
            self_ind: Some(name),
        };
        if references_pending(&arity_text, &scope, pending, name) {
            return Ok(false);
        }
        let Some(arity) = recon::parse_check_type(&arity_text, &scope) else {
            return Ok(false);
        };
        arity
    };
    let (n_prods, sort_codomain) = recon::arity_shape(&arity);
    if !sort_codomain || n_prods < header.num_params {
        return Ok(false);
    }
    // Constructor types. Constructors live in the module namespace.
    let modpath = name.rsplit_once('.').map_or("", |(m, _)| m);
    let mut ctors: Vec<(String, Sexp)> = Vec::new();
    for cname in &header.ctor_names {
        let ctor_q = format!("{modpath}.{cname}");
        // Raw TypeOf first — the faithful payload (real universes), and it
        // references siblings by their TRUE kind, so no deferral is needed.
        // Measured: 12 of the 53 mathcomp crash-family ctor types serialize;
        // the other 41 SEGFAULT the session on a Proj node and fall back to
        // the flagged pretty-print parse below.
        let raw = match session.client()?.query_obj("TypeOf", &ctor_q) {
            Ok(QueryObj::Constr(ty)) => Some(ty),
            Ok(_) => None,
            Err(_) => {
                session.reset();
                None
            }
        };
        let ty = match raw {
            Some(ty) => ty,
            None => {
                set_pp_flags(session)?;
                let Some(text) = check_type_text(session, &ctor_q)? else {
                    return Ok(false);
                };
                let scope = NameScope {
                    file: file_index,
                    run: overlay,
                    self_ind: Some(name),
                };
                if references_pending(&text, &scope, pending, name) {
                    return Ok(false);
                }
                match recon::parse_check_type(&text, &scope) {
                    Some(ty) => ty,
                    None => return Ok(false),
                }
            }
        };
        ctors.push((ctor_q, ty));
    }
    buf.push_str(&emit::render_inductive(
        name,
        0,
        &arity,
        header.num_params,
        &ctors,
    ));
    counts.inductives += 1;
    counts.ctors += ctors.len() as u32;
    if matches!(header.keyword.as_str(), "Record" | "Structure" | "Class") {
        counts.records += 1;
    }
    if header.prim_record {
        counts.prim_records += 1;
    }
    counts.notes.push(format!(
        "{name}: MInd serialization crashed sertop; reconstructed the REAL \
         inductive from parts ({} `Print` ctor name(s), {} params, ctor types \
         via raw TypeOf or flagged `Check` parse) — kernel replay arbitrates \
         at verify time",
        ctors.len(),
        header.num_params,
    ));
    counts.skipped.retain(|s| s.name != name);
    overlay.insert(name.to_string(), FormEntry::Ind(0));
    for (j, (ctor_q, _)) in ctors.iter().enumerate() {
        overlay.insert(
            ctor_q.clone(),
            FormEntry::Ctor {
                block: name.to_string(),
                block_idx: 0,
                ctor_idx: j as u32,
            },
        );
    }
    Ok(true)
}

/// Recover a statement-only axiom for a constant whose TYPE query crashes
/// (a `Proj`-laced type): parse the flagged `Check` pretty-print. Defers
/// while the text references a still-pending sibling.
fn try_reconstruct_constant(
    session: &mut Session<'_>,
    name: &str,
    file_index: &DumpNameIndex,
    overlay: &mut RunOverlay,
    pending: &HashSet<&str>,
    buf: &mut String,
    counts: &mut Counts,
) -> Result<bool, SertopErr> {
    set_pp_flags(session)?;
    let Some(text) = check_type_text(session, name)? else {
        return Ok(false);
    };
    let ty = {
        let scope = NameScope {
            file: file_index,
            run: overlay,
            self_ind: None,
        };
        if references_pending(&text, &scope, pending, name) {
            return Ok(false);
        }
        let Some(ty) = recon::parse_check_type(&text, &scope) else {
            return Ok(false);
        };
        ty
    };
    // Inline StandIn marker: crash-salvaged constant (see
    // `emit::render_axiom_standin`).
    buf.push_str(&emit::render_axiom_standin(name, &ty));
    counts.axioms += 1;
    counts.notes.push(format!(
        "{name}: value AND type raw serialization crashed sertop (Proj-laced \
         type); emitted statement-only axiom parsed from the flagged `Check` \
         pretty-print"
    ));
    counts.skipped.retain(|s| s.name != name);
    overlay.insert(name.to_string(), FormEntry::Const);
    Ok(true)
}

/// True when a pretty-printed type mentions a name that is still PENDING in
/// the reconstruction fixpoint (its final kind — stand-in constant vs real
/// inductive — is not decided yet), excluding the self-reference.
fn references_pending(
    text: &str,
    scope: &NameScope<'_>,
    pending: &HashSet<&str>,
    self_name: &str,
) -> bool {
    recon::referenced_names(text, scope)
        .iter()
        .any(|n| n != self_name && pending.contains(n.as_str()))
}

/// Run a read-only vernacular under `(Query () (Vernac ...))` and return the
/// Notice text.
fn query_vernac_notice(session: &mut Session<'_>, stmt: &str) -> Result<Option<String>, SertopErr> {
    let cmd = format!("(Query () (Vernac {}))", quote_string(stmt));
    let out = session.client()?.command(&cmd)?;
    if out.exn.is_some() {
        return Ok(None);
    }
    Ok(listing::extract_message_str(&out.feedback))
}

/// `Check <name>.` and return the text after the `\n     : ` separator.
fn check_type_text(session: &mut Session<'_>, name: &str) -> Result<Option<String>, SertopErr> {
    let Some(text) = query_vernac_notice(session, &format!("Check {name}."))? else {
        return Ok(None);
    };
    let Some(colon) = text.find("\n     : ") else {
        return Ok(None);
    };
    Ok(Some(text[colon + "\n     : ".len()..].to_string()))
}

/// Make the pretty-printer notation-free, implicit-arg-explicit, and
/// primitive-projection-parameter-explicit — the shape `parse_check_type`
/// recognizes. Issued before EVERY parse-route `Check` because a crash
/// respawn loses the document state; goes through `Add`+`Exec` (a
/// query-context vernac's side effects do not reliably persist).
fn set_pp_flags(session: &mut Session<'_>) -> Result<(), SertopErr> {
    session
        .client()?
        .execute("Set Printing All. Set Printing Primitive Projection Parameters.")
}

/// Run `Check <name>.` and parse the printed type as a NON-DEPENDENT ARROW
/// telescope whose parts are sorts (`Type`/`Set`/`Prop`) or semi-qualified
/// CONSTANT ATOMS resolvable against the already-dumped names
/// (`ssralg.GRing.Ring.type -> Type -> Type`), returning the importer-DIALECT
/// arity sexp (`(Prod _ (Ind mathcomp.algebra.ssralg.GRing.Ring.type 0)
/// (Prod _ (Sort (Type 1)) (Sort (Type 1))))`). The CODOMAIN must be a sort
/// (these stand-ins are type formers). Returns `Ok(None)` for anything richer
/// (dependent binders, parentheses, unresolvable or ambiguous atoms) — fail
/// closed, only the exactly-recognized shape is synthesized. `Type` maps to
/// `(Sort (Type 1))`, matching the importer's named-level collapse convention
/// for a bare `Type@{…}` occurrence.
fn check_sort_arrow_arity(
    session: &mut Session<'_>,
    name: &str,
    index: &DumpNameIndex,
) -> Result<Option<Sexp>, SertopErr> {
    let cmd = format!(
        "(Query () (Vernac {}))",
        quote_string(&format!("Check {name}."))
    );
    let out = session.client()?.command(&cmd)?;
    if out.exn.is_some() {
        return Ok(None);
    }
    let Some(text) = listing::extract_message_str(&out.feedback) else {
        return Ok(None);
    };
    // Shape: "<short.name>\n     : <type>" — take everything after the first
    // top-level " : " separator line.
    let Some(colon) = text.find("\n     : ") else {
        return Ok(None);
    };
    let ty_text = &text[colon + "\n     : ".len()..];
    let no_aliases = std::collections::HashMap::new();
    if let Some(arity) = parse_check_arity(ty_text, index, &no_aliases) {
        return Ok(Some(arity));
    }
    // NOTATION rung: inside the defining module `Check` prints structure
    // abbreviations (`ringType`, not `GRing.Ring.type` — measured live on
    // ssralg's own Lmodule/Lalgebra `class_of` family), which no dumped name
    // can suffix-match. `Print <atom>.` answers `Notation <atom> := <target>`
    // for such an abbreviation; resolve each unresolved atom ONE level through
    // it (a parameterized or non-path target fails closed) and re-parse.
    let mut aliases = std::collections::HashMap::new();
    for atom in unresolved_path_atoms(ty_text, index) {
        if let Some(target) = print_notation_target(session, &atom)? {
            if index.resolve(&target).is_some() {
                aliases.insert(atom, target);
            }
        }
    }
    if aliases.is_empty() {
        return Ok(None);
    }
    Ok(parse_check_arity(ty_text, index, &aliases))
}

/// The distinct path atoms of an arrow telescope that are neither sorts nor
/// resolvable against the dumped-name index (candidates for the notation
/// rung of [`check_sort_arrow_arity`]).
fn unresolved_path_atoms(ty_text: &str, index: &DumpNameIndex) -> Vec<String> {
    let joined = ty_text.split_whitespace().collect::<Vec<_>>().join(" ");
    let mut atoms = Vec::new();
    for part in joined.split("->") {
        let atom = part.trim();
        if !matches!(atom, "Type" | "Set" | "Prop")
            && is_path_atom(atom)
            && index.resolve(atom).is_none()
            && !atoms.iter().any(|a| a == atom)
        {
            atoms.push(atom.to_string());
        }
    }
    atoms
}

/// Run `Print <atom>.` and, when the answer is a notation ABBREVIATION with a
/// bare path-atom target (`Notation ringType := GRing.Ring.type`), return the
/// target. Parameterized notations, application bodies, genuine constants,
/// missing names — all `None` (fail closed). Session-level failures propagate
/// like every other salvage query (the caller resets and skips).
fn print_notation_target(
    session: &mut Session<'_>,
    atom: &str,
) -> Result<Option<String>, SertopErr> {
    let cmd = format!(
        "(Query () (Vernac {}))",
        quote_string(&format!("Print {atom}."))
    );
    let out = session.client()?.command(&cmd)?;
    if out.exn.is_some() {
        return Ok(None);
    }
    let Some(text) = listing::extract_message_str(&out.feedback) else {
        return Ok(None);
    };
    let Some(rest) = text
        .strip_prefix("Notation ")
        .and_then(|r| r.trim_start().strip_prefix(atom))
        .and_then(|r| r.trim_start().strip_prefix(":="))
    else {
        return Ok(None);
    };
    // The target runs to the first whitespace/newline (the record body or
    // argument scopes follow on later lines).
    let target = rest
        .split_whitespace()
        .next()
        .unwrap_or_default()
        .to_string();
    if is_path_atom(&target) {
        Ok(Some(target))
    } else {
        Ok(None)
    }
}

/// Pure parsing half of [`check_sort_arrow_arity`]: parse a `Check`-printed
/// type into the importer-dialect arity sexp, or `None` (fail closed).
/// `aliases` maps notation abbreviations to their resolved path atoms (the
/// notation rung); pass an empty map for the pure first attempt.
fn parse_check_arity(
    ty_text: &str,
    index: &DumpNameIndex,
    aliases: &std::collections::HashMap<String, String>,
) -> Option<Sexp> {
    // Collapse the pretty-printer's line wrapping so a long telescope parses
    // like a single-line one.
    let ty_text = ty_text.split_whitespace().collect::<Vec<_>>().join(" ");
    let mut parts = Vec::new();
    for part in ty_text.split("->") {
        let (node, is_sort) = match part.trim() {
            "Type" => (
                Sexp::List(vec![
                    Sexp::Atom("Sort".to_string()),
                    Sexp::List(vec![
                        Sexp::Atom("Type".to_string()),
                        Sexp::Atom("1".to_string()),
                    ]),
                ]),
                true,
            ),
            "Set" => (
                Sexp::List(vec![
                    Sexp::Atom("Sort".to_string()),
                    Sexp::Atom("Set".to_string()),
                ]),
                true,
            ),
            "Prop" => (
                Sexp::List(vec![
                    Sexp::Atom("Sort".to_string()),
                    Sexp::Atom("Prop".to_string()),
                ]),
                true,
            ),
            atom if is_path_atom(atom) => {
                match index.resolve(aliases.get(atom).map_or(atom, String::as_str)) {
                    // An already-dumped inductive: reference it by the importer's
                    // inductive spelling `(Ind <fq> <idx>)`.
                    Some((fq, FormEntry::Ind(idx))) => (
                        Sexp::List(vec![
                            Sexp::Atom("Ind".to_string()),
                            Sexp::Atom(fq.to_string()),
                            Sexp::Atom(idx.to_string()),
                        ]),
                        false,
                    ),
                    // An already-dumped constant/axiom (e.g. an earlier salvage
                    // stand-in): a plain constant reference.
                    Some((fq, FormEntry::Const)) => (
                        Sexp::List(vec![
                            Sexp::Atom("Const".to_string()),
                            Sexp::Atom(fq.to_string()),
                        ]),
                        false,
                    ),
                    // Constructor entries never resolve through
                    // `DumpNameIndex::resolve`; unresolvable or ambiguous
                    // atoms fail closed.
                    _ => return None,
                }
            }
            _ => return None, // dependent binders / parentheses: fail closed
        };
        parts.push((node, is_sort));
    }
    let (arity, codomain_is_sort) = parts.pop()?;
    if !codomain_is_sort {
        // A stand-in must be a TYPE FORMER; a constant-atom codomain is not
        // an arity we can vouch for.
        return None;
    }
    let mut arity = arity;
    for (dom, _) in parts.into_iter().rev() {
        arity = Sexp::List(vec![
            Sexp::Atom("Prod".to_string()),
            Sexp::Atom("_".to_string()),
            dom,
            arity,
        ]);
    }
    Some(arity)
}

/// Emit a mutual inductive: `(CoqInductive ...)` per Finite block, or
/// statement-only `CoqAxiom` entries (named by the `<base>.<block>[.<k>]`
/// shard convention) for coinductive/bifinite blocks — counted, never silent.
fn dump_inductive(
    session: &mut Session<'_>,
    cand: &Candidate,
    objs: &[Sexp],
    minds_seen: &mut HashSet<String>,
    buf: &mut String,
    counts: &mut Counts,
) -> Result<(), SertopErr> {
    let info = match emit::parse_mind(objs) {
        Ok(i) => i,
        Err(reason) => {
            counts.skipped.push(SkipEntry {
                name: cand.qualified.clone(),
                reason: format!("mind-parse: {reason}"),
            });
            return Ok(());
        }
    };
    let base = info.base.clone().unwrap_or_else(|| cand.qualified.clone());
    if !minds_seen.insert(base.clone()) {
        return Ok(()); // another candidate of the same mutual block
    }
    // Constructors live in the module namespace, not under the type name.
    let modpath = base.rsplit_once('.').map_or("", |(m, _)| m);
    if info.prim_record {
        counts.prim_records += 1;
        // Accessors of a primitive record are `Proj`-term-valued; sertop 8.20
        // segfaults serializing `Proj`, so their bodies may fail to dump.
        // Informational (the record type + ctor below dump normally).
        counts.notes.push(format!(
            "{base}: PrimRecord — accessor bodies are Proj-valued and may not \
             dump (sertop 8.20 Proj serialization limitation)"
        ));
    }
    // Records/classes (BiFinite) are ordinary non-recursive kernel inductives
    // and are emitted as `CoqInductive`; only genuinely COINDUCTIVE blocks
    // (CoFinite) are statement-only axiomatized (their non-well-founded
    // semantics has no sound inductive replay).
    if info.finite == "BiFinite" {
        counts.records += 1;
    }
    let axiomatize = info.finite == "CoFinite";
    for (block, packet) in info.packets.iter().enumerate() {
        let block = block as u32;
        let block_name = format!("{base}.{block}");
        let (mut arity, template_collapsed) = match &packet.arity {
            Ok((a, t)) => (a.clone(), *t),
            Err(reason) => {
                counts.skipped.push(SkipEntry {
                    name: block_name,
                    reason: format!("packet {} arity: {reason}", packet.typename),
                });
                continue;
            }
        };
        // Constructor types via TypeOf (closed, Ind-referenced); fall back to
        // `mind_user_lc` only for single-block inductives (mutual user_lc may
        // carry cross-block Rels the importer cannot resolve).
        let mut ctors: Vec<(String, Sexp)> = Vec::new();
        let mut ctor_failure: Option<String> = None;
        for (k, cname) in packet.consnames.iter().enumerate() {
            let ctor_qualified = format!("{modpath}.{cname}");
            match session.client()?.query_obj("TypeOf", &ctor_qualified)? {
                QueryObj::Constr(ty) => ctors.push((ctor_qualified, ty)),
                _ => {
                    if info.ntypes == 1 {
                        if let Some(ty) = packet.user_lc.get(k) {
                            ctors.push((ctor_qualified, ty.clone()));
                            continue;
                        }
                    }
                    ctor_failure = Some(format!(
                        "packet {} ctor-typeof-failed: {ctor_qualified}",
                        packet.typename
                    ));
                    break;
                }
            }
        }
        if let Some(reason) = ctor_failure {
            counts.skipped.push(SkipEntry {
                name: block_name,
                reason,
            });
            continue;
        }
        // Arity-reduction safety guard. `packet_arity` emits Coq's REDUCED
        // arity (sort-ending, indices exposed) for a `RegularArity` family,
        // which is correct only when every constructor concludes directly in
        // the inductive. When a constructor concludes through a definitional
        // abbreviation — a `(Const ...)` head, e.g. `Image.Im_intro`'s
        // `In V (Im ...) (f x)` — the importer buckets it under the wrong owner
        // and the reduced arity would import the family as a WRONG
        // zero-constructor inductive, breaking its dependent lemmas. Fall back
        // to the raw `mind_user_arity` for such families, keeping the
        // pre-reduction behavior (arity does not end in a sort -> axiomatized),
        // byte-identical to the baseline. Families whose constructors conclude
        // in the inductive (`clos_refl_sym_trans`, records, …) keep the reduced
        // arity and import correctly.
        if let Some(raw) = &packet.user_arity {
            if !ctors
                .iter()
                .all(|(_, ty)| emit::ctor_conclusion_has_inductive_head(ty))
            {
                arity = raw.clone();
            }
        }
        if template_collapsed {
            counts.template_collapsed += 1;
        }
        if axiomatize {
            // Coinductive / bifinite: statement-only axioms under the shard
            // naming convention so `(Ind ...)`/`(Construct ...)` references
            // in other terms still resolve.
            buf.push_str(&emit::render_axiom(&block_name, &arity));
            counts.axioms += 1;
            for (k, (_, cty)) in ctors.iter().enumerate() {
                buf.push_str(&emit::render_axiom(&format!("{block_name}.{k}"), cty));
                counts.axioms += 1;
            }
            counts.coinductive_axiomatized += 1;
        } else {
            buf.push_str(&emit::render_inductive(
                &base,
                block,
                &arity,
                info.nparams,
                &ctors,
            ));
            counts.inductives += 1;
            counts.ctors += ctors.len() as u32;
        }
    }
    Ok(())
}

fn run_validation(content: &str) -> Result<ValidateStats> {
    let mut writer = ShardWriter::new();
    let stats = CoqImporter
        .import_sexp(content, &mut writer)
        .map_err(|e| anyhow::anyhow!("validation import failed: {e}"))?;
    Ok(ValidateStats {
        total: stats.total,
        translated: stats.translated,
        axiomatized: stats.axiomatized,
        skipped: stats.skipped,
    })
}

#[cfg(test)]
mod check_arity_tests {
    use super::*;
    use clean_mathverse::coq::alpha::parse_sexp;

    fn index() -> DumpNameIndex {
        DumpNameIndex::from_entries(vec![
            ("mathcomp.algebra.ssralg.GRing.Ring.type", FormEntry::Ind(0)),
            (
                "mathcomp.ssreflect.fintype.Finite.class_of",
                FormEntry::Const,
            ),
            // Two names sharing the suffix `dup.name`: ambiguous on purpose.
            ("a.dup.name", FormEntry::Const),
            ("b.dup.name", FormEntry::Const),
        ])
    }

    /// The original pure sort telescope parses byte-identically to before
    /// the constant-atom extension (no index consultation).
    #[test]
    fn test_parse_check_arity_pure_sort_telescope_unchanged() {
        let got = parse_check_arity("Type -> Type", &index(), &Default::default())
            .expect("sort telescope parses");
        let want = parse_sexp("(Prod _ (Sort (Type 1)) (Sort (Type 1)))").unwrap();
        assert_eq!(got, want);
    }

    /// The measured `Vector.class_of` shape: a semi-qualified inductive atom
    /// resolves by unique suffix to the `(Ind <fq> <idx>)` spelling, and the
    /// pretty-printer's line wrapping collapses.
    #[test]
    fn test_parse_check_arity_resolves_inductive_atom_by_suffix() {
        let got = parse_check_arity(
            "ssralg.GRing.Ring.type ->\n     Type -> Type",
            &index(),
            &Default::default(),
        )
        .expect("constant-atom telescope parses");
        let want = parse_sexp(
            "(Prod _ (Ind mathcomp.algebra.ssralg.GRing.Ring.type 0) \
              (Prod _ (Sort (Type 1)) (Sort (Type 1))))",
        )
        .unwrap();
        assert_eq!(got, want);
    }

    /// A constant/axiom hit (e.g. an earlier salvage stand-in) resolves to a
    /// plain `(Const <fq>)` reference.
    #[test]
    fn test_parse_check_arity_resolves_constant_atom() {
        let got = parse_check_arity(
            "fintype.Finite.class_of -> Prop",
            &index(),
            &Default::default(),
        )
        .expect("constant-atom telescope parses");
        let want =
            parse_sexp("(Prod _ (Const mathcomp.ssreflect.fintype.Finite.class_of) (Sort Prop))")
                .unwrap();
        assert_eq!(got, want);
    }

    /// Fail-closed set: unresolvable atoms, ambiguous suffixes, dependent
    /// binders, and a non-sort codomain must all yield `None`.
    #[test]
    fn test_parse_check_arity_fails_closed() {
        let idx = index();
        assert_eq!(
            parse_check_arity("nowhere.to.be.found -> Type", &idx, &Default::default()),
            None
        );
        assert_eq!(
            parse_check_arity("dup.name -> Type", &idx, &Default::default()),
            None
        );
        assert_eq!(
            parse_check_arity("forall (T : Type), T -> Type", &idx, &Default::default()),
            None
        );
        assert_eq!(
            parse_check_arity("Type -> ssralg.GRing.Ring.type", &idx, &Default::default()),
            None,
            "a constant-atom CODOMAIN is not a type-former arity"
        );
        assert_eq!(parse_check_arity("", &idx, &Default::default()), None);
    }

    /// Suffix resolution is exact-segment: `ing.type` must not match
    /// `….GRing.Ring.type` (the suffix match requires a `.` boundary and the
    /// full trailing segments).
    #[test]
    fn test_name_index_suffix_requires_segment_boundary() {
        let idx = index();
        assert_eq!(idx.resolve("ing.type"), None);
        assert_eq!(
            idx.resolve("GRing.Ring.type"),
            Some((
                "mathcomp.algebra.ssralg.GRing.Ring.type",
                &FormEntry::Ind(0)
            ))
        );
    }

    /// The notation rung's alias map substitutes an abbreviation atom
    /// (`ringType`, printed by `Check` inside the defining module) with its
    /// `Print`-resolved target before index resolution — the measured
    /// `GRing.Lmodule.class_of : ringType -> Type -> Type` shape.
    #[test]
    fn test_parse_check_arity_notation_alias_substitutes() {
        let mut aliases = std::collections::HashMap::new();
        aliases.insert("ringType".to_string(), "GRing.Ring.type".to_string());
        let got = parse_check_arity("ringType -> Type -> Type", &index(), &aliases)
            .expect("aliased telescope parses");
        let want = parse_sexp(
            "(Prod _ (Ind mathcomp.algebra.ssralg.GRing.Ring.type 0) \
              (Prod _ (Sort (Type 1)) (Sort (Type 1))))",
        )
        .unwrap();
        assert_eq!(got, want);
        // Without the alias the abbreviation stays unresolvable: fail closed.
        assert_eq!(
            parse_check_arity("ringType -> Type -> Type", &index(), &Default::default()),
            None
        );
    }
}
