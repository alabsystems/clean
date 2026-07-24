// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Shared shard-side inductive-family reconstruction for checked
//! `add_inductive` replay.
//!
//! Two verify surfaces replay inductive families from `.mathverse` shard
//! bytes through the kernel's full checked `Environment::add_inductive` path:
//! the incremental verifier ([`crate::verify::incremental`]) and the
//! graduation cake gate ([`crate::shard_verify::cake_gate`], gate v3 carried
//! inductive families). Both MUST reconstruct the [`InductiveDecl`] from
//! shard constants + typed header metadata in exactly the same way — a
//! divergence between the two reconstructions would let one surface accept
//! family bytes the other rejects (graduation-v3 design §5, adversarial
//! surface a6). This module is that single reconstruction path.

use std::collections::{HashMap, HashSet};

use clean_kernel::expr::{BinderData, BinderInfo, Expr, ExprFolder, ExprKind};
use clean_kernel::flat::{FlatExpr, FlatLevel};
use clean_kernel::inductive::{
    count_pi_args, mentions_name, Constructor, InductiveDecl, InductiveType,
};
use clean_kernel::{Environment, Name};

use crate::shard::ShardReader;
use crate::shard_reconstruct::{reconstruct_from_shard_with_level_lists, reconstruct_level_params};
use crate::types::{DeclKind, MathverseConstantHeader, NO_VALUE};
use crate::verify::incremental::{alpha_type_match_against_existing, AlphaTypeMatch};

/// Env-gated reconstruction diagnostic (WS16 triage hook). When
/// `CLEAN_WS16_DEBUG` is set, print the precise reconstruction step at which a
/// representative root returns `None`. If the value is a comma-separated list of
/// names, only those roots are printed; otherwise every root is printed. Pure
/// diagnostics: never influences the reconstruction decision.
fn ws16_dbg(reconstructed: &ReconstructedConstant, msg: impl FnOnce() -> String) {
    let Ok(filter) = std::env::var("CLEAN_WS16_DEBUG") else {
        return;
    };
    let name = reconstructed.decl_name.to_string();
    let show = filter.trim().is_empty()
        || filter
            .split(',')
            .any(|wanted| wanted.trim() == name.as_str());
    if show {
        eprintln!("WS16 build_inductive_replay_metadata[{name}]: {}", msg());
    }
}

/// A constant reconstructed from shard (or merged-arena) flat slices.
pub(crate) struct ReconstructedConstant {
    pub(crate) decl_name: Name,
    pub(crate) decl_kind: DeclKind,
    pub(crate) level_params: Vec<Name>,
    pub(crate) type_expr: Expr,
    pub(crate) value_expr: Option<Expr>,
}

/// A reconstructed family declaration plus the member names the kernel's
/// `add_inductive` deterministically generates for it.
pub(crate) struct InductiveReplayMetadata {
    pub(crate) decl: InductiveDecl,
    pub(crate) generated_names: HashSet<Name>,
}

/// Outcome of [`checked_inductive_replay_matches_shard`]: did the regenerated
/// family byte-match the shard's stored member copies?
///
/// Structured (rather than a bare bool) so callers can surface WHICH member
/// failed the match and how, instead of collapsing every family failure into a
/// generic skeleton rejection (A2-2 family-replay diagnostics). Carrying the
/// detail changes nothing about the accept/reject decision itself.
#[derive(Debug)]
pub(crate) enum ShardFamilyMatch {
    /// Every generated member matched its shard-stored copy.
    Matched,
    /// `member` failed the byte-match; `detail` says how (absent from the
    /// regenerated scratch env, level-param mismatch, or type mismatch).
    Mismatch { member: String, detail: String },
}

/// A borrowed view over a (merged or single-shard) flat arena, holding exactly
/// the slices `reconstruct_from_shard_with_level_lists` needs.
///
/// This is the unit the shared reconstruct+replay helpers operate on, so the
/// per-shard verifier (slices borrowed from a [`ShardReader`]) and the corpus
/// verifier (slices borrowed from a merged library) drive identical
/// reconstruction + kernel-replay logic and cannot diverge.
#[derive(Clone, Copy)]
pub(crate) struct ShardSlices<'a> {
    pub(crate) exprs: &'a [FlatExpr],
    pub(crate) levels: &'a [FlatLevel],
    pub(crate) strings: &'a [String],
    pub(crate) level_lists: &'a [u32],
}

impl<'a> ShardSlices<'a> {
    pub(crate) fn from_reader(reader: &'a ShardReader) -> Self {
        Self {
            exprs: &reader.exprs,
            levels: &reader.levels,
            strings: &reader.strings,
            level_lists: &reader.level_lists,
        }
    }
}

pub(crate) fn reconstruct_constant(
    name: &str,
    reader: &ShardReader,
    constant: &MathverseConstantHeader,
) -> Result<ReconstructedConstant, String> {
    reconstruct_constant_from_slices(name, ShardSlices::from_reader(reader), constant)
}

/// Reconstruct a constant's declaration (type, optional value, level params)
/// from raw flat slices. The merged-arena path passes the slice math is the
/// whole point of: a `Const`'s level arguments come from `slices.level_lists`,
/// which must already be index-remapped into the same level pool as
/// `slices.levels`.
pub(crate) fn reconstruct_constant_from_slices(
    name: &str,
    slices: ShardSlices<'_>,
    constant: &MathverseConstantHeader,
) -> Result<ReconstructedConstant, String> {
    let type_expr = reconstruct_from_shard_with_level_lists(
        slices.exprs,
        slices.levels,
        slices.strings,
        slices.level_lists,
        constant.type_idx,
    )
    .map_err(|e| format!("reconstruct type: {e}"))?;

    // A header that CLAIMS a value must yield that value: a corrupt proof-term
    // encoding is a reconstruction FAILURE (`Err`), never a silent downgrade to
    // "no value". The old `.ok()` here let a corrupt value degrade the constant
    // to a value-less reconstruction, which downstream replay then classified
    // as an axiom fallback — silently laundering a broken proof term into an
    // accepted axiom. Every caller of this function already routes `Err` to a
    // fail-closed reconstruct-failure verdict (`AddConstResult::
    // ReconstructFailed` in verify/incremental, `CakeGateViolation::
    // ReconstructFailed` in the cake gate, skip-and-report in the CLI lanes).
    let value_expr = if constant.value_idx != NO_VALUE {
        Some(
            reconstruct_from_shard_with_level_lists(
                slices.exprs,
                slices.levels,
                slices.strings,
                slices.level_lists,
                constant.value_idx,
            )
            .map_err(|e| format!("reconstruct value: {e}"))?,
        )
    } else {
        None
    };

    let level_params = reconstruct_level_params(
        slices.strings,
        constant.level_params_start,
        constant.level_params_count,
    )
    .unwrap_or_default();

    // An unknown decl_kind byte is a reconstruction FAILURE. The old
    // `unwrap_or(DeclKind::Theorem)` silently misclassified corrupt/unknown
    // kind bytes as theorems, which changes which replay path (and which trust
    // guard) the constant is routed through.
    let decl_kind = DeclKind::try_from(constant.decl_kind)
        .map_err(|byte| format!("unknown decl_kind byte {byte}"))?;

    Ok(ReconstructedConstant {
        decl_name: Name::from_string(name),
        decl_kind,
        level_params,
        type_expr,
        value_expr,
    })
}

/// One constructor's identity for [`constructor_index_for`] — enough to rebuild
/// an [`InductiveType`] member without re-reconstructing the constructor.
struct CtorEntry {
    name: Name,
    type_: Expr,
    level_params: Vec<Name>,
    return_arg_count: usize,
}

thread_local! {
    /// Per-reader memoized constructor index (owner name → its constructors),
    /// keyed by the reader's constant-buffer pointer + length. Corpus replay
    /// uses one merged reader for the whole run, so this is built once (O(N))
    /// and reused by every inductive — turning the previous O(K·N) family-
    /// association rescan (K inductives, each reconstructing all N constants)
    /// into O(N) build + O(matches) lookup. Three independently-memoized slots,
    /// indexed by [`NormMode::slot`]: baseline (Off), Shallow, and Deep synonym
    /// bucketing, each built once and reused across the replay attempts.
    static CTOR_INDEX: std::cell::RefCell<
        [Option<(usize, usize, std::rc::Rc<HashMap<Name, Vec<CtorEntry>>>)>; 3],
    > = const { std::cell::RefCell::new([None, None, None]) };
}

/// Beta-reduce a lambda telescope `value` applied to `args`, returning the
/// contracted body (extra args re-applied). `None` when `value` is not a lambda
/// or is under-applied (fewer args than binders).
fn beta_head_reduce(value: &Expr, args: &[Expr]) -> Option<Expr> {
    let mut body = value;
    let mut k = 0usize;
    while let ExprKind::Lam(_, _, inner) = body.kind() {
        body = inner.as_ref();
        k += 1;
    }
    if k == 0 || args.len() < k {
        return None;
    }
    // `instantiate_rev(vals)` substitutes `vals[0]` for BVar(0) (innermost
    // binder) … `vals[k-1]` for BVar(k-1) (outermost); application order applies
    // `args[0]` to the outermost binder, so reverse.
    let mut vals: Vec<Expr> = args[..k].to_vec();
    vals.reverse();
    let core = body.instantiate_rev(&vals);
    Some(args[k..].iter().fold(core, |f, a| Expr::app(f, a.clone())))
}

/// Per-reader synonym-resolution context: the set of inductive names + a
/// name → `reader.constants` index map, so a definitional abbreviation
/// (`In A a := A a`, `Ensemble A := A → Prop`) can be looked up and unfolded.
struct SynonymCtx {
    inductives: HashSet<Name>,
    header_idx: HashMap<Name, usize>,
}

thread_local! {
    /// Memoized [`SynonymCtx`] keyed by the reader's constant-buffer identity
    /// (same key discipline as [`CTOR_INDEX`]), so the O(N) pre-scan runs once
    /// per corpus rather than once per inductive family.
    static SYNONYM_CTX: std::cell::RefCell<Option<(usize, usize, std::rc::Rc<SynonymCtx>)>> =
        const { std::cell::RefCell::new(None) };
}

fn synonym_ctx_for(reader: &ShardReader) -> std::rc::Rc<SynonymCtx> {
    let key = reader.constants.as_ptr() as usize;
    let len = reader.constants.len();
    SYNONYM_CTX.with(|cell| {
        if let Some((k, l, ctx)) = cell.borrow().as_ref() {
            if *k == key && *l == len {
                return ctx.clone();
            }
        }
        let mut inductives = HashSet::new();
        let mut header_idx = HashMap::new();
        for (i, constant) in reader.constants.iter().enumerate() {
            let Some(nm) = reader.strings.get(constant.name_idx as usize) else {
                continue;
            };
            let name = Name::from_string(nm);
            if DeclKind::try_from(constant.decl_kind).unwrap_or(DeclKind::Theorem)
                == DeclKind::Inductive
            {
                inductives.insert(name.clone());
            }
            header_idx.insert(name, i);
        }
        let ctx = std::rc::Rc::new(SynonymCtx {
            inductives,
            header_idx,
        });
        *cell.borrow_mut() = Some((key, len, ctx.clone()));
        ctx
    })
}

/// Reconstruct the (memoized) value of a definition by name, for delta-unfolding.
fn synonym_value(
    name: &Name,
    reader: &ShardReader,
    ctx: &SynonymCtx,
    memo: &mut HashMap<Name, Option<Expr>>,
) -> Option<Expr> {
    if let Some(cached) = memo.get(name) {
        return cached.clone();
    }
    let value = ctx.header_idx.get(name).and_then(|&i| {
        let constant = &reader.constants[i];
        let nm = reader.strings.get(constant.name_idx as usize)?;
        reconstruct_constant(nm, reader, constant)
            .ok()
            .and_then(|c| c.value_expr)
    });
    memo.insert(name.clone(), value.clone());
    value
}

/// Repeatedly delta-unfold + beta-reduce the HEAD of `expr` while it is a
/// non-inductive `Const` with a value — seeing through definitional
/// abbreviations. Stops at a known inductive head, a non-`Const` head, or a
/// `Const` with no value. Bounded depth (synonyms do not chain deeply).
fn whnf_synonym_head(
    expr: &Expr,
    reader: &ShardReader,
    ctx: &SynonymCtx,
    memo: &mut HashMap<Name, Option<Expr>>,
) -> Expr {
    let mut result = expr.clone();
    for _ in 0..8 {
        let ExprKind::Const(name, _) = result.get_app_fn().kind() else {
            return result;
        };
        if ctx.inductives.contains(name) {
            return result;
        }
        let name = name.clone();
        let Some(value) = synonym_value(&name, reader, ctx, memo) else {
            return result;
        };
        // `get_app_args_iter` yields innermost-first (`f a b c` → `c, b, a`);
        // `beta_head_reduce` wants application order (`a, b, c`).
        let mut args: Vec<Expr> = result.get_app_args_iter().cloned().collect();
        args.reverse();
        let Some(reduced) = beta_head_reduce(&value, &args) else {
            return result;
        };
        result = reduced;
    }
    result
}

/// How a synonym-family constructor/arity type is normalized for checked
/// `add_inductive` replay. Different families need different depths, so the
/// replay tries them in order (see `try_add_inductive_family_checked`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum NormMode {
    /// No normalization — byte-identical to the pre-normalization baseline. The
    /// fail-closed final attempt: a family that gains from nothing replays
    /// exactly as before (never regresses).
    Off,
    /// Unfold the synonym head of the CONCLUSION only, keeping every binder
    /// domain (parameters, premises) verbatim. Correct for families with
    /// synonym-typed PARAMETERS (`Union (B C : Ensemble U)`) whose parameter
    /// prefix must stay spelled like the inductive's shared telescope.
    Shallow,
    /// Fully delta-unfold synonyms throughout the type. Correct for families
    /// whose PREMISES reference a synonym not yet in scope at replay time
    /// (`Power_set`'s `Included U X A` — `Included` defined later), which
    /// `add_inductive`'s syntactic field type-check would otherwise reject as an
    /// unknown constant.
    Deep,
}

impl NormMode {
    fn slot(self) -> usize {
        match self {
            NormMode::Off => 0,
            NormMode::Shallow => 1,
            NormMode::Deep => 2,
        }
    }
}

/// Recursively delta-unfold every synonym-`Const` HEAD throughout `expr` (head
/// position and all children), seeing through definitional abbreviations
/// wherever they occur. The result is definitionally equal to the input (only
/// synonym deltas + betas).
fn deep_unfold_synonyms(
    expr: &Expr,
    reader: &ShardReader,
    ctx: &SynonymCtx,
    memo: &mut HashMap<Name, Option<Expr>>,
    fuel: u32,
) -> Expr {
    if fuel == 0 {
        return expr.clone();
    }
    let head_reduced = whnf_synonym_head(expr, reader, ctx, memo);
    match head_reduced.kind() {
        ExprKind::App(f, a) => Expr::app(
            deep_unfold_synonyms(f, reader, ctx, memo, fuel - 1),
            deep_unfold_synonyms(a, reader, ctx, memo, fuel - 1),
        ),
        ExprKind::Pi(bi, dom, body) => Expr::pi(
            *bi,
            deep_unfold_synonyms(dom, reader, ctx, memo, fuel - 1),
            deep_unfold_synonyms(body, reader, ctx, memo, fuel - 1),
        ),
        ExprKind::Lam(bi, dom, body) => Expr::lam(
            *bi,
            deep_unfold_synonyms(dom, reader, ctx, memo, fuel - 1),
            deep_unfold_synonyms(body, reader, ctx, memo, fuel - 1),
        ),
        _ => head_reduced,
    }
}

/// Whether the conclusion (codomain under the `Pi` telescope) of `ty` is headed
/// by a non-inductive `Const` that has a value — i.e. a definitional
/// abbreviation the kernel's syntactic inductive checks cannot see through.
/// Gates normalization so the common inductive-/sort-headed case stays a strict
/// byte-identity (no spurious rebuild, no regression risk).
fn conclusion_is_synonym_headed(ty: &Expr, ctx: &SynonymCtx) -> bool {
    let mut cur = ty;
    while let ExprKind::Pi(_, _, body) = cur.kind() {
        cur = body.as_ref();
    }
    match cur.get_app_fn().kind() {
        ExprKind::Const(name, _) => {
            !ctx.inductives.contains(name) && ctx.header_idx.contains_key(name)
        }
        _ => false,
    }
}

/// Normalize a constructor type or inductive arity that concludes through a
/// synonym, by delta-unfolding the synonym head of the CONCLUSION (codomain
/// under the `Pi` telescope) in place — `In V (Im …) …` → `Im …`,
/// `… → Ensemble V` → `… → V → Prop` — so it is inductive- (resp. sort-) headed,
/// the form the kernel's syntactic `add_inductive` requires.
///
/// CRUCIALLY, the telescope binder domains are left UNTOUCHED. A synonym-typed
/// PARAMETER (`B : Ensemble U`) must stay spelled the same way it is in the
/// inductive's shared parameter telescope — Coq's own arity keeps its parameters
/// as `Ensemble U`, and `add_inductive`'s `check_block_agreement` compares each
/// constructor's parameter prefix to the type former's STRUCTURALLY. Unfolding a
/// parameter's type in the constructor but not the arity (or vice versa) would
/// make them disagree ("parameter N disagrees with the block's shared parameter
/// telescope"). Only the conclusion is reduced; premises and binder domains are
/// preserved (they type-check as-is, and the shard byte-match normalizes the
/// stored member the same way).
///
/// STRICT IDENTITY for the common case: [`conclusion_is_synonym_headed`] gates
/// entry, so an already inductive-/sort-headed type is returned unchanged
/// (byte-identical), leaving all non-synonym families untouched. `NormMode::Off`
/// is always identity.
fn normalize_synonym_family_type(
    ty: &Expr,
    reader: &ShardReader,
    ctx: &SynonymCtx,
    memo: &mut HashMap<Name, Option<Expr>>,
    mode: NormMode,
) -> Expr {
    if mode == NormMode::Off || !conclusion_is_synonym_headed(ty, ctx) {
        return ty.clone();
    }
    if mode == NormMode::Deep {
        return deep_unfold_synonyms(ty, reader, ctx, memo, 64);
    }
    // NormMode::Shallow — unfold the conclusion head only, keep binder domains.
    let mut binders: Vec<(BinderData, Expr)> = Vec::new();
    let mut cur = ty;
    while let ExprKind::Pi(bi, dom, body) = cur.kind() {
        binders.push((*bi, (**dom).clone()));
        cur = body.as_ref();
    }
    let concl = whnf_synonym_head(cur, reader, ctx, memo);
    binders
        .into_iter()
        .rev()
        .fold(concl, |body, (bi, dom)| Expr::pi(bi, dom, body))
}

fn build_constructor_index(reader: &ShardReader, mode: NormMode) -> HashMap<Name, Vec<CtorEntry>> {
    let ctx = synonym_ctx_for(reader);
    let mut memo: HashMap<Name, Option<Expr>> = HashMap::new();
    let mut index: HashMap<Name, Vec<CtorEntry>> = HashMap::new();
    for constant in &reader.constants {
        if DeclKind::try_from(constant.decl_kind).unwrap_or(DeclKind::Theorem)
            != DeclKind::Constructor
        {
            continue;
        }
        let Some(ctor_name) = reader.strings.get(constant.name_idx as usize) else {
            continue;
        };
        let Ok(ctor) = reconstruct_constant(ctor_name, reader, constant) else {
            continue;
        };
        // Normalize a synonym-headed conclusion (`In V (Im …) …` → `Im …`) so
        // the constructor buckets under its real owning inductive and the
        // kernel's syntactic constructor checks accept it. Strict identity for
        // the common inductive-headed conclusion. `NormMode::Off` is the
        // pre-normalization baseline bucketing (byte-identical to the original
        // `constructor_return_target(&ctor.type_expr)`), the fail-closed final
        // attempt so a family that does NOT gain from normalization is replayed
        // exactly as before (no regression).
        let ctor_type =
            normalize_synonym_family_type(&ctor.type_expr, reader, &ctx, &mut memo, mode);
        let Some((owner, return_arg_count)) = constructor_return_target(&ctor_type) else {
            continue;
        };
        index.entry(owner).or_default().push(CtorEntry {
            name: ctor.decl_name,
            type_: ctor_type,
            level_params: ctor.level_params,
            return_arg_count,
        });
    }
    index
}

fn constructor_index_for(
    reader: &ShardReader,
    mode: NormMode,
) -> std::rc::Rc<HashMap<Name, Vec<CtorEntry>>> {
    let key = reader.constants.as_ptr() as usize;
    let len = reader.constants.len();
    let slot = mode.slot();
    CTOR_INDEX.with(|cell| {
        {
            let cached = cell.borrow();
            if let Some((k, l, idx)) = cached[slot].as_ref() {
                if *k == key && *l == len {
                    return idx.clone();
                }
            }
        }
        let idx = std::rc::Rc::new(build_constructor_index(reader, mode));
        cell.borrow_mut()[slot] = Some((key, len, idx.clone()));
        idx
    })
}

/// Reconstruct the checked-replay [`InductiveDecl`] for a `DeclKind::Inductive`
/// shard constant from sibling shard constants + typed header metadata.
///
/// Returns `Ok(None)` when the shard does not carry enough coherent metadata
/// to rebuild a checked declaration (the caller fails closed). This is the
/// SINGLE reconstruction both the incremental verifier and the cake gate use.
pub(crate) fn build_inductive_replay_metadata(
    reader: &ShardReader,
    constant: &MathverseConstantHeader,
    reconstructed: &ReconstructedConstant,
    mode: NormMode,
) -> Result<Option<InductiveReplayMetadata>, String> {
    ws16_dbg(reconstructed, || {
        format!(
            "ENTER kind={:?} num_params_hdr={:?} mode={mode:?}",
            reconstructed.decl_kind,
            constant.inductive_decl_num_params()
        )
    });
    if reconstructed.decl_kind != DeclKind::Inductive {
        ws16_dbg(reconstructed, || {
            format!("STEP non-inductive decl_kind={:?}", reconstructed.decl_kind)
        });
        return Ok(None);
    }

    let synonym_ctx = synonym_ctx_for(reader);
    let mut synonym_memo: HashMap<Name, Option<Expr>> = HashMap::new();

    let all_names_from_header = inductive_all_names_from_header(reader, constant)?;
    ws16_dbg(reconstructed, || {
        format!("all_names_from_header={all_names_from_header:?}")
    });
    let type_names = all_names_from_header
        .clone()
        .unwrap_or_else(|| vec![reconstructed.decl_name.clone()]);
    if type_names.is_empty() || !type_names.contains(&reconstructed.decl_name) {
        ws16_dbg(reconstructed, || {
            format!("STEP type_names: empty or self-missing ({type_names:?})")
        });
        return Ok(None);
    };

    let type_name_set: HashSet<Name> = type_names.iter().cloned().collect();
    let mut type_arities = HashMap::new();
    let mut types = Vec::with_capacity(type_names.len());
    let mut explicit_num_params = constant.inductive_decl_num_params();

    for type_name in &type_names {
        let Some((ind_name, ind_header)) = shard_inductive_header(reader, type_name)? else {
            ws16_dbg(reconstructed, || {
                format!("STEP shard_inductive_header: missing header for {type_name}")
            });
            return Ok(None);
        };
        let ind = reconstruct_constant(ind_name, reader, ind_header)?;
        if ind.decl_kind != DeclKind::Inductive || ind.level_params != reconstructed.level_params {
            ws16_dbg(reconstructed, || {
                format!(
                    "STEP type-member kind/level: {type_name} kind={:?} lp={:?} vs root lp={:?}",
                    ind.decl_kind, ind.level_params, reconstructed.level_params
                )
            });
            return Ok(None);
        }
        if let Some(header_num_params) = ind_header.inductive_decl_num_params() {
            match explicit_num_params {
                Some(existing) if existing != header_num_params => {
                    ws16_dbg(reconstructed, || {
                        format!("STEP num_params disagree on {type_name}: {existing} vs {header_num_params}")
                    });
                    return Ok(None);
                }
                Some(_) => {}
                None => explicit_num_params = Some(header_num_params),
            }
        }
        // Normalize a synonym-headed arity codomain (`… → Ensemble V` →
        // `… → V → Prop`) so it ends in a sort with the correct index count.
        // Strict identity for the common sort-headed arity; `NormMode::Off` is
        // the baseline fail-closed attempt (identity).
        let ind_type = normalize_synonym_family_type(
            &ind.type_expr,
            reader,
            &synonym_ctx,
            &mut synonym_memo,
            mode,
        );
        let type_arity = count_pi_args(&ind_type);
        type_arities.insert(ind.decl_name.clone(), type_arity);
        types.push(InductiveType {
            name: ind.decl_name,
            type_: ind_type,
            constructors: Vec::new(),
        });
    }

    let Some(num_params) =
        explicit_num_params.or_else(|| type_arities.values().all(|arity| *arity == 0).then_some(0))
    else {
        ws16_dbg(reconstructed, || {
            format!("STEP num_params unknown: no header value, arities={type_arities:?}")
        });
        return Ok(None);
    };
    if type_arities.values().any(|arity| num_params > *arity) {
        ws16_dbg(reconstructed, || {
            format!("STEP num_params>arity: num_params={num_params} arities={type_arities:?}")
        });
        return Ok(None);
    };

    // Look up this family's constructors via a per-reader memoized index
    // (owner → constructors), instead of rescanning + reconstructing every
    // constructor in the shard for every inductive — the O(K·N) blowup that
    // froze corpus-scale replay (K inductives × N constants, each rebuilt).
    let _ = &type_name_set; // (constructors are bucketed by owner in the index)
    let index = constructor_index_for(reader, mode);
    for type_name in &type_names {
        let Some(entries) = index.get(type_name) else {
            continue;
        };
        let owner_arity = type_arities.get(type_name).copied().unwrap_or(0);
        for e in entries {
            if e.return_arg_count != owner_arity as usize
                || e.level_params != reconstructed.level_params
            {
                ws16_dbg(reconstructed, || {
                    format!(
                        "STEP ctor return/level: {} owner={type_name} return_args={} owner_arity={owner_arity} ctor_lp={:?} root_lp={:?}",
                        e.name, e.return_arg_count, e.level_params, reconstructed.level_params
                    )
                });
                return Ok(None);
            }
            let Some(ind_type) = types
                .iter_mut()
                .find(|ind_type| &ind_type.name == type_name)
            else {
                return Ok(None);
            };
            ind_type.constructors.push(Constructor {
                name: e.name.clone(),
                type_: e.type_.clone(),
            });
        }
    }

    // Constructor DECLARATION order. The owner index yields shard SCAN order,
    // which for some oleans differs from the family's declaration order
    // (observed: Lean.Data.Trie serializes node1/node/leaf while the family
    // declares leaf/node1/node). The regenerated recursor's minors follow
    // declaration order and the member byte-match compares against the
    // shard's stored `rec`, so a wrong order fails the whole family. The
    // shard's own `{member}.rec` TYPE is the order authority: constructor
    // constants appear in a recursor type only at each minor's motive-return
    // position, exactly once, in declaration order. Reorder accordingly;
    // when the rec is absent or disagrees, keep scan order (the byte-match
    // still fails closed downstream, same as before).
    for ind_type in &mut types {
        if let Some(order) =
            ctor_order_from_shard_rec(reader, &ind_type.name, &ind_type.constructors)
        {
            ind_type.constructors.sort_by_key(|c| {
                order
                    .iter()
                    .position(|n| n == &c.name)
                    .unwrap_or(usize::MAX)
            });
        }
    }

    // Empty-constructor families are reconstructable ONLY when the shard root
    // header carries the typed `InductiveDecl.num_params` stamp — i.e. it was
    // written by the checked family-export path (`add_inductive_family`, which
    // stamps `set_inductive_decl_num_params` on the root and is the source for
    // graduation / `--env olean`).
    //
    // - A genuine zero-constructor inductive (Lean core `False`/`Empty`/`PEmpty`)
    //   exported that way is a COMPLETE family declaration: an empty constructor
    //   list genuinely means zero constructors, so it flows on to the checked
    //   `add_inductive` replay (which proves the zero-ctor family sound — the
    //   constructor loop is empty, the recursor has zero minor premises) and the
    //   member byte-match (which still rejects any tampered type/recursor).
    //   Rejecting these was the bug that blocked graduating every proof carrying
    //   `False` (i.e. essentially any concrete Nat/Bool comparison, which reaches
    //   `False` via `noConfusion -> False.elim`).
    //
    // - A bare header WITHOUT that stamp (e.g. a raw `add_constant` inductive
    //   skeleton on the incremental verify path) cannot be told apart from one
    //   whose constructors are merely ABSENT from the shard (incomplete
    //   metadata), so it must STILL fail closed here. The incremental verifier's
    //   trust guard (`reject_inductive_family_skeleton` ->
    //   `validate_inductive_skeleton_trust`) only runs on this `None`, so
    //   admitting a bare zero-ctor skeleton would silently bypass the
    //   KernelVerified / axiom-free confidence checks.
    let has_family_export_stamp = constant.inductive_decl_num_params().is_some();
    if !has_family_export_stamp
        && types
            .iter()
            .any(|ind_type| ind_type.constructors.is_empty())
    {
        ws16_dbg(reconstructed, || {
            let empties: Vec<_> = types
                .iter()
                .filter(|t| t.constructors.is_empty())
                .map(|t| t.name.to_string())
                .collect();
            format!(
                "STEP empty constructors without family-export num_params stamp for: {empties:?}"
            )
        });
        return Ok(None);
    }
    if all_names_from_header.is_none()
        && has_same_shard_mutual_inductive_peer(reader, reconstructed, &types[0].constructors)?
    {
        ws16_dbg(reconstructed, || {
            "STEP same-shard mutual peer detected (all_names header absent)".to_string()
        });
        return Ok(None);
    }

    let mut generated_names = HashSet::new();
    for ind_type in &types {
        generated_names.insert(ind_type.name.clone());
        for ctor in &ind_type.constructors {
            generated_names.insert(ctor.name.clone());
        }
        for suffix in ["rec", "casesOn", "recOn"] {
            generated_names.insert(Name::from_string(&format!("{}.{suffix}", ind_type.name)));
        }
    }

    ws16_dbg(reconstructed, || {
        format!(
            "SUCCESS num_params={num_params} types={} ctors={:?}",
            types.len(),
            types
                .iter()
                .map(|t| (t.name.to_string(), t.constructors.len()))
                .collect::<Vec<_>>()
        )
    });
    Ok(Some(InductiveReplayMetadata {
        decl: InductiveDecl {
            level_params: reconstructed.level_params.clone(),
            num_params,
            types,
        },
        generated_names,
    }))
}

pub(crate) fn inductive_all_names_from_header(
    reader: &ShardReader,
    constant: &MathverseConstantHeader,
) -> Result<Option<Vec<Name>>, String> {
    let Some((start, count)) = constant.inductive_decl_all_names_block() else {
        return Ok(None);
    };
    if count == 0 {
        return Ok(None);
    }
    let start = start as usize;
    let count = count as usize;
    let end = start
        .checked_add(count)
        .ok_or_else(|| "InductiveVal.all_names string block overflow".to_string())?;
    if end > reader.strings.len() {
        return Err(format!(
            "InductiveVal.all_names string block [{start}..{end}) out of range {}",
            reader.strings.len()
        ));
    }
    Ok(Some(
        reader.strings[start..end]
            .iter()
            .map(|name| Name::from_string(name))
            .collect(),
    ))
}

fn shard_inductive_header<'a>(
    reader: &'a ShardReader,
    target: &Name,
) -> Result<Option<(&'a str, &'a MathverseConstantHeader)>, String> {
    for constant in &reader.constants {
        let decl_kind = DeclKind::try_from(constant.decl_kind).unwrap_or(DeclKind::Theorem);
        if decl_kind != DeclKind::Inductive {
            continue;
        }
        let name = reader
            .strings
            .get(constant.name_idx as usize)
            .ok_or_else(|| format!("constant name index {} out of range", constant.name_idx))?;
        if Name::from_string(name) == *target {
            return Ok(Some((name.as_str(), constant)));
        }
    }
    Ok(None)
}

fn has_same_shard_mutual_inductive_peer(
    reader: &ShardReader,
    reconstructed: &ReconstructedConstant,
    constructors: &[Constructor],
) -> Result<bool, String> {
    let other_inductive_names = shard_inductive_type_names(reader, &reconstructed.decl_name)?;
    for ctor in constructors {
        for other in &other_inductive_names {
            if mentions_name(&ctor.type_, other)
                && shard_constructor_for_owner_mentions(reader, other, &reconstructed.decl_name)?
            {
                return Ok(true);
            }
        }
    }
    Ok(false)
}

fn shard_inductive_type_names(reader: &ShardReader, except: &Name) -> Result<Vec<Name>, String> {
    let mut names = Vec::new();
    for constant in &reader.constants {
        let decl_kind = DeclKind::try_from(constant.decl_kind).unwrap_or(DeclKind::Theorem);
        if decl_kind != DeclKind::Inductive {
            continue;
        }
        let name = reader
            .strings
            .get(constant.name_idx as usize)
            .ok_or_else(|| format!("constant name index {} out of range", constant.name_idx))?;
        let name = Name::from_string(name);
        if &name != except {
            names.push(name);
        }
    }
    Ok(names)
}

fn shard_constructor_for_owner_mentions(
    reader: &ShardReader,
    owner: &Name,
    target: &Name,
) -> Result<bool, String> {
    for constant in &reader.constants {
        let decl_kind = DeclKind::try_from(constant.decl_kind).unwrap_or(DeclKind::Theorem);
        if decl_kind != DeclKind::Constructor {
            continue;
        }

        let ctor_name = reader
            .strings
            .get(constant.name_idx as usize)
            .ok_or_else(|| format!("constant name index {} out of range", constant.name_idx))?;
        let ctor = reconstruct_constant(ctor_name, reader, constant)?;
        let Some((ctor_owner, _)) = constructor_return_target(&ctor.type_expr) else {
            continue;
        };
        if &ctor_owner == owner && mentions_name(&ctor.type_expr, target) {
            return Ok(true);
        }
    }
    Ok(false)
}

/// Require every shard-resident family member to byte-match (level params +
/// type) the constant the checked `add_inductive` replay regenerated in
/// `scratch`. This is the discipline that makes recursor swaps, dropped
/// constructors, and `num_params` lies fail closed on BOTH verify surfaces.
/// Derive a member's constructor DECLARATION order from the shard's stored
/// `{member}.rec` type (see the call site above for why). Returns `None`
/// when the rec is absent, unreadable, or the derived order does not cover
/// exactly the given constructor set.
fn ctor_order_from_shard_rec(
    reader: &ShardReader,
    member: &Name,
    ctors: &[Constructor],
) -> Option<Vec<Name>> {
    if ctors.len() < 2 {
        return None;
    }
    let rec_name = format!("{member}.rec");
    let (constant, name_str) = reader.constants.iter().find_map(|c| {
        let s = reader.strings.get(c.name_idx as usize)?;
        (s.as_str() == rec_name).then_some((c, s.as_str()))
    })?;
    if constant.decl_kind != DeclKind::Recursor as u8 {
        return None;
    }
    let rec = reconstruct_constant(name_str, reader, constant).ok()?;

    let ctor_names: HashSet<&Name> = ctors.iter().map(|c| &c.name).collect();
    let mut order: Vec<Name> = Vec::with_capacity(ctors.len());
    collect_ctor_consts_in_order(&rec.type_expr, &ctor_names, &mut order);
    (order.len() == ctors.len()).then_some(order)
}

/// Depth-first, left-to-right walk collecting first occurrences of the given
/// constructor constants.
///
/// Iterative with pointer-identity dedup: recursor types are Arc-shared DAGs
/// at corpus scale, so a naive recursive walk re-visits shared subtrees once
/// per occurrence (exponential blowup / stack overflow — the same hazard the
/// kernel's `FoldMemo` exists for). Sharing cannot hide a constructor
/// constant's FIRST occurrence, which is all the ordering needs.
fn collect_ctor_consts_in_order(root: &Expr, wanted: &HashSet<&Name>, out: &mut Vec<Name>) {
    let mut stack: Vec<&Expr> = vec![root];
    let mut seen: HashSet<*const Expr> = HashSet::new();
    while let Some(e) = stack.pop() {
        if !seen.insert(e as *const Expr) {
            continue;
        }
        // Children pushed in REVERSE so the pop order is left-to-right.
        match e.kind() {
            ExprKind::Const(name, _) if wanted.contains(name) && !out.contains(name) => {
                out.push(name.clone());
            }
            ExprKind::App(f, a) => {
                stack.push(a);
                stack.push(f);
            }
            ExprKind::Pi(_, d, b) | ExprKind::Lam(_, d, b) => {
                stack.push(b);
                stack.push(d);
            }
            ExprKind::Let(_, t, v, b, _) => {
                stack.push(b);
                stack.push(v);
                stack.push(t);
            }
            ExprKind::MData(_, inner) | ExprKind::Proj(_, _, inner) => {
                stack.push(inner);
            }
            _ => {}
        }
    }
}

pub(crate) fn checked_inductive_replay_matches_shard(
    scratch: &Environment,
    reader: &ShardReader,
    metadata: &InductiveReplayMetadata,
    mode: NormMode,
) -> Result<ShardFamilyMatch, String> {
    let synonym_ctx = synonym_ctx_for(reader);
    let mut synonym_memo: HashMap<Name, Option<Expr>> = HashMap::new();
    for constant in &reader.constants {
        let name = reader
            .strings
            .get(constant.name_idx as usize)
            .ok_or_else(|| format!("constant name index {} out of range", constant.name_idx))?;
        let name = Name::from_string(name);
        if !metadata.generated_names.contains(&name) {
            continue;
        }

        let Some(existing) = scratch.get_const(&name) else {
            // The lean-core family replay (`Environment::add_inductive_core`)
            // regenerates the inductive TYPE, its CONSTRUCTORS, and `rec` — but
            // NOT the value-bearing auxiliary eliminators `casesOn`/`recOn`,
            // which Lean stores as definitions that delta-unfold to `rec`. Those
            // are therefore carried as ORDINARY definitions and re-typechecked by
            // their own `add_decl` replay (their value is checked against the
            // regenerated `rec`), so they are not the family replay's
            // responsibility and are legitimately absent from the regenerated
            // env here. Skip them. Any OTHER absent generated member (the type,
            // a constructor, or `rec`) IS a genuine family-replay defect and
            // still fails closed below.
            //
            // SOUNDNESS: skipping `casesOn`/`recOn` cannot launder a forged
            // eliminator — a shard-resident `casesOn`/`recOn` is a
            // `DeclKind::Definition` listed in the record's `carried_definitions`
            // and is re-typechecked by `replay_constant`'s `add_decl` (a wrong
            // value fails the kernel). In the clean-prelude lane the full
            // `add_inductive` DOES regenerate them, so they ARE present in
            // `scratch` and the exact match below is enforced as before.
            if is_auxiliary_eliminator(&name) {
                continue;
            }
            if std::env::var("CLEAN_WS16_DEBUG").is_ok() {
                eprintln!("WS16 match[{name}]: ABSENT from regenerated scratch env");
            }
            return Ok(ShardFamilyMatch::Mismatch {
                member: name.to_string(),
                detail: "generated member absent from regenerated scratch environment".to_string(),
            });
        };
        let reconstructed = reconstruct_constant(&name.to_string(), reader, constant)?;

        // The RECURSOR member (`{T}.rec`) is compared up to the kernel's own
        // `is_def_eq`, not raw structure. `build_recursor` regenerates a recursor
        // TYPE that is definitionally equal to Lean's stored `.rec` but can differ
        // STRUCTURALLY for indexed / large-eliminating families — index-binder
        // placement, motive-application form, and a fresh motive-universe param
        // NAME (the prop-only split in `inductive_recursor.rs`). A raw structural
        // `!=` rejected these sound families outright (the `Relation.ReflGen` /
        // `TransGen` / `ReflTransGen` shape). Widen ONLY the recursor accept gate
        // to `is_def_eq` via the shared `alpha_type_match_against_existing`
        // (structural-first, then a positional level-param rename + kernel
        // `is_def_eq`); non-recursor members keep the exact structural gate below.
        //
        // SOUNDNESS: `add_inductive` is the oracle, NOT this gate. The family was
        // already fully re-derived and validated by the checked `add_inductive` on
        // the scratch clone (positivity, well-typedness, recursor GENERATION), and
        // the recursor INSTALLED in the real env is always Clean's own freshly
        // generated one — never the shard's bytes (a `.mathverse` `.rec` carries
        // only a type, no reduction rules). This gate merely decides whether the
        // shard's copy AGREES with what the kernel built; `is_def_eq` is exactly
        // the equivalence the kernel uses everywhere else, so widening to it can
        // only additionally accept families whose sound regenerated recursor is
        // def-eq to the shard recursor — never a genuinely different (swapped,
        // dropped-minor, or mis-split) recursor, which stays not-def-eq and fails
        // closed. Even a hypothetical def-eq slip is non-TCB: every downstream
        // reference to `{T}.rec` is re-typechecked by its own `add_decl` against
        // Clean's installed recursor, so a real divergence fails there (a
        // downstream false-reject, never a false proof).
        if is_recursor_member(&name) {
            match alpha_type_match_against_existing(
                scratch,
                existing,
                &reconstructed.level_params,
                &reconstructed.type_expr,
            ) {
                AlphaTypeMatch::Match => continue,
                AlphaTypeMatch::ArityMismatch => {
                    if std::env::var("CLEAN_WS16_DEBUG").is_ok() {
                        eprintln!(
                            "WS16 match[{name}]: RECURSOR ARITY MISMATCH regenerated={} shard={}",
                            existing.level_params.len(),
                            reconstructed.level_params.len()
                        );
                    }
                    return Ok(ShardFamilyMatch::Mismatch {
                        member: name.to_string(),
                        detail: format!(
                            "recursor level-param arity differs (regenerated {}, shard {})",
                            existing.level_params.len(),
                            reconstructed.level_params.len()
                        ),
                    });
                }
                AlphaTypeMatch::TypeMismatch => {
                    if std::env::var("CLEAN_WS16_DEBUG").is_ok() {
                        eprintln!(
                            "WS16 match[{name}]: RECURSOR TYPE MISMATCH (not def-eq)\n  regenerated: {:?}\n  shard      : {:?}",
                            existing.type_, reconstructed.type_expr
                        );
                    }
                    return Ok(ShardFamilyMatch::Mismatch {
                        member: name.to_string(),
                        detail: format!(
                            "recursor type differs under kernel is_def_eq (regenerated {:?}, shard {:?})",
                            existing.type_, reconstructed.type_expr
                        ),
                    });
                }
            }
        }

        // Compare types up to binder *annotations* (`BinderInfo`): the kernel's
        // `is_def_eq` never consults binder info (see
        // `clean_kernel::tc::def_eq::binding::is_def_eq_binding`, which compares
        // only binder domains and bodies), so `(x : A) → B`, `{x : A} → B`,
        // `⦃x : A⦄ → B`, and `[x : A] → B` are the SAME type to the type checker.
        //
        // Lean's `.olean` recursor/`casesOn` types carry Lean's own binder-info
        // convention (e.g. a `StrictImplicit` major premise, an `Implicit`
        // minor-premise field), while Clean's checked `add_inductive` regenerates
        // those carriers with Clean's convention. A raw structural `!=` on the
        // derived `PartialEq` (which includes `BinderInfo`) therefore rejected
        // every shard-stored structure whose recursor binder annotations differ —
        // even though the regenerated and stored types are the same kernel type.
        //
        // SOUNDNESS: this only ignores binder annotations, the one field of
        // `BinderData` the kernel itself ignores. Every other distinction —
        // expression shape, constant names, universe levels, de Bruijn indices,
        // and QTT multiplicities — is still compared exactly, so a genuinely
        // wrong member (different domain/codomain, swapped fields, lied-about
        // `num_params`) still fails closed. We never install the shard's bytes:
        // what `add_inductive` installs is Clean's freshly kernel-checked
        // regeneration; this guard only decides accept/reject of the family.
        // The structural check (`types_equal_ignoring_binder_info`) canonicalizes
        // binder annotations but does NOT reduce. For a family nesting through a
        // dependent-parameter container (Json/PrefixTreeNode via
        // Std.DTreeMap.Internal.Impl / RBNode), Clean's regenerated recursor
        // carries the const-map field BETA-REDUCED — `(fun x => V) k ↦ V` — because
        // `Expr::beta_normalize` runs at the nested-elimination source, whereas
        // Lean's stored `rec` keeps the redex (Lean whnfs only to DETECT
        // recursiveness, inductive.cpp:383-390, never to rewrite the stored field
        // type). The two recursor types are DEFINITIONALLY equal (the entire delta
        // is redex-vs-contractum), so fall back to the kernel's own `is_def_eq`
        // before rejecting.
        //
        // SOUNDNESS: `is_def_eq` is exactly the kernel's equality — a genuinely
        // different member (wrong domain/codomain, swapped fields, lied-about
        // arity) is not def-eq and still fails closed. We install nothing from the
        // shard: `add_inductive` already installed Clean's freshly kernel-checked
        // regeneration; this guard only decides accept/reject of the family.
        // The regenerated member carries Clean's `add_inductive` output, whose
        // synonym-family constructor/arity types were normalized (delta-unfolded
        // through `In`/`Ensemble`) so the kernel's syntactic checks accept them
        // (see `normalize_synonym_family_type`). The shard stores the ORIGINAL
        // synonym-headed form (`In V (Im …) …`). Normalize the shard side the
        // same way — deterministically, using the shard's own stored synonym
        // values (independent of whether `In` is yet in `scratch`) — so the two
        // def-equal forms compare structurally equal. This is the same
        // definitional equality the `is_def_eq` fallback below certifies; doing
        // it up front makes the family accept even when the synonym definition
        // has not yet been added to the scratch environment.
        let reconstructed_type = normalize_synonym_family_type(
            &reconstructed.type_expr,
            reader,
            &synonym_ctx,
            &mut synonym_memo,
            mode,
        );
        let type_matches = types_equal_ignoring_binder_info(&existing.type_, &reconstructed_type)
            || {
                let tc = clean_kernel::tc::TypeChecker::new(scratch);
                tc.is_def_eq(&existing.type_, &reconstructed_type)
            };
        if existing.level_params != reconstructed.level_params || !type_matches {
            if std::env::var("CLEAN_WS16_DEBUG").is_ok() {
                eprintln!(
                    "WS16 match[{name}]: MISMATCH\n  regenerated lparams={:?}\n  shard       lparams={:?}\n  regenerated type: {:?}\n  shard       type: {:?}",
                    existing.level_params,
                    reconstructed.level_params,
                    existing.type_,
                    reconstructed.type_expr
                );
            }
            let detail = if existing.level_params != reconstructed.level_params {
                let fmt_params = |params: &[Name]| {
                    params
                        .iter()
                        .map(Name::to_string)
                        .collect::<Vec<_>>()
                        .join(", ")
                };
                format!(
                    "level params differ (regenerated [{}], shard [{}])",
                    fmt_params(&existing.level_params),
                    fmt_params(&reconstructed.level_params)
                )
            } else {
                format!(
                    "type differs (regenerated {:?}, shard {:?})",
                    existing.type_, reconstructed.type_expr
                )
            };
            return Ok(ShardFamilyMatch::Mismatch {
                member: name.to_string(),
                detail,
            });
        }
    }

    Ok(ShardFamilyMatch::Matched)
}

/// `true` if `name`'s final component is `casesOn` or `recOn` — the
/// value-bearing auxiliary eliminators that the lean-core family replay
/// (`add_inductive_core`) does NOT regenerate (it produces only `rec`). They
/// are carried and re-checked as ordinary definitions, so the family-replay
/// match treats their absence from the regenerated environment as expected
/// rather than a defect. See `checked_inductive_replay_matches_shard`.
fn is_auxiliary_eliminator(name: &Name) -> bool {
    let s = name.to_string();
    s.ends_with(".casesOn") || s.ends_with(".recOn")
}

/// `true` if `name`'s final component is `rec` — the primary recursor
/// (`{T}.rec`) the kernel's `build_recursor` regenerates. Its accept gate is
/// widened to the kernel's `is_def_eq` in `checked_inductive_replay_matches_shard`
/// (structurally-divergent-but-definitionally-equal recursors arise for indexed
/// / large-eliminating families). Excludes `recOn` (an auxiliary eliminator,
/// handled by [`is_auxiliary_eliminator`]) — `.rec` is a distinct suffix.
fn is_recursor_member(name: &Name) -> bool {
    name.to_string().ends_with(".rec")
}

/// `ExprFolder` that rewrites every `Pi`/`Lam` binder annotation (`BinderInfo`)
/// to a single canonical value while preserving everything else — expression
/// shape, names, levels, de Bruijn indices, and QTT multiplicities. Applied to
/// both sides before comparison so that types differing ONLY in binder
/// annotations compare equal. The default `fold_expr` recurses through every
/// `ExprKind` variant (Core, Impredicative, Cubical, ZFC), so no binder at any
/// depth — or in any extension node — escapes normalization.
struct BinderInfoCanonicalizer;

impl ExprFolder for BinderInfoCanonicalizer {
    fn fold_pi(&mut self, bd: BinderData, ty: &Expr, body: &Expr) -> Expr {
        let canon = BinderData::new(BinderInfo::Default, bd.mult);
        Expr::pi(canon, self.fold_expr(ty), self.fold_binder_body(body))
    }

    fn fold_lam(&mut self, bd: BinderData, ty: &Expr, body: &Expr) -> Expr {
        let canon = BinderData::new(BinderInfo::Default, bd.mult);
        Expr::lam(canon, self.fold_expr(ty), self.fold_binder_body(body))
    }

    // SOUNDNESS: PEEL `MData` (compare the inner expr, dropping the metadata
    // wrapper) rather than the default fold, which PRESERVES it. `MData` is an
    // elaboration annotation with NO logical content: the kernel's WHNF strips it
    // (`tc/whnf.rs`: `MData(_, inner) => Continue(inner)`), so `is_def_eq` is
    // already MData-blind. Peeling here aligns this structural check with kernel
    // semantics — it only ever WIDENS acceptance to MData-differences `is_def_eq`
    // would itself ignore, never narrows it. This is REQUIRED for the build-time
    // round-trip oracle: the eager `convert_expr` import RETAINS MData while the
    // `FlatBuilder` shard encoder STRIPS it, so without peeling every MData-bearing
    // served constant would FAIL `verify_round_trip_equal` (`types_equal_ignoring_
    // binder_info`), StampClosure the whole module, and force it off the lazy path
    // — killing the speedup on real Mathlib (Init/Prelude reproduces this). Both
    // sides flow through this same canonicalizer, so the peel is symmetric.
    fn fold_mdata(&mut self, _metadata: &clean_kernel::expr::MDataMap, inner: &Expr) -> Expr {
        self.fold_expr(inner)
    }

    // SOUNDNESS: canonicalize the `Let` binder NAME to anonymous and the `nondep`
    // flag to `false` (rebuilding ty/val/body via the recursive fold), exactly as
    // `fold_pi`/`fold_lam` canonicalize binder info. The kernel's `is_def_eq` is
    // provably blind to BOTH fields: `EquivManager::is_equiv_core`'s `(Let, Let)`
    // arm (`tc/equiv_manager.rs`) compares ty/val/body and binds the name + nondep
    // to `_`; the cached `Expr` hash (`expr/meta.rs::mk_let_meta`) mixes only depth
    // + ty/val/body hashes, never name/nondep; and WHNF zeta reduces every head
    // `Let` ignoring both. So peeling these here only WIDENS acceptance to
    // Let-name/nondep differences `is_def_eq` would itself ignore, never narrows.
    // REQUIRED for the build-time round-trip oracle: eager `convert_expr` RETAINS
    // the Let binder name + parsed `nondep`, while the `FlatBuilder` encoder +
    // shard reconstructor drop the name to `anon()` and hardcode `nondep=false`,
    // so without this every `Let`-bearing served constant (Init/Lean eqn-compiler
    // output `*.eq_def`/`*.induct`/`_private.*.go` + monadic defs are Let-dense)
    // would FAIL `verify_round_trip_equal`, StampClosure its whole module, and force
    // it off lazy — collapsing coverage on real Mathlib. RECURSES `fold_expr` into
    // ty AND val AND body, so a GENUINE difference in any subterm still survives
    // canonicalization and is still rejected. Both sides flow through the same
    // canonicalizer (symmetric).
    fn fold_let(
        &mut self,
        _name: &Name,
        ty: &Expr,
        val: &Expr,
        body: &Expr,
        _non_dep: bool,
    ) -> Expr {
        Expr::let_named(
            Name::anon(),
            self.fold_expr(ty),
            self.fold_expr(val),
            self.fold_binder_body(body),
            false,
        )
    }
}

/// Compare two types for equality ignoring binder *annotations* (`BinderInfo`),
/// `MData` annotations, and the `Let` binder *name* + `nondep` flag.
///
/// All four axes are elaboration hints with no logical content: the kernel's
/// `is_def_eq` never inspects binder info, strips `MData` in WHNF (`tc/whnf.rs`),
/// and ignores the `Let` binder name + `nondep` flag (`tc/equiv_manager.rs`'s
/// `(Let, Let)` arm binds both to `_`; the cached `Expr` hash never mixes them).
/// Two types that differ only in binder explicit/implicit-ness, `MData` wrappers,
/// or a `Let` binder name / `nondep` flag are the same kernel type. This
/// comparison stays strict on every logically-relevant distinction (shape,
/// `Const` names, levels, indices, multiplicities, literal payloads, `Proj`
/// fields) — it only erases those four kernel-blind axes (see
/// `BinderInfoCanonicalizer`) — so it is the tightest sound widening of the raw
/// structural `==` check, and is exactly the "modulo MData + binder-info +
/// Let-name/nondep" equality the no-weaker certificate relies on.
pub(crate) fn types_equal_ignoring_binder_info(a: &Expr, b: &Expr) -> bool {
    // Cheap exact-match fast path: identical bytes need no canonicalization.
    if a == b {
        return true;
    }
    let canon_a = BinderInfoCanonicalizer.fold_expr(a);
    let canon_b = BinderInfoCanonicalizer.fold_expr(b);
    canon_a == canon_b
}

pub(crate) fn constructor_return_target(expr: &Expr) -> Option<(Name, usize)> {
    let result = pi_result_type(expr);
    let head = result.get_app_fn();
    match head.kind() {
        ExprKind::Const(name, _) => Some((name.clone(), result.get_app_num_args())),
        _ => None,
    }
}

fn pi_result_type(mut expr: &Expr) -> &Expr {
    while let ExprKind::Pi(_, _, body) = expr.kind() {
        expr = body.as_ref();
    }
    expr
}

#[cfg(test)]
mod binder_info_eq_tests {
    use super::{is_auxiliary_eliminator, types_equal_ignoring_binder_info};
    use clean_kernel::expr::{BinderData, BinderInfo, Expr};
    use clean_kernel::level::Level;
    use clean_kernel::Multiplicity;
    use clean_kernel::Name;

    /// A closed `Prop` (`Sort 0`) — a convenient distinct leaf.
    fn p() -> Expr {
        Expr::prop()
    }
    /// A different closed leaf (`BVar 0`) — structurally distinct from `p()`.
    fn q() -> Expr {
        Expr::from_kind(clean_kernel::expr::ExprKind::BVar(0))
    }

    // --- Let-name / Let-nondep canonicalization (Lever A: the kernel-blind axes
    //     the round-trip oracle must ignore so Let-dense Init.* defs serve lazily) ---

    #[test]
    fn test_let_name_difference_accepted() {
        // `let x := p in p` vs `let y := p in p` — differ ONLY in the binder name.
        let a = Expr::let_named(Name::from_string("x"), p(), p(), p(), true);
        let b = Expr::let_named(Name::from_string("y"), p(), p(), p(), true);
        assert!(
            types_equal_ignoring_binder_info(&a, &b),
            "Let differing only in binder name must compare equal (is_def_eq is Let-name-blind)"
        );
    }

    #[test]
    fn test_let_nondep_difference_accepted() {
        // Differ ONLY in the `nondep` flag.
        let a = Expr::let_named(Name::from_string("x"), p(), p(), p(), true);
        let b = Expr::let_named(Name::from_string("x"), p(), p(), p(), false);
        assert!(
            types_equal_ignoring_binder_info(&a, &b),
            "Let differing only in the nondep flag must compare equal"
        );
    }

    // The THREE reject tests are the sole guard that `fold_let` recurses into every
    // subterm — a copy-paste dropping `self.fold_expr(val)` would silently mask a
    // genuine value divergence (the most damaging possible regression).

    #[test]
    fn test_let_ty_difference_rejected() {
        let a = Expr::let_named(Name::from_string("x"), p(), p(), p(), true);
        let b = Expr::let_named(Name::from_string("x"), q(), p(), p(), true);
        assert!(
            !types_equal_ignoring_binder_info(&a, &b),
            "a genuine difference in the Let TYPE must still be rejected"
        );
    }

    #[test]
    fn test_let_val_difference_rejected() {
        let a = Expr::let_named(Name::from_string("x"), p(), p(), p(), true);
        let b = Expr::let_named(Name::from_string("x"), p(), q(), p(), true);
        assert!(
            !types_equal_ignoring_binder_info(&a, &b),
            "a genuine difference in the Let VALUE must still be rejected"
        );
    }

    #[test]
    fn test_let_body_difference_rejected() {
        let a = Expr::let_named(Name::from_string("x"), p(), p(), p(), true);
        let b = Expr::let_named(Name::from_string("x"), p(), p(), q(), true);
        assert!(
            !types_equal_ignoring_binder_info(&a, &b),
            "a genuine difference in the Let BODY must still be rejected"
        );
    }

    /// `is_auxiliary_eliminator` recognises exactly the value-bearing auxiliary
    /// eliminators (`casesOn`/`recOn`) the lean-core family replay does not
    /// regenerate — and nothing else (NOT the family type, constructors, or the
    /// kernel-generated `rec`, which MUST be present in the regenerated env).
    #[test]
    fn test_is_auxiliary_eliminator_matches_only_cases_and_rec_on() {
        assert!(is_auxiliary_eliminator(&Name::from_string(
            "Exists.casesOn"
        )));
        assert!(is_auxiliary_eliminator(&Name::from_string("Nat.casesOn")));
        assert!(is_auxiliary_eliminator(&Name::from_string("Eq.recOn")));
        // Enforced (regenerated) members are NOT skipped:
        assert!(!is_auxiliary_eliminator(&Name::from_string("Exists")));
        assert!(!is_auxiliary_eliminator(&Name::from_string("Exists.intro")));
        assert!(!is_auxiliary_eliminator(&Name::from_string("Nat.rec")));
        assert!(!is_auxiliary_eliminator(&Name::from_string("Nat.zero")));
        // Substrings, not suffixes, must not match:
        assert!(!is_auxiliary_eliminator(&Name::from_string("casesOn")));
        assert!(!is_auxiliary_eliminator(&Name::from_string("X.recOnFoo")));
    }

    fn nat_ty() -> Expr {
        Expr::const_(Name::from_string("Nat"), Vec::new())
    }
    fn bool_ty() -> Expr {
        Expr::const_(Name::from_string("Bool"), Vec::new())
    }
    fn sort0() -> Expr {
        Expr::sort(Level::zero())
    }

    /// `(x : Nat) → Sort 0` with the given binder annotation on `x`.
    fn pi_nat_sort(info: BinderInfo) -> Expr {
        Expr::pi(BinderData::new(info, Multiplicity::Many), nat_ty(), sort0())
    }

    #[test]
    fn test_binder_info_eq_identical_types_equal() {
        assert!(types_equal_ignoring_binder_info(
            &pi_nat_sort(BinderInfo::Default),
            &pi_nat_sort(BinderInfo::Default)
        ));
    }

    #[test]
    fn test_binder_info_eq_differs_only_in_binder_info_equal() {
        // Default vs Implicit vs StrictImplicit vs InstImplicit over the SAME
        // domain/codomain are the same kernel type — must compare equal.
        let default = pi_nat_sort(BinderInfo::Default);
        for info in [
            BinderInfo::Implicit,
            BinderInfo::StrictImplicit,
            BinderInfo::InstImplicit,
        ] {
            assert!(
                types_equal_ignoring_binder_info(&default, &pi_nat_sort(info)),
                "binder-info-only difference ({info:?}) must compare equal"
            );
        }
    }

    #[test]
    fn test_binder_info_eq_nested_binder_info_difference_equal() {
        // `(a : Nat) → (b : Nat) → Sort 0` with mismatched inner+outer infos.
        let lhs = Expr::pi(
            BinderData::new(BinderInfo::Default, Multiplicity::Many),
            nat_ty(),
            pi_nat_sort(BinderInfo::Default),
        );
        let rhs = Expr::pi(
            BinderData::new(BinderInfo::Implicit, Multiplicity::Many),
            nat_ty(),
            pi_nat_sort(BinderInfo::StrictImplicit),
        );
        assert!(types_equal_ignoring_binder_info(&lhs, &rhs));
    }

    // ── Adversarial: logically-relevant differences must STILL be rejected ──

    #[test]
    fn test_binder_info_eq_different_domain_rejected() {
        // `{x : Nat} → Sort 0` vs `{x : Bool} → Sort 0`: different domain type.
        // Erasing binder info must NOT make these equal.
        assert!(!types_equal_ignoring_binder_info(
            &Expr::pi(
                BinderData::new(BinderInfo::Implicit, Multiplicity::Many),
                nat_ty(),
                sort0()
            ),
            &Expr::pi(
                BinderData::new(BinderInfo::Implicit, Multiplicity::Many),
                bool_ty(),
                sort0()
            ),
        ));
    }

    #[test]
    fn test_binder_info_eq_different_codomain_rejected() {
        // Same domain + binder info, different codomain.
        assert!(!types_equal_ignoring_binder_info(
            &Expr::pi(
                BinderData::new(BinderInfo::Default, Multiplicity::Many),
                nat_ty(),
                nat_ty()
            ),
            &Expr::pi(
                BinderData::new(BinderInfo::Default, Multiplicity::Many),
                nat_ty(),
                bool_ty()
            ),
        ));
    }

    #[test]
    fn test_binder_info_eq_different_arity_rejected() {
        // `(x : Nat) → Sort 0` vs `(x : Nat) → (y : Nat) → Sort 0`.
        let one = pi_nat_sort(BinderInfo::Default);
        let two = Expr::pi(
            BinderData::new(BinderInfo::Default, Multiplicity::Many),
            nat_ty(),
            pi_nat_sort(BinderInfo::Default),
        );
        assert!(!types_equal_ignoring_binder_info(&one, &two));
    }

    #[test]
    fn test_binder_info_eq_multiplicity_difference_rejected() {
        // QTT multiplicity is logically relevant and preserved by the
        // canonicalizer; a `mult` mismatch must still be rejected.
        assert!(!types_equal_ignoring_binder_info(
            &Expr::pi(
                BinderData::new(BinderInfo::Default, Multiplicity::Many),
                nat_ty(),
                sort0()
            ),
            &Expr::pi(
                BinderData::new(BinderInfo::Implicit, Multiplicity::Zero),
                nat_ty(),
                sort0()
            ),
        ));
    }

    #[test]
    fn test_binder_info_eq_const_level_difference_rejected() {
        // Same shape, different universe-level args on a Const head.
        let u = Name::from_string("u");
        let lhs = Expr::const_(Name::from_string("List"), vec![Level::zero()]);
        let rhs = Expr::const_(Name::from_string("List"), vec![Level::param(u)]);
        assert!(!types_equal_ignoring_binder_info(&lhs, &rhs));
    }
}
