// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **The minter**: a core module becomes the Clean definition script that
//! registers it.
//!
//! Total or refusing. Every instruction, type, constant and operator is
//! rendered through [`super::shape`]'s one table; anything not in it, and any
//! flag a reader could not witness, is a hard [`MintError`] rather than an
//! approximation. The minter is deliberately NOT trusted: the gate's decode
//! round-trip (M4) reads the elaborated term back into a core module and
//! compares digests, so a minter that wrote `IRBinOp.or_` where the artifact
//! had `and` is caught by the reader that never saw the minter's output.

use std::fmt::Write as _;

use super::core::{for_each_inst, Sx};
use super::error::{CoreError, MintError};
use super::mint_globals::{check_global_namespace, global, parse_globals};
use super::shape::{self, Arg};
use super::tags::Tags;

/// The minted definition script for one chain.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MintedScript {
    /// The `def` lines, in registration order.
    pub lines: Vec<String>,
}

impl MintedScript {
    /// The script as committed text: one `def` per line, trailing newline.
    #[must_use]
    pub fn text(&self) -> String {
        let mut s = String::new();
        for l in &self.lines {
            let _ = writeln!(s, "{l}");
        }
        s
    }
}

/// Mint the definition script for `core` under the given name prefix
/// (`ir_h2` yields `ir_h2_b0`, …, `ir_h2_func`, `ir_h2_module`).
///
/// `tags` supplies the crate-level interning id for every aggregate the body
/// names, and the Clean alias minted for it. An aggregate the table does not
/// list is a hard refusal, never an invented id.
///
/// A module's `(globals …)` list mints as one `def {prefix}_g{k} : IRGlobal`
/// per entry, placed after the alias definitions and before the first block
/// — see [`check_global_namespace`] for what the list must agree with. An
/// List constructors name their type arguments explicitly with `@`, including
/// the empty global list. This changes the source spelling and its digest,
/// while preserving the constructor application and decoded core module.
///
/// # Errors
/// Returns [`MintError`] on a malformed core module, a construct outside the
/// Clean fragment, an unwitnessed flag, an aggregate absent from `tags`, a
/// global index the `(globals …)` list, the instructions and the tag table's
/// `globals` lane do not all account for, or a numeral outside the registered
/// `ir_d0..ir_d130` atom pool.
pub fn mint(core: &Sx, prefix: &str, tags: &Tags) -> Result<MintedScript, MintError> {
    let body = core.tagged("module")?;
    let funcs = body[0].tagged("funcs")?;
    // The module's function list must be EXACTLY the bodies the tag table
    // declares, in order. One body is the default and needs no lane; a second
    // one is a reviewed row, never something a core module can introduce on
    // its own.
    let declared = tags.body_canonicals();
    if funcs.len() != declared.len() {
        return Err(CoreError::Shape(format!(
            "this module carries {} function(s) and the chain's tag table declares {} \
             ({declared:?}). A body the table does not declare has no pinned interface and no \
             name prefix, so minting it would invent both",
            funcs.len(),
            declared.len()
        ))
        .into());
    }
    let globals = parse_globals(body[1].tagged("globals")?)?;
    let parsed: Vec<&[Sx]> = funcs
        .iter()
        .map(|f| f.tagged("func"))
        .collect::<Result<_, _>>()?;
    check_func_namespace(core, &parsed, tags)?;
    check_global_namespace(core, &globals, tags)?;
    let mut lines = tags.alias_defs();
    // Globals FIRST: a block may take a global's address, and the module line
    // names every global, so the definitions land between the aliases and the
    // first block. A module with none emits no line here.
    let mut global_names = Vec::new();
    for g in &globals {
        let name = format!("{prefix}_g{}", g.index);
        lines.push(format!("def {name} : IRGlobal := {}", global(g, tags)?));
        global_names.push(name);
    }
    let mut func_names = Vec::new();
    for (f, canonical) in parsed.iter().zip(&declared) {
        let own = u32::try_from(f[0].num()?)
            .map_err(|_| CoreError::Shape("a function id does not fit u32".into()))?;
        if own != *canonical {
            return Err(CoreError::Shape(format!(
                "the module's function list is out of order: position for canonical index \
                 {canonical} carries `(func {own} …)`. The list order IS the order \
                 `ir_func_find` walks, so it is a fact about the module"
            ))
            .into());
        }
        let fp = tags.body_prefix(*canonical, prefix);
        let mut block_names = Vec::new();
        for b in f[3].tagged("blocks")? {
            let bi = b.tagged("block")?;
            let name = format!("{fp}_b{}", bi[0].atom()?);
            let params = nat_list(bi[1].tagged("params")?)?;
            let nodes = node_list(bi[2].tagged("nodes")?, tags)?;
            lines.push(format!(
                "def {name} : IRBlock := IRBlock.mk {} {params} {nodes}",
                nat(bi[0].num()?)?
            ));
            block_names.push(name);
        }
        let mut blocks = String::from("ir_blk0");
        for n in block_names.iter().rev() {
            blocks = format!("(ir_blk {n} {blocks})");
        }
        lines.push(format!(
            "def {fp}_func : IRFunc := IRFunc.mk {} {} {} {blocks}",
            nat(f[0].num()?)?,
            nat_list(f[1].tagged("params")?)?,
            nat(f[2].tagged("entry")?[0].num()?)?
        ));
        func_names.push(format!("{fp}_func"));
    }
    let mut list = String::from("(@IRList.nil IRFunc)");
    for n in func_names.iter().rev() {
        list = format!("(@IRList.cons IRFunc {n} {list})");
    }
    // The global list is spelled the same way, and its empty case is the
    // explicit literal `(@IRList.nil IRGlobal)`. M3 checks the regenerated
    // source spelling against this renderer as well as its decoded module.
    let mut glist = String::from("(@IRList.nil IRGlobal)");
    for n in global_names.iter().rev() {
        glist = format!("(@IRList.cons IRGlobal {n} {glist})");
    }
    // The lists are already parenthesised, which is what every chain before
    // this lane minted and what `IRModule.mk`'s argument positions need.
    //
    // This still mints `IRModule.mk`, deliberately, and the Phase-B note that
    // used to stand here has come true rather than been deleted. It read:
    // "Phase B adds an additive `IRModule.mkv` carrying a derived encodings
    // table, but the minter arm for it rides on the globals rendering of
    // Phase-A job A:S6, which is not in this worktree; both arms land together
    // in B4/B5." This lane IS where the two met — the globals rendering above
    // is that A:S6 work — so the `mkv` arm is now unblocked and is still not
    // taken here. Every chain minted by this function stays an `IRModule.mk`,
    // which is exactly the term the M3 byte-identity fixtures pin and what
    // makes the EvalIR extension conservative over them by iota. A chain that
    // needs an encodings table gets the `mkv` arm beside this one, never by
    // changing what this line emits.
    // THE ENCODINGS LIST, and the `mkv` arm it selects.
    //
    // Empty table -> `IRModule.mk`, byte for byte what every chain before
    // Phase B minted, which is what their M3 gates assert. A table WITH rows
    // -> `IRModule.mkv`, which carries them, and `ir_mod_encs` reads them
    // back. That split is the whole conservativity argument: `mk` sends
    // `ir_mod_encs` to the empty table and the encoding-aware load
    // iota-reduces to the identity there, so adding `mkv` cannot move a term
    // any older chain minted.
    let mut enc_names = Vec::new();
    for (i, e) in tags.encodings.iter().enumerate() {
        let name = format!("{prefix}_e{i}");
        let payload = ty(&super::core::parse(&e.payload)?, tags)?;
        // *** THE KEY IS THE CRATE ID, NOT THE CANONICAL INDEX. ***
        //
        // `ir_enc_matches` compares the row's first `Nat` against the number an
        // `IRTy.enum_` / `IRTy.struct_` carries — and an aggregate renders as
        // the chain's ALIAS, whose definition carries the CRATE-level id (see
        // `ty` above). So a row minted at the canonical index keys on a number
        // no type in the module ever presents.
        //
        // That is not hypothetical: `ir_lzd`'s first two rows shipped that way
        // on 2026-09-10 and were silently inert — worse than inert, because
        // canonical 1 and crate id 1 both exist here, so one row fired at the
        // WRONG TYPE and another re-entered itself until its fuel ran out.
        // Nothing caught it until the machine was executed at those types,
        // which is why `the_encodings_keys_are_the_ids_the_aliases_carry`
        // exists beside this line.
        //
        // Resolving through `enum_alias`/`struct_alias` also makes a row whose
        // canonical index the tag table does not name a REFUSAL rather than a
        // numeral standing for nothing — the same rule the function namespace
        // has.
        let crate_id = match e.kind {
            super::tags::EncKind::Niche { .. } => tags.enum_alias(e.canonical)?.0,
            super::tags::EncKind::Wrap { .. } => tags.struct_alias(e.canonical)?.0,
        };
        let k = nat(u128::from(crate_id))?;
        lines.push(match e.kind {
            super::tags::EncKind::Niche {
                none_variant,
                some_variant,
            } => format!(
                "def {name} : IREnc := IREnc.nicheptr {k} {} {} {payload}",
                nat(u128::from(none_variant))?,
                nat(u128::from(some_variant))?,
            ),
            super::tags::EncKind::Wrap { slot, fields } => format!(
                "def {name} : IREnc := IREnc.ptrwrap {k} {} {} {payload}",
                nat(u128::from(slot))?,
                nat(u128::from(fields))?,
            ),
        });
        enc_names.push(name);
    }
    let head = if enc_names.is_empty() {
        format!("IRModule.mk {list} {glist}")
    } else {
        let mut elist = String::from("(@IRList.nil IREnc)");
        for n in enc_names.iter().rev() {
            elist = format!("(@IRList.cons IREnc {n} {elist})");
        }
        format!("IRModule.mkv {list} {glist} {elist}")
    };
    lines.push(format!("def {prefix}_module : IRModule := {head}"));
    Ok(MintedScript { lines })
}

/// **One namespace, and every index in it accounted for.**
///
/// `(func N …)` and `(call M …)` name the SAME namespace — `ir_func_find`
/// resolves a callee by scanning for a function whose own id equals it — so a
/// callee index that no table row pins is a numeral standing for nothing, and
/// the 2026-08-20 collision was exactly two writers filling that namespace from
/// two counters.
///
/// The rule is stated so that it needs no exception for a body that calls
/// nothing: an EMPTY `funcs` lane is consistent only with a module containing
/// no `call`. A body that calls anything must pin the whole namespace, its own
/// entry included.
fn check_func_namespace(core: &Sx, fs: &[&[Sx]], tags: &Tags) -> Result<(), MintError> {
    let mut used: Vec<u128> = Vec::new();
    for f in fs {
        used.push(
            f.first()
                .ok_or_else(|| CoreError::Shape("(func …) carries no id".into()))?
                .num()?,
        );
    }
    for_each_inst(core, |block, node, inst| {
        let l = inst.list()?;
        if l.first().and_then(|h| h.atom().ok()) == Some("call") {
            used.push(
                l.get(1)
                    .ok_or_else(|| {
                        CoreError::Shape(format!("bb{block}#{node}: `call` with no callee"))
                    })?
                    .num()?,
            );
        }
        Ok(())
    })?;
    if tags.funcs.is_empty() {
        if used.len() > 1 {
            return Err(CoreError::NoImage(
                "this body CALLS something, and the chain's tag table has no `funcs` lane. The \
                 function's own id and its callee ids are one namespace; leaving it unpinned is \
                 what let one numeral denote two functions until 2026-08-20. Pin the lane."
                    .into(),
            )
            .into());
        }
        return Ok(());
    }
    for id in used {
        let canonical = u32::try_from(id)
            .map_err(|_| CoreError::Shape(format!("function index {id} does not fit u32")))?;
        tags.func_pin(canonical)?;
    }
    Ok(())
}

/// A STRUCTURAL INDEX: `ir_dN`, or a refusal naming the numeral the atom pool
/// lacks.
///
/// The pool is `ir_d0..ir_d130` since 2026-09-16, `ir_d0..ir_d63` before that
/// (the designated target's SSA ids reach 20 alone and 39 in its own minted
/// body; 130 is the max SSA result id of `tc::heartbeat::tick_heartbeat`, the
/// callee whose absence makes infer_type's transitive closure cyclic). The
/// spec registers the atoms in `eval_ir_crystal.rs`. The
/// DATA pool cutoff in [`nat_data`] deliberately stays at 16: widening it
/// would respell data slots of already-minted artifacts (`(IRConst.int_ 63)`
/// in the meta_tag chain would become `ir_d63`), and byte-identity of every
/// landed artifact is the widening's own regression gate.
///
/// Every slot that reaches here names a position in this module — an SSA id, a
/// block id, a function id, an aggregate interning id — and the
/// refusal is the point: a `(func 20 …)` minted as a bare `20` would register a
/// module naming a numeral the specification never introduced, and nothing
/// downstream would say so.
pub(super) fn nat(n: u128) -> Result<String, MintError> {
    if n <= MAX_STRUCTURAL_ATOM {
        Ok(format!("ir_d{n}"))
    } else {
        Err(MintError::Numeral(n))
    }
}

/// The highest numeral the specification declares as a structural `ir_d<N>`
/// atom -- `eval_ir_crystal.rs` registers `ir_d65..ir_d130` (2026-09-16), and
/// `generated/ir_itc.defs.txt` really does name `ir_d130`.
///
/// It is a CONSTANT because the bound and the refusal message drifted the day
/// the pool widened: the check moved to 130 and `MintError::Numeral` went on
/// saying `ir_d0..ir_d63`, which is a false statement in a user-facing error
/// and is what let two refusal pins stop refusing without anyone reading a
/// wrong number. The message is now formatted from this value.
pub(crate) const MAX_STRUCTURAL_ATOM: u128 = 130;

/// The crate-level INTERNING ID of an aggregate, as the chain's alias
/// definition names it.
///
/// Same policy as [`nat_data`] and for the same reason, but this slot had a
/// latent fail-OPEN before: `Tags::alias_defs` formatted every id as
/// `ir_d{id}` unconditionally, so an enum interned at 127 minted
/// `IRTy.enum_ ir_d127` — a constant the specification does not declare, which
/// no reader in this module would have caught and which surfaces only as an
/// elaboration failure at registration time. It is a datum, not a position in
/// the module, and it renders as one.
#[must_use]
pub(crate) fn interning_id(id: u32) -> String {
    nat_data(u128::from(id))
}

/// A MACHINE DATUM — a type's bit width, or an integer constant's value.
///
/// Not a position in the module, and not bounded by the atom pool: `u32`'s
/// width is 32 and `SimpPriority::Default`'s value is 1000. Renders through the
/// pool while it can, and as a decimal `Nat` literal above it — which Clean's
/// parser already accepts (`ir_mt_amt : Nat := 63`,
/// `IRConst.int_ 4294967295` in the `bvar_in_range` chain) and which
/// [`super::decode`] reads back through `ExprKind::Lit`.
///
/// Keeping the pool for `n <= 16` is not caution for its own sake: it makes
/// every artifact minted before this function existed byte-identical after it,
/// so the change is visible in exactly the chains that need it and in no other.
///
/// Total, deliberately: a datum has no upper bound to refuse at. What is still
/// refused is a datum in a STRUCTURAL slot, which is [`nat`]'s job.
fn nat_data(n: u128) -> String {
    if n <= 16 {
        format!("ir_d{n}")
    } else {
        n.to_string()
    }
}

fn flag(sx: &Sx) -> Result<&'static str, MintError> {
    match sx.atom()? {
        "true" => Ok("Bool.true"),
        "false" => Ok("Bool.false"),
        "?" => Err(CoreError::Unwitnessed(
            "a flag this reader could not witness reached the minter".into(),
        )
        .into()),
        other => Err(CoreError::Shape(format!("expected a flag, found `{other}`")).into()),
    }
}

fn nat_list(items: &[Sx]) -> Result<String, MintError> {
    let vals: Vec<String> = items
        .iter()
        .map(|i| i.num().map_err(MintError::from).and_then(nat))
        .collect::<Result<_, _>>()?;
    Ok(match vals.len() {
        0 => "ir_nl0".into(),
        1 => format!("(ir_nl1 {})", vals[0]),
        2 => format!("(ir_nl2 {} {})", vals[0], vals[1]),
        _ => {
            let mut s = String::from("(@IRList.nil Nat)");
            for v in vals.iter().rev() {
                s = format!("(@IRList.cons Nat {v} {s})");
            }
            s
        }
    })
}

fn node_list(nodes: &[Sx], tags: &Tags) -> Result<String, MintError> {
    let rendered: Vec<String> = nodes
        .iter()
        .map(|n| node(n, tags))
        .collect::<Result<_, _>>()?;
    Ok(match rendered.len() {
        0 => "ir_bd0".into(),
        1 => format!("(ir_bd1 {})", rendered[0]),
        2 => format!("(ir_bd2 {} {})", rendered[0], rendered[1]),
        3 => format!("(ir_bd3 {} {} {})", rendered[0], rendered[1], rendered[2]),
        6 => format!(
            "(ir_bd6 {} {} {} {} {} {})",
            rendered[0], rendered[1], rendered[2], rendered[3], rendered[4], rendered[5]
        ),
        _ => {
            let mut s = String::from("(@IRList.nil IRNode)");
            for r in rendered.iter().rev() {
                s = format!("(@IRList.cons IRNode {r} {s})");
            }
            s
        }
    })
}

fn node(n: &Sx, tags: &Tags) -> Result<String, MintError> {
    let items = n.tagged("node")?;
    if items.len() != 2 {
        return Err(CoreError::Shape("(node (results ..) INST) takes 2 items".into()).into());
    }
    let results = items[0].tagged("results")?;
    let i = inst(&items[1], tags)?;
    Ok(match results.len() {
        0 => format!("(ir_nd {i})"),
        1 => format!("(ir_nd1 {i} {})", nat(results[0].num()?)?),
        _ => format!("(IRNode.mk {i} {})", nat_list(results)?),
    })
}

fn inst(sx: &Sx, tags: &Tags) -> Result<String, MintError> {
    let l = sx.list()?;
    let head = l
        .first()
        .ok_or_else(|| CoreError::Shape("empty instruction".into()))?
        .atom()?;
    let sh = shape::inst(head)
        .ok_or_else(|| CoreError::NoImage(format!("instruction mnemonic `{head}`")))?;
    let args = &l[1..];
    if args.len() != sh.args.len() {
        return Err(CoreError::Shape(format!(
            "`{head}` takes {} argument(s), found {}",
            sh.args.len(),
            args.len()
        ))
        .into());
    }
    let mut out = String::from(sh.clean);
    for (kind, a) in sh.args.iter().zip(args) {
        let _ = write!(out, " {}", arg(*kind, a, tags)?);
    }
    Ok(if sh.args.is_empty() {
        out
    } else {
        format!("({out})")
    })
}

pub(super) fn arg(kind: Arg, a: &Sx, tags: &Tags) -> Result<String, MintError> {
    Ok(match kind {
        Arg::Ty => ty(a, tags)?,
        Arg::Val | Arg::Blk | Arg::Nat => nat(a.num()?)?,
        Arg::Data => nat_data(a.num()?),
        Arg::Flag => flag(a)?.to_string(),
        Arg::Vals(head) => nat_list(a.tagged(head)?)?,
        Arg::Cases => cases(a.tagged("cases")?, tags)?,
        Arg::Const => cst(a, tags)?,
        Arg::OptVal => match a.list()?.first().map(Sx::atom).transpose()? {
            Some("none") => "(@IROption.none Nat)".into(),
            Some("some") => format!("(@IROption.some Nat {})", nat(a.tagged("some")?[0].num()?)?),
            other => {
                return Err(CoreError::Shape(format!(
                    "expected (some n) or (none), found `{other:?}`"
                ))
                .into())
            }
        },
        Arg::Op(alpha) => {
            let name = a.atom()?;
            shape::alphabet(alpha)
                .iter()
                .find(|(c, _)| *c == name)
                .map(|(_, k)| (*k).to_string())
                .ok_or_else(|| CoreError::NoImage(format!("{alpha} operator `{name}`")))?
        }
    })
}

fn cases(items: &[Sx], _tags: &Tags) -> Result<String, MintError> {
    let mut s = String::from("ir_sc0");
    for c in items.iter().rev() {
        let ci = c.tagged("case")?;
        if ci.len() != 3 {
            return Err(CoreError::Shape("(case v blk (args ..)) takes 3 items".into()).into());
        }
        let args = ci[2].tagged("args")?;
        s = if args.is_empty() {
            format!("(ir_sc {} {} {s})", nat(ci[0].num()?)?, nat(ci[1].num()?)?)
        } else {
            format!(
                "(@IRList.cons IRSwitchCase (IRSwitchCase.mk {} {} {}) {s})",
                nat(ci[0].num()?)?,
                nat(ci[1].num()?)?,
                nat_list(args)?
            )
        };
    }
    Ok(s)
}

fn ty(a: &Sx, tags: &Tags) -> Result<String, MintError> {
    let l = a.list()?;
    let head = l
        .first()
        .ok_or_else(|| CoreError::Shape("empty type".into()))?
        .atom()?;
    // Aggregates render as the chain's ALIAS, whose definition carries the
    // crate-level id from the tag table. Everything else renders structurally.
    if head == "enum" || head == "struct" {
        let canonical = u32::try_from(l[1].num()?)
            .map_err(|_| CoreError::Shape("aggregate index does not fit u32".to_string()))?;
        let (_, alias) = if head == "enum" {
            tags.enum_alias(canonical)?
        } else {
            tags.struct_alias(canonical)?
        };
        return Ok(alias.clone());
    }
    let sh = shape::ty(head).ok_or_else(|| CoreError::NoImage(format!("type `{head}`")))?;
    if l.len() - 1 != sh.args.len() {
        return Err(CoreError::Shape(format!(
            "type `{head}` takes {} argument(s), found {}",
            sh.args.len(),
            l.len() - 1
        ))
        .into());
    }
    let mut out = String::from(sh.clean);
    for (kind, x) in sh.args.iter().zip(&l[1..]) {
        let _ = write!(out, " {}", arg(*kind, x, tags)?);
    }
    Ok(if sh.args.is_empty() {
        out
    } else {
        format!("({out})")
    })
}

fn cst(a: &Sx, tags: &Tags) -> Result<String, MintError> {
    let l = a.list()?;
    let head = l
        .first()
        .ok_or_else(|| CoreError::Shape("empty constant".into()))?
        .atom()?;
    if head == "agg" {
        let mut spine = String::from("IRConst.vnil");
        for e in l[1..].iter().rev() {
            spine = format!("(IRConst.vcons {} {spine})", cst(e, tags)?);
        }
        return Ok(format!("(IRConst.aggv {spine})"));
    }
    let sh = shape::cst(head).ok_or_else(|| CoreError::NoImage(format!("constant `{head}`")))?;
    if l.len() - 1 != sh.args.len() {
        return Err(CoreError::Shape(format!(
            "constant `{head}` takes {} argument(s), found {}",
            sh.args.len(),
            l.len() - 1
        ))
        .into());
    }
    let mut out = String::from(sh.clean);
    for (kind, x) in sh.args.iter().zip(&l[1..]) {
        let _ = write!(out, " {}", arg(*kind, x, tags)?);
    }
    Ok(if sh.args.is_empty() {
        out
    } else {
        format!("({out})")
    })
}
