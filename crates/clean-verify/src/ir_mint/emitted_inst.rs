// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Reader B's instruction grammar: one arm per printed form of
//! `trust_ir::display::write_inst`, and a refusal for everything else.
//!
//! The arms are written against the producer's printer, form for form, so an
//! instruction the producer prints differently than this expects FAILS rather
//! than being read as something else. That is the whole discipline here: there
//! is no fallback arm and no "unknown instruction" placeholder.

use super::core::Sx;
use super::emitted::EmittedReader;
use super::error::{CoreError, EmittedError};
use super::shape;

type R = Result<Sx, EmittedError>;

/// Parse one printed instruction into its core form.
///
/// # Errors
/// Returns [`EmittedError`] when the text is not a form this reader knows.
#[allow(clippy::too_many_lines)]
pub(super) fn parse(r: &mut EmittedReader, s: &str) -> R {
    let s = s.trim();
    if s == "unreachable" {
        return Ok(Sx::tag("unreachable", vec![]));
    }
    if let Some(c) = s.strip_prefix("assert ") {
        return Ok(Sx::tag("assert", vec![num(r.r_val(c)?)]));
    }
    if let Some(rest) = s.strip_prefix("ret") {
        return Ok(Sx::tag("ret", vec![Sx::tag("vals", r.r_args(rest)?)]));
    }
    if let Some(rest) = s.strip_prefix("br ") {
        let (t, a) = r.r_target(rest)?;
        return Ok(Sx::tag("br", vec![num(t), Sx::tag("args", a)]));
    }
    if let Some(rest) = s.strip_prefix("condbr ") {
        let (c, arms) = rest
            .split_once(", ")
            .ok_or_else(|| r.e_syn("condbr needs a condition and two arms".into()))?;
        let cond = r.r_val(c)?;
        let (t, e) = split_arms(r, arms)?;
        let (tt, ta) = r.r_target(&t)?;
        let (et, ea) = r.r_target(&e)?;
        return Ok(Sx::tag(
            "condbr",
            vec![
                num(cond),
                num(tt),
                Sx::tag("args", ta),
                num(et),
                Sx::tag("args", ea),
            ],
        ));
    }
    if let Some(rest) = s.strip_prefix("switch ") {
        return switch(r, rest);
    }
    if let Some(rest) = s.strip_prefix("call @func.") {
        let (id, argtxt) = rest
            .split_once('(')
            .ok_or_else(|| r.e_syn("call needs an argument list".into()))?;
        let id: u32 = id
            .parse()
            .map_err(|_| r.e_syn(format!("callee id `{id}` is not a number")))?;
        let inner = argtxt
            .strip_suffix(')')
            .ok_or_else(|| r.e_syn("unbalanced call argument list".into()))?;
        let mapped = r.r_func(id);
        return Ok(Sx::tag(
            "call",
            vec![num(mapped), Sx::tag("args", r.r_args(inner)?)],
        ));
    }
    if let Some(rest) = s.strip_prefix("global_addr @global.") {
        let id: u32 = rest
            .trim()
            .parse()
            .map_err(|_| r.e_syn(format!("global id `{rest}` is not a number")))?;
        let mapped = r.global_index(id)?;
        return Ok(Sx::tag("globaladdr", vec![num(mapped)]));
    }
    if let Some(rest) = s.strip_prefix("ptr_from_parts ") {
        return ptr_from_parts(r, rest);
    }
    // Crystal E5 (decision memo §23): the two lane projections, first printed by
    // chained bodies once the M0 producer's fat kinds have images. Printed forms
    // are trust-ir's `display.rs`: `ptr_data {ptr_ty} %{}` and
    // `ptr_metadata {ptr_ty} %{} to {metadata_ty}`. The core order is the
    // specification's (`IRInst.ptrdata ty p`, `IRInst.ptrmetadata pt mt p`),
    // the one reader A emits. The types go through `split_ty`, which keeps a
    // `slice ty.N` kind whole so its refusal names the kind.
    if let Some(rest) = s.strip_prefix("ptr_data ") {
        let (ptr_ty, v) = split_ty(r, rest)?;
        return Ok(Sx::tag(
            "ptrdata",
            vec![r.r_ty(&ptr_ty)?, num(r.r_val(&v)?)],
        ));
    }
    if let Some(rest) = s.strip_prefix("ptr_metadata ") {
        let (ptr_ty, tail) = split_ty(r, rest)?;
        let ptr_ty = r.r_ty(&ptr_ty)?;
        let (v, md_ty) = tail.split_once(" to ").ok_or_else(|| {
            r.e_syn("ptr_metadata needs `%p to <metadata_ty>` after its pointer type".into())
        })?;
        let md_ty = r.r_ty(md_ty)?;
        return Ok(Sx::tag(
            "ptrmetadata",
            vec![ptr_ty, md_ty, num(r.r_val(v)?)],
        ));
    }
    if let Some(rest) = s.strip_prefix("const ") {
        let (ty, lit) = rest
            .split_once(' ')
            .ok_or_else(|| r.e_syn("const needs a type and a literal".into()))?;
        return Ok(Sx::tag("const", vec![r.r_ty(ty)?, r.r_cst(lit)?]));
    }
    if let Some(rest) = s.strip_prefix("undef ") {
        return Ok(Sx::tag("undef", vec![r.r_ty(rest)?]));
    }
    if let Some(rest) = s.strip_prefix("load ") {
        return load(r, rest, "false");
    }
    if let Some(rest) = s.strip_prefix("volatile load ") {
        return load(r, rest, "true");
    }
    if let Some(rest) = s.strip_prefix("store ") {
        return store(r, rest, "false");
    }
    if let Some(rest) = s.strip_prefix("volatile store ") {
        return store(r, rest, "true");
    }
    if let Some(rest) = s.strip_prefix("extractfield ") {
        let (ty, tail) = split1(r, rest)?;
        let (agg, field) = tail
            .rsplit_once(", ")
            .ok_or_else(|| r.e_syn("extractfield needs an aggregate and a field".into()))?;
        let f: u128 = field
            .trim()
            .parse()
            .map_err(|_| r.e_syn(format!("field `{field}` is not a number")))?;
        return Ok(Sx::tag(
            "extractfield",
            vec![r.r_ty(&ty)?, num(r.r_val(agg)?), Sx::a(f.to_string())],
        ));
    }
    if let Some(rest) = s.strip_prefix("insertfield ") {
        // `insertfield <ty> <agg>, <field>, <value>` — the WRITE dual of
        // `extractfield`, first reached by the `FlatFlags::with` chain
        // (2026-08-21). Until then this arm did not exist and reader B
        // REFUSED the fixture by name, which is the recorded posture for a
        // mnemonic outside the fragment: fail closed, never approximate.
        let (ty, tail) = split1(r, rest)?;
        let parts: Vec<&str> = tail.split(", ").collect();
        if parts.len() != 3 {
            return Err(r.e_syn("insertfield needs an aggregate, a field and a value".into()));
        }
        let f: u128 = parts[1]
            .trim()
            .parse()
            .map_err(|_| r.e_syn(format!("field `{}` is not a number", parts[1])))?;
        return Ok(Sx::tag(
            "insertfield",
            vec![
                r.r_ty(&ty)?,
                num(r.r_val(parts[0])?),
                Sx::a(f.to_string()),
                num(r.r_val(parts[2])?),
            ],
        ));
    }
    if let Some(rest) = s.strip_prefix("select ") {
        let (ty, tail) = split1(r, rest)?;
        let ops = r.r_args(&tail)?;
        if ops.len() != 3 {
            return Err(r.e_syn("select takes three operands".into()));
        }
        let mut v = vec![r.r_ty(&ty)?];
        v.extend(ops);
        return Ok(Sx::tag("select", v));
    }
    // THE THREE THE PHASE-B CLOSURE ADDS, and the only three of its nineteen
    // opcodes reader B could not already read (measured, not assumed: `zext`
    // reads through the generic CAST table below, and `ptr_from_parts` got its
    // arm with the `ir_lzc` chain). Printed forms are trust-ir's own
    // `display.rs`, quoted at each arm rather than inferred from a fixture, so
    // a form the producer emits and no committed body happens to contain is
    // still read correctly or refused by name.
    //
    // `borrow %p` — display.rs: `write!(f, "borrow %{}", val(ptr))`. One
    // operand and no type: `IRInst.borrow` is `[Val]`.
    if let Some(rest) = s.strip_prefix("borrow ") {
        return Ok(Sx::tag("borrow", vec![num(r.r_val(rest.trim())?)]));
    }
    // `copy <ty> %v` — display.rs: `write!(f, "copy {ty} %{}", val(operand))`.
    // `IRInst.copy` is `[Ty, Val]`; the type is READ and not dropped, because
    // the machine's copy arm checks the operand's shape class against it and
    // `data/evalir_adequacy_grid.json` carries `copy-type-check-coarse` as a
    // measured disagreement with the reference over exactly that check.
    if let Some(rest) = s.strip_prefix("copy ") {
        let (ty, v) = split1(r, rest)?;
        return Ok(Sx::tag("copy", vec![r.r_ty(&ty)?, num(r.r_val(&v)?)]));
    }
    // `alloca <ty>[, %count][, align N]` — display.rs writes the type, then
    // `", %{count}"` if there is one, then `", align {a}"` if there is one, in
    // that order.
    if let Some(rest) = s.strip_prefix("alloca ") {
        return alloca(r, rest);
    }
    if let Some(rest) = s.strip_prefix("gep inbounds ") {
        return gep(r, rest, "true");
    }
    if let Some(rest) = s.strip_prefix("gep ") {
        return gep(r, rest, "false");
    }
    if let Some(rest) = s.strip_prefix("icmp ") {
        return cmp(r, rest, "icmp");
    }
    if let Some(rest) = s.strip_prefix("fcmp ") {
        return cmp(r, rest, "fcmp");
    }
    // Cast: `<op> <srcty> %v to <dstty>`. Checked before the binops so a
    // future op name shared by both alphabets cannot be read as the wrong one.
    if let Some((head, tail)) = s.split_once(' ') {
        if let Some((_, clean)) = shape::CAST.iter().find(|(c, _)| *c == head) {
            let _ = clean;
            let (src, rest) = split1(r, tail)?;
            let (v, dst) = rest
                .split_once(" to ")
                .ok_or_else(|| r.e_syn("a cast needs `to <type>`".into()))?;
            return Ok(Sx::tag(
                "cast",
                vec![Sx::a(head), r.r_ty(&src)?, r.r_ty(dst)?, num(r.r_val(v)?)],
            ));
        }
        if shape::BINOP.iter().any(|(c, _)| *c == head) {
            return binary(r, "binop", head, tail);
        }
        if shape::OVERFLOW.iter().any(|(c, _)| *c == head) {
            return binary(r, "overflow", head, tail);
        }
        if shape::UNOP.iter().any(|(c, _)| *c == head) {
            let (ty, v) = split1(r, tail)?;
            return Ok(Sx::tag(
                "unop",
                vec![Sx::a(head), r.r_ty(&ty)?, num(r.r_val(&v)?)],
            ));
        }
    }
    Err(r.e_core(CoreError::NoImage(format!("printed instruction `{s}`"))))
}

/// `alloca <ty>[, %count][, align N]`.
///
/// `IRInst.alloca` is `[Arg::Ty, Arg::OptVal]`: it has a slot for the COUNT and
/// none for the alignment. So `align` is read and RECORDED in reader A's own
/// spelling — the same disposition `load` and `store` take, and for the same
/// reason: before 2026-08-20 those two split on the first comma and dropped
/// whatever followed WITHOUT LOOKING, so `, align 8` and `, banana` were
/// equally invisible. Anything after the type that is neither a `%count` nor
/// an `align N` is a refusal, and the operands must arrive in the order the
/// printer emits them: a count after an alignment is a form trust-ir does not
/// print, and reading it would be reading outside the fragment.
fn alloca(r: &mut EmittedReader, rest: &str) -> R {
    let mut parts = rest.split(',').map(str::trim).filter(|p| !p.is_empty());
    let ty = parts
        .next()
        .ok_or_else(|| r.e_syn("alloca needs a type".into()))?;
    let ty = r.r_ty(ty)?;
    let mut next = parts.next();
    let mut count: Option<u32> = None;
    if let Some(c) = next.filter(|c| c.starts_with('%')) {
        count = Some(r.r_val(c)?);
        next = parts.next();
    }
    let mut align: Option<u64> = None;
    if let Some(a) = next {
        let n = a.strip_prefix("align ").ok_or_else(|| {
            r.e_syn(format!(
                "`{a}` is not an operand this reader knows on an `alloca`. trust-ir's printer \
                 emits `%count` and then `align N`, in that order; an unrecognised one — or one \
                 out of order — is refused rather than dropped"
            ))
        })?;
        align = Some(
            n.trim()
                .parse()
                .map_err(|_| r.e_syn(format!("alignment `{n}` is not a number")))?,
        );
        next = parts.next();
    }
    if let Some(extra) = next {
        return Err(r.e_syn(format!(
            "`{extra}` follows an `alloca`'s type, count and alignment; trust-ir's printer emits \
             nothing after them"
        )));
    }
    r.r_align(format!("alloca:{align:?}"));
    let opt = match count {
        Some(v) => Sx::tag("some", vec![num(v)]),
        None => Sx::tag("none", vec![]),
    };
    Ok(Sx::tag("alloca", vec![ty, opt]))
}

fn num(n: u32) -> Sx {
    Sx::a(n.to_string())
}

/// Split off the leading type token of `<ty> <rest>`.
fn split1(r: &EmittedReader, s: &str) -> Result<(String, String), EmittedError> {
    let s = s.trim();
    let (a, b) = s
        .split_once(' ')
        .ok_or_else(|| r.e_syn(format!("expected `<type> <operands>`, found `{s}`")))?;
    Ok((a.to_string(), b.to_string()))
}

/// Split off the leading type token of `<ty> <rest>` at the first TOP-LEVEL
/// space — one outside `<…>`, `(…)` and `[…]`.
///
/// [`split1`] cuts at the first space, which is right for every type token
/// the earlier arms meet and WRONG for a fat pointer: trust-ir prints
/// `FatPtrKind::Slice` as `slice ty.N` (`ty.rs`, with a space), so
/// `ptr_from_parts fatptr<slice ty.0> ptr %1, u64 %2` split at the first
/// space yields `fatptr<slice` and the rest is refused as a SYNTAX error at
/// `ptr ` — fail-closed, but for the wrong reason, and never reaching the
/// `ty()` arm that names the kind. This splitter carries the whole token to
/// `ty()`, so the refusal is the one that says which kind has no image.
fn split_ty(r: &EmittedReader, s: &str) -> Result<(String, String), EmittedError> {
    let s = s.trim();
    let mut depth = 0i32;
    for (i, c) in s.char_indices() {
        match c {
            '<' | '(' | '[' => depth += 1,
            '>' | ')' | ']' => depth -= 1,
            ' ' if depth == 0 => return Ok((s[..i].to_string(), s[i + 1..].to_string())),
            _ => {}
        }
    }
    Err(r.e_syn(format!("expected `<type> <operands>`, found `{s}`")))
}

/// `ptr_from_parts <ptr_ty> ptr %d, <metadata_ty> %m` — trust-ir
/// `display.rs`: `ptr_from_parts {ptr_ty} ptr %{}, {metadata_ty} %{}`. The
/// data operand's printed type is the literal keyword `ptr`, so it is matched
/// as one rather than read as a type; the metadata operand's type is read.
///
/// First reached by `<LevelArc as Deref>::deref` (the `ir_lzc` chain,
/// 2026-09-09), whose `expect` message is a `&str` built from a module-table
/// global and its byte length. Until then this arm did not exist and reader B
/// REFUSED the body by name — the recorded posture for a mnemonic outside the
/// fragment. The core order is the specification's `IRInst.ptrfromparts ptr_ty
/// metadata_ty data metadata` (`shape.rs`), the same one reader A emits.
/// `ptr_data` and `ptr_metadata` have their own arms since crystal E5.
fn ptr_from_parts(r: &mut EmittedReader, rest: &str) -> R {
    let (ptr_ty, tail) = split_ty(r, rest)?;
    // The fat-pointer type is routed through `ty()` BEFORE the operand syntax
    // is checked, so a kind outside the fragment is refused as "no image for
    // this kind" and not as a syntax error further along the line.
    let ptr_ty = r.r_ty(&ptr_ty)?;
    let tail = tail.strip_prefix("ptr ").ok_or_else(|| {
        r.e_syn(
            "ptr_from_parts needs `ptr %d` as its data operand: trust-ir's printer spells the \
             data type as the literal keyword `ptr`"
                .into(),
        )
    })?;
    let (data, md) = tail.split_once(", ").ok_or_else(|| {
        r.e_syn("ptr_from_parts needs `, <metadata_ty> %m` after the data operand".into())
    })?;
    let (md_ty, m) = split1(r, md)?;
    let md_ty = r.r_ty(&md_ty)?;
    let d = r.r_val(data)?;
    let m = r.r_val(&m)?;
    Ok(Sx::tag("ptrfromparts", vec![ptr_ty, md_ty, num(d), num(m)]))
}

fn binary(r: &mut EmittedReader, kind: &str, op: &str, tail: &str) -> R {
    let (ty, ops) = split1(r, tail)?;
    let vs = r.r_args(&ops)?;
    if vs.len() != 2 {
        return Err(r.e_syn(format!("`{op}` takes two operands")));
    }
    let mut v = vec![Sx::a(op), r.r_ty(&ty)?];
    v.extend(vs);
    Ok(Sx::tag(kind, v))
}

fn cmp(r: &mut EmittedReader, rest: &str, kind: &str) -> R {
    let (op, tail) = split1(r, rest)?;
    let alpha = shape::alphabet(kind);
    if !alpha.iter().any(|(c, _)| *c == op) {
        return Err(r.e_core(CoreError::NoImage(format!("{kind} operator `{op}`"))));
    }
    binary(r, kind, &op, &tail)
}

fn load(r: &mut EmittedReader, rest: &str, volatile: &str) -> R {
    // `<ty>, ptr %p[, align N]`.
    //
    // `align` has no `IRInst` field, so it cannot reach the core module — but
    // until 2026-08-20 this took `tail.split(',').next()` and dropped whatever
    // followed the pointer WITHOUT LOOKING AT IT, so `, align 8` and `, banana`
    // were equally invisible. It is now read and recorded (reader A's spelling,
    // so the two records compare), and anything else after the pointer is a
    // refusal.
    let (ty, tail) = rest
        .split_once(", ptr ")
        .ok_or_else(|| r.e_syn("load needs `, ptr %p`".into()))?;
    let mut parts = tail.split(',').map(str::trim);
    let ptr = parts
        .next()
        .ok_or_else(|| r.e_syn("load needs a pointer operand".into()))?;
    let ptr = r.r_val(ptr)?;
    let mut align: Option<u64> = None;
    for extra in parts.filter(|p| !p.is_empty()) {
        let n = extra.strip_prefix("align ").ok_or_else(|| {
            r.e_syn(format!(
                "`{extra}` is not an operand this reader knows on a `load`. The only trailing \
                 operand trust-ir's printer emits is `align N`; an unrecognised one is refused \
                 rather than dropped"
            ))
        })?;
        if align.is_some() {
            return Err(r.e_syn("a load carries two `align` operands".into()));
        }
        align = Some(
            n.trim()
                .parse()
                .map_err(|_| r.e_syn(format!("alignment `{n}` is not a number")))?,
        );
    }
    r.r_align(format!("load:{align:?}"));
    Ok(Sx::tag(
        "load",
        vec![r.r_ty(ty)?, num(ptr), Sx::a(volatile)],
    ))
}

/// `store <ty> <value>, ptr %p[, align N]` — the WRITE dual of `load`, first
/// reached by the `set_lean4_core_strict_monads` chain (2026-08-22). Until
/// then this arm did not exist and reader B REFUSED the fixture by name — the
/// recorded posture for a mnemonic outside the fragment. The printed order is
/// value-then-pointer; the core order is the specification's
/// `IRInst.store ty ptr value volatile`, the same one reader A emits.
fn store(r: &mut EmittedReader, rest: &str, volatile: &str) -> R {
    let (head, tail) = rest
        .split_once(", ptr ")
        .ok_or_else(|| r.e_syn("store needs `, ptr %p`".into()))?;
    let (ty, value) = split1(r, head)?;
    let mut parts = tail.split(',').map(str::trim);
    let ptr = parts
        .next()
        .ok_or_else(|| r.e_syn("store needs a pointer operand".into()))?;
    let ptr = r.r_val(ptr)?;
    let mut align: Option<u64> = None;
    for extra in parts.filter(|p| !p.is_empty()) {
        let n = extra.strip_prefix("align ").ok_or_else(|| {
            r.e_syn(format!(
                "`{extra}` is not an operand this reader knows on a `store`. The only trailing \
                 operand trust-ir's printer emits is `align N`; an unrecognised one is refused \
                 rather than dropped"
            ))
        })?;
        if align.is_some() {
            return Err(r.e_syn("a store carries two `align` operands".into()));
        }
        align = Some(
            n.trim()
                .parse()
                .map_err(|_| r.e_syn(format!("alignment `{n}` is not a number")))?,
        );
    }
    r.r_align(format!("store:{align:?}"));
    Ok(Sx::tag(
        "store",
        vec![
            r.r_ty(&ty)?,
            num(ptr),
            num(r.r_val(&value)?),
            Sx::a(volatile),
        ],
    ))
}

fn gep(r: &mut EmittedReader, rest: &str, inbounds: &str) -> R {
    // `<pointee>, ptr %base[, %i]*`
    let (ty, tail) = rest
        .split_once(", ptr ")
        .ok_or_else(|| r.e_syn("gep needs `, ptr %base`".into()))?;
    let mut parts = tail.split(',').map(str::trim);
    let base = parts
        .next()
        .ok_or_else(|| r.e_syn("gep needs a base pointer".into()))?;
    let base = r.r_val(base)?;
    let mut idx = Vec::new();
    for p in parts.filter(|p| !p.is_empty()) {
        idx.push(num(r.r_val(p)?));
    }
    Ok(Sx::tag(
        "gep",
        vec![r.r_ty(ty)?, num(base), Sx::tag("idx", idx), Sx::a(inbounds)],
    ))
}

fn switch(r: &mut EmittedReader, rest: &str) -> R {
    // `%v [ k: bbN(args) … default: bbM(args) ]`
    let (v, body) = rest
        .split_once(" [")
        .ok_or_else(|| r.e_syn("switch needs an arm list".into()))?;
    let value = r.r_val(v)?;
    let inner = body
        .trim()
        .strip_suffix(']')
        .ok_or_else(|| r.e_syn("unbalanced switch arm list".into()))?
        .trim();
    let mut cases = Vec::new();
    let mut dflt: Option<(u32, Vec<Sx>)> = None;
    for arm in inner.split_whitespace().collect::<Vec<_>>().chunks(2) {
        if arm.len() != 2 {
            return Err(r.e_syn(format!("switch arm `{}` is not `k: bbN`", arm.join(" "))));
        }
        let key = arm[0]
            .strip_suffix(':')
            .ok_or_else(|| r.e_syn(format!("switch arm key `{}` needs a `:`", arm[0])))?;
        let (t, a) = r.r_target(arm[1])?;
        if key == "default" {
            if dflt.is_some() {
                return Err(r.e_syn("switch has two default arms".into()));
            }
            dflt = Some((t, a));
        } else {
            let k: u128 = key
                .parse()
                .map_err(|_| r.e_syn(format!("switch case value `{key}` is not a number")))?;
            cases.push(Sx::tag(
                "case",
                vec![Sx::a(k.to_string()), num(t), Sx::tag("args", a)],
            ));
        }
    }
    let (dt, da) = dflt.ok_or_else(|| r.e_syn("switch has no default arm".into()))?;
    Ok(Sx::tag(
        "switch",
        vec![
            num(value),
            num(dt),
            Sx::tag("args", da),
            Sx::tag("cases", cases),
            // NOT WITNESSED. `display.rs` matches `Inst::Switch { .., .. }`
            // and never prints `exhaustive_enum_unreachable`, so no reader of
            // the text can supply it. `?` refuses to mint.
            Sx::a("?"),
        ],
    ))
}

/// Split `bbA[(args)], bbB[(args)]` at the comma that separates the two arms,
/// not at a comma inside an argument list.
fn split_arms(r: &EmittedReader, s: &str) -> Result<(String, String), EmittedError> {
    let mut depth = 0i32;
    for (i, c) in s.char_indices() {
        match c {
            '(' => depth += 1,
            ')' => depth -= 1,
            ',' if depth == 0 => return Ok((s[..i].to_string(), s[i + 1..].to_string())),
            _ => {}
        }
    }
    Err(r.e_syn(format!(
        "condbr arms `{s}` are not separated by a top-level comma"
    )))
}
