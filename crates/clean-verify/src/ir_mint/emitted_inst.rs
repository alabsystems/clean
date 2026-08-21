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
        let mapped = r.r_global(id)?;
        return Ok(Sx::tag("globaladdr", vec![num(mapped)]));
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
