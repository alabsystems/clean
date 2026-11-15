// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0

use super::*;
use std::fmt;

mod observed_wire;

/// Bounds apply before allocating the descriptor tree. The module binary
/// reader imposes its own outer byte/allocation limits as well.
pub const MAX_ABI_TEXT_BYTES: usize = 1 << 20;
const MAX_NODES: usize = 65_536;
const MAX_DEPTH: usize = 32;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AbiTextError(pub String);
impl fmt::Display for AbiTextError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}
impl std::error::Error for AbiTextError {}

type R<T> = Result<T, AbiTextError>;
#[derive(Debug)]
enum N {
    Atom(String),
    Text(String),
    List(Vec<N>),
    Record(Vec<(String, N)>),
}
fn err<T>(message: &str) -> R<T> {
    Err(AbiTextError(message.into()))
}
fn atom(value: impl ToString) -> N {
    N::Atom(value.to_string())
}
fn string(value: &str) -> N {
    N::Text(value.into())
}
fn record(fields: Vec<(&str, N)>) -> N {
    N::Record(fields.into_iter().map(|(n, v)| (n.into(), v)).collect())
}
fn list<T>(items: &[T], f: impl Fn(&T) -> N) -> N {
    N::List(items.iter().map(f).collect())
}
fn option<T>(value: Option<&T>, f: impl Fn(&T) -> N) -> N {
    value.map_or_else(|| atom("none"), f)
}
fn fields(n: N, names: &[&str]) -> R<std::vec::IntoIter<N>> {
    let N::Record(fields) = n else {
        return err("expected named ABI record");
    };
    if fields.len() != names.len()
        || fields
            .iter()
            .zip(names)
            .any(|((name, _), expected)| name != expected)
    {
        return err("unknown, duplicate, missing, or out-of-order ABI field");
    }
    Ok(fields
        .into_iter()
        .map(|(_, v)| v)
        .collect::<Vec<_>>()
        .into_iter())
}
fn number(n: N) -> R<u64> {
    let N::Atom(value) = n else {
        return err("expected ABI unsigned integer");
    };
    if value.is_empty() || !value.bytes().all(|b| b.is_ascii_digit()) {
        return err("expected ABI unsigned integer");
    }
    value
        .parse()
        .map_err(|_| AbiTextError("ABI unsigned integer overflows".into()))
}
fn boolean(n: N) -> R<bool> {
    match n {
        N::Atom(s) if s == "true" => Ok(true),
        N::Atom(s) if s == "false" => Ok(false),
        _ => err("expected ABI boolean"),
    }
}
fn text(n: N) -> R<String> {
    match n {
        N::Text(s) => Ok(s),
        _ => err("expected ABI quoted string"),
    }
}
fn many<T>(n: N, f: impl Fn(N) -> R<T>) -> R<Vec<T>> {
    match n {
        N::List(values) => values.into_iter().map(f).collect(),
        _ => err("expected ABI list"),
    }
}
fn optional<T>(n: N, f: impl Fn(N) -> R<T>) -> R<Option<T>> {
    match n {
        N::Atom(s) if s == "none" => Ok(None),
        value => f(value).map(Some),
    }
}
fn u32_value(n: N) -> R<u32> {
    u32::try_from(number(n)?).map_err(|_| AbiTextError("ABI index exceeds u32".into()))
}
fn next(fields: &mut impl Iterator<Item = N>) -> N {
    fields.next().expect("field count checked")
}

fn attrs(a: &AbiAttributes) -> N {
    record(vec![
        (
            "extension",
            string(match a.extension {
                AbiExtension::None => "none",
                AbiExtension::Sign => "sign",
                AbiExtension::Zero => "zero",
            }),
        ),
        ("in_reg", atom(a.in_reg)),
        ("no_alias", atom(a.no_alias)),
        ("nonnull", atom(a.nonnull)),
        ("readonly", atom(a.readonly)),
        ("no_undef", atom(a.no_undef)),
        ("writable", atom(a.writable)),
        ("no_free", atom(a.no_free)),
        (
            "capture",
            string(match a.capture {
                AbiCapture::Any => "any",
                AbiCapture::ReadOnly => "readonly",
                AbiCapture::Address => "address",
                AbiCapture::None => "none",
            }),
        ),
        ("pointee_size", atom(a.pointee_size)),
        (
            "pointee_align",
            option(a.pointee_align.as_ref(), |v| atom(*v)),
        ),
    ])
}
fn read_attrs(n: N) -> R<AbiAttributes> {
    let mut f = fields(
        n,
        &[
            "extension",
            "in_reg",
            "no_alias",
            "nonnull",
            "readonly",
            "no_undef",
            "writable",
            "no_free",
            "capture",
            "pointee_size",
            "pointee_align",
        ],
    )?;
    Ok(AbiAttributes {
        extension: match text(next(&mut f))?.as_str() {
            "none" => AbiExtension::None,
            "sign" => AbiExtension::Sign,
            "zero" => AbiExtension::Zero,
            _ => return err("unknown ABI extension"),
        },
        in_reg: boolean(next(&mut f))?,
        no_alias: boolean(next(&mut f))?,
        nonnull: boolean(next(&mut f))?,
        readonly: boolean(next(&mut f))?,
        no_undef: boolean(next(&mut f))?,
        writable: boolean(next(&mut f))?,
        no_free: boolean(next(&mut f))?,
        capture: match text(next(&mut f))?.as_str() {
            "any" => AbiCapture::Any,
            "readonly" => AbiCapture::ReadOnly,
            "address" => AbiCapture::Address,
            "none" => AbiCapture::None,
            _ => return err("unknown ABI capture mode"),
        },
        pointee_size: number(next(&mut f))?,
        pointee_align: optional(next(&mut f), number)?,
    })
}
fn register(r: &AbiRegister) -> N {
    record(vec![
        (
            "class",
            string(match r.class {
                AbiRegisterClass::Integer => "integer",
                AbiRegisterClass::Float => "float",
                AbiRegisterClass::Vector => "vector",
            }),
        ),
        ("bytes", atom(r.bytes)),
    ])
}
fn read_register(n: N) -> R<AbiRegister> {
    let mut f = fields(n, &["class", "bytes"])?;
    Ok(AbiRegister {
        class: match text(next(&mut f))?.as_str() {
            "integer" => AbiRegisterClass::Integer,
            "float" => AbiRegisterClass::Float,
            "vector" => AbiRegisterClass::Vector,
            _ => return err("unknown ABI register class"),
        },
        bytes: number(next(&mut f))?,
    })
}
fn scalar(s: &AbiScalar) -> N {
    record(vec![
        ("register", register(&s.register)),
        ("source_offset", atom(s.source_offset)),
        ("source_bytes", atom(s.source_bytes)),
        ("value_bits", atom(s.value_bits)),
        ("attributes", attrs(&s.attributes)),
    ])
}
fn read_scalar(n: N) -> R<AbiScalar> {
    let mut f = fields(
        n,
        &[
            "register",
            "source_offset",
            "source_bytes",
            "value_bits",
            "attributes",
        ],
    )?;
    Ok(AbiScalar {
        register: read_register(next(&mut f))?,
        source_offset: number(next(&mut f))?,
        source_bytes: number(next(&mut f))?,
        value_bits: u16::try_from(number(next(&mut f))?)
            .map_err(|_| AbiTextError("ABI value_bits exceeds u16".into()))?,
        attributes: read_attrs(next(&mut f))?,
    })
}
fn uniform(u: &AbiUniform) -> N {
    record(vec![
        ("unit", register(&u.unit)),
        ("total", atom(u.total)),
        ("consecutive", atom(u.consecutive)),
    ])
}
fn read_uniform(n: N) -> R<AbiUniform> {
    let mut f = fields(n, &["unit", "total", "consecutive"])?;
    Ok(AbiUniform {
        unit: read_register(next(&mut f))?,
        total: number(next(&mut f))?,
        consecutive: boolean(next(&mut f))?,
    })
}
fn mode(m: &AbiPassMode) -> N {
    match m {
        AbiPassMode::Ignore => record(vec![("kind", string("ignore"))]),
        AbiPassMode::Direct(s) => record(vec![("kind", string("direct")), ("scalar", scalar(s))]),
        AbiPassMode::Pair(a, b) => record(vec![
            ("kind", string("pair")),
            ("first", scalar(a)),
            ("second", scalar(b)),
        ]),
        AbiPassMode::Cast {
            pad_i32,
            prefix,
            rest_offset,
            rest,
            attributes,
        } => record(vec![
            ("kind", string("cast")),
            ("pad_i32", atom(pad_i32)),
            ("prefix", list(prefix, register)),
            ("rest_offset", option(rest_offset.as_ref(), |v| atom(*v))),
            ("rest", uniform(rest)),
            ("attributes", attrs(attributes)),
        ]),
        AbiPassMode::Indirect {
            attributes,
            metadata_attributes,
            on_stack,
            caller_copy,
        } => record(vec![
            ("kind", string("indirect")),
            ("attributes", attrs(attributes)),
            (
                "metadata_attributes",
                option(metadata_attributes.as_ref(), attrs),
            ),
            ("on_stack", atom(on_stack)),
            ("caller_copy", atom(caller_copy)),
        ]),
    }
}
fn read_mode(n: N) -> R<AbiPassMode> {
    let N::Record(ref pairs) = n else {
        return err("expected ABI mode record");
    };
    let Some((name, N::Text(kind))) = pairs.first() else {
        return err("missing ABI mode kind");
    };
    if name != "kind" {
        return err("missing ABI mode kind");
    }
    match kind.as_str() {
        "ignore" => {
            fields(n, &["kind"])?;
            Ok(AbiPassMode::Ignore)
        }
        "direct" => {
            let mut f = fields(n, &["kind", "scalar"])?;
            next(&mut f);
            Ok(AbiPassMode::Direct(read_scalar(next(&mut f))?))
        }
        "pair" => {
            let mut f = fields(n, &["kind", "first", "second"])?;
            next(&mut f);
            Ok(AbiPassMode::Pair(
                read_scalar(next(&mut f))?,
                read_scalar(next(&mut f))?,
            ))
        }
        "cast" => {
            let mut f = fields(
                n,
                &[
                    "kind",
                    "pad_i32",
                    "prefix",
                    "rest_offset",
                    "rest",
                    "attributes",
                ],
            )?;
            next(&mut f);
            Ok(AbiPassMode::Cast {
                pad_i32: boolean(next(&mut f))?,
                prefix: many(next(&mut f), read_register)?,
                rest_offset: optional(next(&mut f), number)?,
                rest: read_uniform(next(&mut f))?,
                attributes: read_attrs(next(&mut f))?,
            })
        }
        "indirect" => {
            let mut f = fields(
                n,
                &[
                    "kind",
                    "attributes",
                    "metadata_attributes",
                    "on_stack",
                    "caller_copy",
                ],
            )?;
            next(&mut f);
            Ok(AbiPassMode::Indirect {
                attributes: read_attrs(next(&mut f))?,
                metadata_attributes: optional(next(&mut f), read_attrs)?,
                on_stack: boolean(next(&mut f))?,
                caller_copy: boolean(next(&mut f))?,
            })
        }
        _ => err("unknown ABI pass mode"),
    }
}
fn binding(b: &AbiBinding) -> N {
    let (place, index) = match b.place {
        AbiBindingPlace::Parameter(i) => ("parameter", i),
        AbiBindingPlace::Result(i) => ("result", i),
        AbiBindingPlace::HiddenResult(i) => ("hidden_result", i),
    };
    record(vec![
        ("place", string(place)),
        ("index", atom(index)),
        ("source_offset", atom(b.source_offset)),
        ("source_bytes", atom(b.source_bytes)),
        ("carrier_offset", atom(b.carrier_offset)),
        ("carrier_bytes", atom(b.carrier_bytes)),
    ])
}
fn read_binding(n: N) -> R<AbiBinding> {
    let mut f = fields(
        n,
        &[
            "place",
            "index",
            "source_offset",
            "source_bytes",
            "carrier_offset",
            "carrier_bytes",
        ],
    )?;
    let place = text(next(&mut f))?;
    let index = u32_value(next(&mut f))?;
    Ok(AbiBinding {
        place: match place.as_str() {
            "parameter" => AbiBindingPlace::Parameter(index),
            "result" => AbiBindingPlace::Result(index),
            "hidden_result" => AbiBindingPlace::HiddenResult(index),
            _ => return err("unknown ABI binding place"),
        },
        source_offset: number(next(&mut f))?,
        source_bytes: number(next(&mut f))?,
        carrier_offset: number(next(&mut f))?,
        carrier_bytes: number(next(&mut f))?,
    })
}
fn argument(a: &AbiArgument) -> N {
    record(vec![
        ("size", atom(a.size)),
        ("align", atom(a.align)),
        ("mode", mode(&a.mode)),
        ("bindings", list(&a.bindings, binding)),
    ])
}
fn read_argument(n: N) -> R<AbiArgument> {
    let mut f = fields(n, &["size", "align", "mode", "bindings"])?;
    Ok(AbiArgument {
        size: number(next(&mut f))?,
        align: number(next(&mut f))?,
        mode: read_mode(next(&mut f))?,
        bindings: many(next(&mut f), read_binding)?,
    })
}
fn target(t: &AbiTarget) -> N {
    record(vec![
        ("triple", string(&t.triple)),
        ("data_layout", string(&t.data_layout)),
        ("abi", string(&t.abi)),
        ("cpu", string(&t.cpu)),
        ("features", list(&t.features, |f| string(f))),
        ("target_spec", string(&t.target_spec)),
        ("pointer_bytes", atom(t.pointer_bytes)),
        ("little_endian", atom(t.little_endian)),
    ])
}
fn read_target(n: N) -> R<AbiTarget> {
    let mut f = fields(
        n,
        &[
            "triple",
            "data_layout",
            "abi",
            "cpu",
            "features",
            "target_spec",
            "pointer_bytes",
            "little_endian",
        ],
    )?;
    Ok(AbiTarget {
        triple: text(next(&mut f))?,
        data_layout: text(next(&mut f))?,
        abi: text(next(&mut f))?,
        cpu: text(next(&mut f))?,
        features: many(next(&mut f), text)?,
        target_spec: text(next(&mut f))?,
        pointer_bytes: u8::try_from(number(next(&mut f))?)
            .map_err(|_| AbiTextError("ABI pointer width exceeds u8".into()))?,
        little_endian: boolean(next(&mut f))?,
    })
}
fn frontend(t: &AbiFrontend) -> N {
    record(vec![
        ("name", string(&t.name)),
        ("revision", string(&t.revision)),
    ])
}
fn read_frontend(n: N) -> R<AbiFrontend> {
    let mut f = fields(n, &["name", "revision"])?;
    Ok(AbiFrontend {
        name: text(next(&mut f))?,
        revision: text(next(&mut f))?,
    })
}
fn signature(a: &SignatureAbi) -> N {
    record(vec![
        ("target", target(&a.target)),
        ("frontend", frontend(&a.frontend)),
        ("convention", string(&a.convention)),
        (
            "lowered_convention",
            string(&a.lowered_convention.to_string()),
        ),
        ("source_abi", string(&a.source_abi)),
        ("can_unwind", atom(a.can_unwind)),
        ("variadic", atom(a.variadic)),
        ("fixed_count", atom(a.fixed_count)),
        ("arguments", list(&a.arguments, argument)),
        ("result", argument(&a.result)),
    ])
}
fn read_calling_conv(n: N) -> R<crate::CallingConv> {
    let token = text(n)?;
    crate::CallingConv::ALL
        .into_iter()
        .find(|cc| cc.to_string() == token)
        .ok_or_else(|| AbiTextError("unknown lowered calling convention".into()))
}
fn read_signature(n: N) -> R<SignatureAbi> {
    let mut f = fields(
        n,
        &[
            "target",
            "frontend",
            "convention",
            "lowered_convention",
            "source_abi",
            "can_unwind",
            "variadic",
            "fixed_count",
            "arguments",
            "result",
        ],
    )?;
    Ok(SignatureAbi {
        target: read_target(next(&mut f))?,
        frontend: read_frontend(next(&mut f))?,
        convention: text(next(&mut f))?,
        lowered_convention: read_calling_conv(next(&mut f))?,
        source_abi: text(next(&mut f))?,
        can_unwind: boolean(next(&mut f))?,
        variadic: boolean(next(&mut f))?,
        fixed_count: u32_value(next(&mut f))?,
        arguments: many(next(&mut f), read_argument)?,
        result: read_argument(next(&mut f))?,
    })
}

fn emit(n: &N, out: &mut String) {
    match n {
        N::Atom(a) => out.push_str(a),
        N::Text(t) => {
            out.push('"');
            for ch in t.chars() {
                match ch {
                    '"' => out.push_str("\\\""),
                    '\\' => out.push_str("\\\\"),
                    '\n' => out.push_str("\\n"),
                    '\r' => out.push_str("\\r"),
                    '\t' => out.push_str("\\t"),
                    c if c.is_control() => {
                        use std::fmt::Write;
                        write!(out, "\\u{{{:x}}}", c as u32).unwrap();
                    }
                    c => out.push(c),
                }
            }
            out.push('"');
        }
        N::List(values) => {
            out.push('[');
            for (i, v) in values.iter().enumerate() {
                if i != 0 {
                    out.push(',');
                }
                emit(v, out);
            }
            out.push(']');
        }
        N::Record(fields) => {
            out.push('{');
            for (i, (key, v)) in fields.iter().enumerate() {
                if i != 0 {
                    out.push(',');
                }
                out.push_str(key);
                out.push('=');
                emit(v, out);
            }
            out.push('}');
        }
    }
}
/// Count the canonical tree before constructing it. Per-list bounds alone
/// permit a quadratic number of nested bindings across many source arguments.
/// The bounded decoder remains the final shared format check.
pub(super) fn validate_node_budget(a: &SignatureAbi) -> Result<(), String> {
    let mut nodes = 20usize; // root, target, frontend, scalar fields, argument list
    let mut add = |count: usize| -> Result<(), String> {
        nodes = nodes.checked_add(count).ok_or("ABI node count overflows")?;
        if nodes > MAX_NODES {
            return Err("ABI record count exceeds wire node limit".into());
        }
        Ok(())
    };
    add(a.target.features.len())?;
    for argument in a.arguments.iter().chain(std::iter::once(&a.result)) {
        let mode_nodes = match &argument.mode {
            AbiPassMode::Ignore => 2,
            AbiPassMode::Direct(_) => 21,
            AbiPassMode::Pair(_, _) => 40,
            AbiPassMode::Cast { prefix, .. } => 23usize
                .checked_add(
                    prefix
                        .len()
                        .checked_mul(3)
                        .ok_or("ABI node count overflows")?,
                )
                .ok_or("ABI node count overflows")?,
            AbiPassMode::Indirect {
                metadata_attributes,
                ..
            } => {
                if metadata_attributes.is_some() {
                    28
                } else {
                    17
                }
            }
        };
        add(4 + mode_nodes)?; // argument record, size, alignment and bindings list
        add(argument
            .bindings
            .len()
            .checked_mul(7)
            .ok_or("ABI node count overflows")?)?;
    }
    Ok(())
}

pub(super) fn encode(a: &SignatureAbi) -> String {
    let mut out = String::new();
    emit(&signature(a), &mut out);
    out
}
pub(super) fn decode(input: &str) -> R<SignatureAbi> {
    if input.len() > MAX_ABI_TEXT_BYTES {
        return err("ABI text exceeds byte limit");
    }
    let mut parser = Parser {
        input,
        offset: 0,
        nodes: 0,
    };
    let node = parser.node(0)?;
    if parser.offset != input.len() {
        return err("trailing ABI text");
    }
    let result = read_signature(node)?;
    if encode(&result) != input {
        return err("noncanonical ABI text");
    }
    Ok(result)
}
struct Parser<'a> {
    input: &'a str,
    offset: usize,
    nodes: usize,
}
impl Parser<'_> {
    fn peek(&self) -> Option<u8> {
        self.input.as_bytes().get(self.offset).copied()
    }
    fn expect(&mut self, b: u8) -> R<()> {
        if self.peek() != Some(b) {
            return err("invalid ABI text delimiter");
        }
        self.offset += 1;
        Ok(())
    }
    fn word(&mut self) -> R<String> {
        let start = self.offset;
        while self
            .peek()
            .is_some_and(|b| b.is_ascii_alphanumeric() || b == b'_')
        {
            self.offset += 1;
        }
        if start == self.offset {
            return err("expected ABI text word");
        }
        Ok(self.input[start..self.offset].into())
    }
    fn quoted(&mut self) -> R<String> {
        self.expect(b'"')?;
        let mut result = String::new();
        loop {
            let Some(ch) = self.input[self.offset..].chars().next() else {
                return err("unterminated ABI string");
            };
            self.offset += ch.len_utf8();
            match ch {
                '"' => return Ok(result),
                '\\' => {
                    let Some(escape) = self.peek() else {
                        return err("unterminated ABI escape");
                    };
                    self.offset += 1;
                    match escape {
                        b'"' => result.push('"'),
                        b'\\' => result.push('\\'),
                        b'n' => result.push('\n'),
                        b'r' => result.push('\r'),
                        b't' => result.push('\t'),
                        b'u' => {
                            self.expect(b'{')?;
                            let start = self.offset;
                            while self.peek().is_some_and(|b| b.is_ascii_hexdigit()) {
                                self.offset += 1;
                            }
                            if self.offset - start > 6 || self.offset == start {
                                return err("invalid ABI unicode escape");
                            }
                            let value = u32::from_str_radix(&self.input[start..self.offset], 16)
                                .map_err(|_| AbiTextError("invalid ABI unicode escape".into()))?;
                            self.expect(b'}')?;
                            result.push(char::from_u32(value).ok_or_else(|| {
                                AbiTextError("invalid ABI unicode scalar".into())
                            })?);
                        }
                        _ => return err("invalid ABI escape"),
                    }
                }
                c if c.is_control() => return err("unescaped ABI control character"),
                c => result.push(c),
            }
        }
    }
    fn node(&mut self, depth: usize) -> R<N> {
        self.nodes += 1;
        if depth > MAX_DEPTH || self.nodes > MAX_NODES {
            return err("ABI text exceeds structural limit");
        }
        match self.peek() {
            Some(b'"') => self.quoted().map(N::Text),
            Some(b'[') => {
                self.offset += 1;
                let mut values = Vec::new();
                if self.peek() != Some(b']') {
                    loop {
                        values.push(self.node(depth + 1)?);
                        if self.peek() != Some(b',') {
                            break;
                        }
                        self.offset += 1;
                    }
                }
                self.expect(b']')?;
                Ok(N::List(values))
            }
            Some(b'{') => {
                self.offset += 1;
                let mut fields = Vec::new();
                if self.peek() != Some(b'}') {
                    loop {
                        let key = self.word()?;
                        self.expect(b'=')?;
                        let value = self.node(depth + 1)?;
                        fields.push((key, value));
                        if self.peek() != Some(b',') {
                            break;
                        }
                        self.offset += 1;
                    }
                }
                self.expect(b'}')?;
                Ok(N::Record(fields))
            }
            _ => self.word().map(N::Atom),
        }
    }
}
