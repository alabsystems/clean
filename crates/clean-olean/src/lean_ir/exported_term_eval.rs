// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Execute pure IR from the selected Lean artifact.
//! The bounded interpreter implements only the object and call operations
//! whose host representations it can validate.

use std::collections::HashMap;
use std::rc::Rc;
use std::sync::Arc;

use clean_kernel::{BigNat, Expr, Level, Name};

use super::decode::IrDecoder;
use super::module_ir::DECL_MAP_EXT;
use super::types::{
    Alt, Arg, CtorInfo, Decl, Expr as IrExpr, FnBody, Instr, IrType, LitVal, Terminal, VarId,
};
use crate::header::OleanHeader;
use crate::region::CompactedRegion;
use crate::{read_exported_term_syntax, OleanError, OleanResult};

const MAX_DECLARATIONS: usize = 1 << 16;
pub(super) const MAX_EXECUTION_STEPS: usize = 1 << 14;
pub(super) const MAX_CALL_DEPTH: usize = 32;
pub(super) const MAX_ARGUMENTS: usize = 32;
pub(super) const MAX_NAT_LIMBS: usize = 256;
const MAX_SYNTAX_BYTES: usize = 4096;

mod provider_host;
mod providers;
pub use providers::ExportedTermProviders;

#[cfg(test)]
mod tests;

/// A prefix invocation parsed from a registered descriptor consisting of a
/// token followed by a numeral.
#[derive(Clone, Copy, Debug)]
pub struct ExportedNumeralSyntax<'a> {
    /// Exact typed syntax node kind from the imported parser descriptor.
    pub kind: &'a Name,
    /// Literal token spelling from the input span.
    pub token: &'a str,
    /// The original numeral spelling, including radix and digit separators.
    pub numeral: &'a str,
}

/// Run a global term elaborator whose registration and code occur in the
/// same captured base `.olean`. The caller supplies a numeral invocation
/// accepted by that artifact's parser descriptor and must type-check the
/// resulting expression in the receiving context.
///
/// # Errors
///
/// Refuses a foreign or malformed artifact, missing or competing handlers,
/// an unsupported ABI or operation, or exhaustion of the decode or execution
/// bounds. The interpreter has no host context, state, IO or native FFI.
pub fn evaluate_exported_term_elaborator(
    bytes: &[u8],
    handler: &Name,
    syntax: ExportedNumeralSyntax<'_>,
) -> OleanResult<Expr> {
    evaluate_handler(bytes, handler, syntax, None)
}

enum ProviderDeclaration {
    Code(Rc<Decl>),
    Host,
}
type ImportedDeclaration<'a> = dyn Fn(&Name) -> OleanResult<Option<ProviderDeclaration>> + 'a;

fn evaluate_handler(
    bytes: &[u8],
    handler: &Name,
    syntax: ExportedNumeralSyntax<'_>,
    imported: Option<&ImportedDeclaration<'_>>,
) -> OleanResult<Expr> {
    if syntax.token.is_empty()
        || syntax.token.len() > MAX_SYNTAX_BYTES
        || syntax.numeral.is_empty()
        || syntax.numeral.len() > MAX_SYNTAX_BYTES
    {
        return Err(refusal(handler, "invalid numeral syntax extent"));
    }
    // The registration decoder also checks the exact stable world identity.
    let registrations = read_exported_term_syntax(bytes)?;
    let mut matching = registrations
        .term_elaborators
        .iter()
        .filter(|row| row.entry.kind == *syntax.kind);
    let registered = matching
        .next()
        .is_some_and(|row| row.scope.is_none() && row.entry.declaration == *handler);
    if !registered || matching.next().is_some() {
        return Err(refusal(
            handler,
            "expected one global handler for the exact syntax kind",
        ));
    }

    let header = OleanHeader::parse(bytes)?;
    let region = CompactedRegion::new(bytes, header.base_addr);
    let part = region
        .ir_part_entries(region.root_ptr()?)
        .map_err(|error| refusal(handler, error.to_string()))?;
    let table = part
        .get(DECL_MAP_EXT)
        .ok_or_else(|| refusal(handler, "missing exported Lean.IR.declMapExt"))?;
    let mut program = Program::new(&region, table, handler)?;
    program.imported = imported;
    let declaration = program
        .declaration(handler)?
        .ok_or_else(|| refusal(handler, "missing exported IR body"))?;
    let Decl::FDecl { params, ty, .. } = declaration.as_ref() else {
        return Err(refusal(
            handler,
            "extern term elaborator has no executable exported body",
        ));
    };
    // Stable `TermElab` ABI: Syntax, optional expected expression, three
    // reader/state pairs, and an erased world token. An unused host argument
    // can be forwarded; inspecting one fails inside the interpreter.
    let abi = [
        IrType::TObject,
        IrType::TObject,
        IrType::Object,
        IrType::TObject,
        IrType::Object,
        IrType::TObject,
        IrType::Object,
        IrType::TObject,
        IrType::Void,
    ];
    if *ty != IrType::Object || !params.iter().map(|param| &param.ty).eq(abi.iter()) {
        return Err(refusal(
            handler,
            "unsupported Lean 4.36 TermElab IR signature",
        ));
    }
    let mut args = vec![Value::Syntax(Syntax::Invocation(syntax))];
    args.extend(std::iter::repeat_n(Value::Unavailable, abi.len() - 2));
    args.push(Value::Erased);
    match program.call(handler, args, 0)? {
        Value::TermResult(expr) => Ok(expr),
        _ => Err(refusal(
            handler,
            "term elaborator did not return an expression in EST.Out.ok",
        )),
    }
}

pub(super) fn evaluate_nat_in_region(
    region: &CompactedRegion<'_>,
    root: u64,
    function: &Name,
    arguments: &[BigNat],
) -> OleanResult<BigNat> {
    if arguments.len() > MAX_ARGUMENTS {
        return Err(refusal(
            function,
            "Nat argument count exceeds execution bound",
        ));
    }
    if arguments
        .iter()
        .any(|argument| argument.limbs().len() > MAX_NAT_LIMBS)
    {
        return Err(refusal(function, "Nat argument exceeds execution bound"));
    }
    let part = region
        .ir_part_entries(root)
        .map_err(|error| refusal(function, error))?;
    if !part.is_module {
        return Err(refusal(function, "captured Nat IR is not module data"));
    }
    let table = part
        .get(DECL_MAP_EXT)
        .ok_or_else(|| refusal(function, "missing Lean.IR.declMapExt in captured IR data"))?;
    let mut program = Program::new(region, table, function)?;
    let declaration = program
        .declaration(function)?
        .ok_or_else(|| refusal(function, "missing function body in captured IR data"))?;
    let Decl::FDecl { params, ty, .. } = declaration.as_ref() else {
        return Err(refusal(
            function,
            "function in captured IR data is an extern",
        ));
    };
    if *ty != IrType::TObject
        || params.len() != arguments.len()
        || !params.iter().all(|param| param.ty == IrType::TObject)
    {
        return Err(refusal(
            function,
            "compiled IR signature does not match the exported Nat type",
        ));
    }
    let arguments = arguments
        .iter()
        .map(|value| Value::Nat(Rc::new(value.clone())))
        .collect();
    match program.call(function, arguments, 0)? {
        Value::Nat(value) => Ok(value.as_ref().clone()),
        _ => Err(refusal(function, "function returned a non-Nat value")),
    }
}

/// Decode the numeral prefix described by a typed ParserDescr constant in an
/// already admitted stable base region. No attached IR part is consulted.
pub(crate) fn evaluate_exported_numeral_parser_in_region(
    region: &CompactedRegion<'_>,
    root: u64,
    name: &Name,
) -> OleanResult<Option<(Name, u64, Arc<str>)>> {
    let part = region
        .ir_part_entries(root)
        .map_err(|error| refusal(name, error))?;
    let Some(table) = part.get(DECL_MAP_EXT) else {
        return Ok(None);
    };
    let mut program = Program::new(region, table, name)?;
    let Some(declaration) = program.declaration(name)? else {
        return Ok(None);
    };
    let Decl::FDecl { params, ty, .. } = declaration.as_ref() else {
        return Ok(None);
    };
    if !params.is_empty() || *ty != IrType::Object {
        return Err(refusal(
            name,
            "exported ParserDescr has an invalid IR signature",
        ));
    }
    match program.call(name, Vec::new(), 0) {
        Ok(Value::Descriptor(Descriptor::Prefix {
            kind,
            precedence,
            literal,
        })) => Ok(Some((kind, precedence, Arc::from(literal.as_ref())))),
        Ok(Value::Descriptor(_)) => Ok(None),
        Ok(_) => Err(refusal(
            name,
            "exported parser did not return a ParserDescr",
        )),
        Err(_) if program.unsupported => Ok(None),
        Err(error) => Err(error),
    }
}

fn refusal(function: &Name, detail: impl std::fmt::Display) -> OleanError {
    OleanError::Region(format!("Lean IR {function}: {detail}"))
}

#[derive(Clone, Copy)]
enum Syntax<'a> {
    Invocation(ExportedNumeralSyntax<'a>),
    Numeral(&'a str),
    Atom(&'a str),
    Missing,
}

impl<'a> Syntax<'a> {
    fn kind(self) -> Name {
        match self {
            Self::Invocation(syntax) => syntax.kind.clone(),
            Self::Numeral(_) => Name::anon().str("num"),
            Self::Atom(text) => Name::anon().str(text),
            Self::Missing => Name::anon().str("missing"),
        }
    }

    fn arg(self, index: &BigNat) -> Self {
        match (self, index.to_u64()) {
            (Self::Invocation(syntax), Some(0)) => Self::Atom(syntax.token),
            (Self::Invocation(syntax), Some(1)) => Self::Numeral(syntax.numeral),
            (Self::Numeral(text), Some(0)) => Self::Atom(text),
            _ => Self::Missing,
        }
    }
}

#[derive(Clone)]
enum Value<'a> {
    Erased,
    Unavailable,
    Syntax(Syntax<'a>),
    Nat(Rc<BigNat>),
    String(Rc<str>),
    Name(Name),
    UInt8(u8),
    Expr(Expr),
    TermResult(Expr),
    Descriptor(Descriptor),
}

/// Bottom-up recognition avoids retaining or recursively dropping a full
/// descriptor graph for forms outside this parser's supported grammar.
#[derive(Clone)]
enum Descriptor {
    Num,
    Symbol(Rc<str>),
    NumeralSequence(Rc<str>),
    Prefix {
        kind: Name,
        precedence: u64,
        literal: Rc<str>,
    },
    Other,
}

impl Value<'_> {
    fn matches_type(&self, ty: &IrType) -> bool {
        match ty {
            IrType::Object => match self {
                Self::Nat(value) => !is_tagged_nat(value),
                Self::Name(name) => !name.is_anon(),
                Self::Syntax(Syntax::Missing) | Self::Erased | Self::UInt8(_) => false,
                _ => true,
            },
            IrType::TObject => !matches!(self, Self::Erased | Self::UInt8(_)),
            IrType::Tagged => matches!(self, Self::Nat(value) if is_tagged_nat(value)),
            IrType::UInt8 => matches!(self, Self::UInt8(_)),
            IrType::Erased | IrType::Void => matches!(self, Self::Erased),
            _ => false,
        }
    }
}

pub(super) fn is_tagged_nat(value: &BigNat) -> bool {
    value.to_u64().is_some_and(|value| value <= u64::MAX >> 1)
}

type Locals<'a> = HashMap<VarId, Value<'a>>;

pub(super) struct Program<'r, 'bytes> {
    decoder: IrDecoder<'r, 'bytes>,
    imported: Option<&'r ImportedDeclaration<'r>>,
    declarations: HashMap<Name, u64>,
    decoded: HashMap<Name, Option<Rc<Decl>>>,
    steps: usize,
    unsupported: bool,
}

impl<'r, 'bytes> Program<'r, 'bytes> {
    pub(super) fn new(
        region: &'r CompactedRegion<'bytes>,
        table: u64,
        handler: &Name,
    ) -> OleanResult<Self> {
        let decoder = IrDecoder::for_stable_execution(region);
        let mut declarations = HashMap::new();
        for pointer in decoder
            .array(table, DECL_MAP_EXT, MAX_DECLARATIONS)
            .map_err(|error| refusal(handler, error.to_string()))?
        {
            let name = decoder
                .decl_name(pointer)
                .ok_or_else(|| refusal(handler, "invalid IR declaration name or header"))?;
            if declarations.insert(name.clone(), pointer).is_some() {
                return Err(refusal(handler, format!("duplicate IR declaration {name}")));
            }
        }
        Ok(Self {
            decoder,
            imported: None,
            declarations,
            decoded: HashMap::new(),
            steps: MAX_EXECUTION_STEPS,
            unsupported: false,
        })
    }

    pub(super) fn declaration(&mut self, name: &Name) -> OleanResult<Option<Rc<Decl>>> {
        if let Some(declaration) = self.decoded.get(name) {
            return Ok(declaration.clone());
        }
        if let Some(lookup) = self.imported {
            if let Some(declaration) = lookup(name)? {
                let code = match declaration {
                    ProviderDeclaration::Code(code) => Some(code),
                    ProviderDeclaration::Host => None,
                };
                self.decoded.insert(name.clone(), code.clone());
                return Ok(code);
            }
        }
        let Some(&pointer) = self.declarations.get(name) else {
            return Ok(None);
        };
        let declaration = self
            .decoder
            .decl(pointer)
            .map_err(|error| refusal(name, error.to_string()))?;
        let declaration = Rc::new(declaration);
        self.decoded
            .insert(name.clone(), Some(Rc::clone(&declaration)));
        Ok(Some(declaration))
    }

    fn tick(&mut self, function: &Name) -> OleanResult<()> {
        self.steps = self
            .steps
            .checked_sub(1)
            .ok_or_else(|| refusal(function, "execution step limit"))?;
        Ok(())
    }

    fn unsupported(&mut self, function: &Name, detail: impl std::fmt::Display) -> OleanError {
        self.unsupported = true;
        refusal(function, detail)
    }

    fn call<'a>(
        &mut self,
        function: &Name,
        args: Vec<Value<'a>>,
        depth: usize,
    ) -> OleanResult<Value<'a>> {
        self.tick(function)?;
        if depth >= MAX_CALL_DEPTH || args.len() > MAX_ARGUMENTS {
            return Err(refusal(function, "call depth or arity limit"));
        }
        let Some(declaration) = self.declaration(function)? else {
            if host_operation(function).is_none()
                && !args.iter().any(|arg| matches!(arg, Value::Unavailable))
            {
                return Err(self.unsupported(function, "unsupported host call"));
            }
            return host_call(function, &args);
        };
        let Decl::FDecl {
            params,
            ty,
            body,
            info,
            ..
        } = declaration.as_ref()
        else {
            return Err(self.unsupported(function, "unsupported extern call"));
        };
        if info.sorry_dep.is_some() || params.len() != args.len() {
            return Err(refusal(function, "sorry dependency or call arity mismatch"));
        }
        let mut locals = HashMap::new();
        for (param, value) in params.iter().zip(args) {
            bind(function, &mut locals, param.x, &param.ty, value)?;
        }
        let value = self.block(function, body, &mut locals, depth)?;
        if matches!(value, Value::Unavailable) || !value.matches_type(ty) {
            return Err(refusal(
                function,
                "return value has unsupported state or IR type",
            ));
        }
        Ok(value)
    }

    fn block<'a>(
        &mut self,
        function: &Name,
        block: &FnBody,
        locals: &mut Locals<'a>,
        depth: usize,
    ) -> OleanResult<Value<'a>> {
        let mut current = block;
        loop {
            for instr in &current.instrs {
                self.tick(function)?;
                match instr {
                    Instr::VDecl { x, ty, e } => {
                        let value = self.value(function, ty, e, locals, depth)?;
                        bind(function, locals, *x, ty, value)?;
                    }
                    Instr::Inc { x, .. } | Instr::Dec { x, .. } | Instr::Del { x } => {
                        // Immutable owned values have no observable RC. The
                        // interpreter refuses state access and reuse/mutation.
                        let value = local(function, locals, *x)?;
                        if matches!(value, Value::Unavailable | Value::Erased | Value::UInt8(_)) {
                            return Err(refusal(
                                function,
                                "RC operation on unavailable or unboxed value",
                            ));
                        }
                    }
                    Instr::JDecl { .. } => {
                        return Err(self.unsupported(function, "unsupported jdecl"))
                    }
                    Instr::Set { .. } => return Err(self.unsupported(function, "unsupported set")),
                    Instr::SetTag { .. } => {
                        return Err(self.unsupported(function, "unsupported setTag"))
                    }
                    Instr::USet { .. } => {
                        return Err(self.unsupported(function, "unsupported uset"))
                    }
                    Instr::SSet { .. } => {
                        return Err(self.unsupported(function, "unsupported sset"))
                    }
                }
            }
            self.tick(function)?;
            match &current.terminal {
                Terminal::Ret(arg) => return argument(function, locals, *arg),
                Terminal::Case {
                    tid,
                    x,
                    x_type,
                    alts,
                } => {
                    if !named(tid, "UInt8") || *x_type != IrType::UInt8 {
                        return Err(
                            self.unsupported(function, format!("unsupported case on {tid}"))
                        );
                    }
                    let Value::UInt8(tag) = local(function, locals, *x)? else {
                        return Err(refusal(function, "case scrutinee is not a UInt8"));
                    };
                    current = bool_case(function, *tag, alts)?;
                }
                Terminal::Jmp { .. } => return Err(self.unsupported(function, "unsupported jmp")),
                Terminal::Unreachable => return Err(refusal(function, "reached unreachable IR")),
            }
        }
    }

    fn value<'a>(
        &mut self,
        function: &Name,
        ty: &IrType,
        expression: &IrExpr,
        locals: &Locals<'a>,
        depth: usize,
    ) -> OleanResult<Value<'a>> {
        match expression {
            IrExpr::Lit(LitVal::Num(n)) if *ty == IrType::UInt8 => {
                let tag = n
                    .to_u64()
                    .and_then(|n| u8::try_from(n).ok())
                    .ok_or_else(|| refusal(function, "UInt8 literal out of range"))?;
                Ok(Value::UInt8(tag))
            }
            IrExpr::Lit(LitVal::Num(n)) => {
                if n.limbs().len() > MAX_NAT_LIMBS {
                    return Err(refusal(function, "Nat literal exceeds execution bound"));
                }
                Ok(Value::Nat(Rc::new(BigNat::from_limbs(n.limbs().to_vec()))))
            }
            IrExpr::Lit(LitVal::Str(text)) => Ok(Value::String(Rc::from(text.as_str()))),
            IrExpr::Fap { f, args } => {
                if args.len() > MAX_ARGUMENTS {
                    return Err(refusal(f, "call arity limit"));
                }
                let args = args
                    .iter()
                    .map(|arg| argument(function, locals, *arg))
                    .collect::<OleanResult<Vec<_>>>()?;
                self.call(f, args, depth + 1)
            }
            IrExpr::Ctor { info, args } => {
                if let Some(tag) = descriptor_constructor_tag(&info.name) {
                    if args.len() > 3 {
                        return Err(refusal(function, format!("invalid {} arity", info.name)));
                    }
                    let args = args
                        .iter()
                        .map(|arg| argument(function, locals, *arg))
                        .collect::<OleanResult<Vec<_>>>()?;
                    return descriptor_constructor(function, info, tag, &args)
                        .map(Value::Descriptor);
                }
                if !named(&info.name, "EST.Out.ok") {
                    return Err(self
                        .unsupported(function, format!("unsupported constructor {}", info.name)));
                }
                if !constructor(info, 0, 1) {
                    return Err(refusal(function, "invalid EST.Out.ok layout"));
                }
                let [arg] = args.as_slice() else {
                    return Err(refusal(function, "invalid EST.Out.ok field count"));
                };
                match argument(function, locals, *arg)? {
                    Value::Expr(expr) => Ok(Value::TermResult(expr)),
                    _ => Err(refusal(function, "EST.Out.ok field is not a Lean Expr")),
                }
            }
            IrExpr::Reset { .. } => Err(self.unsupported(function, "unsupported reset")),
            IrExpr::Reuse { .. } => Err(self.unsupported(function, "unsupported reuse")),
            IrExpr::Proj { .. } => Err(self.unsupported(function, "unsupported proj")),
            IrExpr::UProj { .. } => Err(self.unsupported(function, "unsupported uproj")),
            IrExpr::SProj { .. } => Err(self.unsupported(function, "unsupported sproj")),
            IrExpr::Pap { .. } => Err(self.unsupported(function, "unsupported pap")),
            IrExpr::Ap { .. } => Err(self.unsupported(function, "unsupported ap")),
            IrExpr::Box { .. } => Err(self.unsupported(function, "unsupported box")),
            IrExpr::Unbox { .. } => Err(self.unsupported(function, "unsupported unbox")),
            IrExpr::IsShared { .. } => Err(self.unsupported(function, "unsupported isShared")),
        }
    }
}

fn local<'a, 'locals>(
    function: &Name,
    locals: &'locals Locals<'a>,
    id: VarId,
) -> OleanResult<&'locals Value<'a>> {
    locals
        .get(&id)
        .ok_or_else(|| refusal(function, format!("unbound variable x_{}", id.0)))
}

fn bind<'a>(
    function: &Name,
    locals: &mut Locals<'a>,
    id: VarId,
    ty: &IrType,
    value: Value<'a>,
) -> OleanResult<()> {
    if !value.matches_type(ty) {
        return Err(refusal(
            function,
            format!("x_{} has unsupported representation for {ty:?}", id.0),
        ));
    }
    if locals.insert(id, value).is_some() {
        return Err(refusal(function, format!("duplicate variable x_{}", id.0)));
    }
    Ok(())
}

fn argument<'a>(function: &Name, locals: &Locals<'a>, arg: Arg) -> OleanResult<Value<'a>> {
    match arg {
        Arg::Var(id) => local(function, locals, id).cloned(),
        Arg::Erased => Ok(Value::Erased),
    }
}

fn named(name: &Name, dotted: &str) -> bool {
    *name == Name::from_string(dotted)
}

fn constructor(info: &CtorInfo, tag: u64, fields: u64) -> bool {
    (info.cidx, info.size, info.usize, info.ssize) == (tag, fields, 0, 0)
}

fn descriptor_constructor_tag(name: &Name) -> Option<u64> {
    [
        ("Lean.ParserDescr.const", 0),
        ("Lean.ParserDescr.binary", 2),
        ("Lean.ParserDescr.node", 3),
        ("Lean.ParserDescr.symbol", 5),
    ]
    .into_iter()
    .find_map(|(ctor, tag)| named(name, ctor).then_some(tag))
}

fn descriptor_constructor(
    function: &Name,
    info: &CtorInfo,
    tag: u64,
    args: &[Value<'_>],
) -> OleanResult<Descriptor> {
    let fields = if matches!(tag, 0 | 5) { 1 } else { 3 };
    if !constructor(info, tag, fields) {
        return Err(refusal(function, format!("invalid {} layout", info.name)));
    }
    match (tag, args) {
        (0, [Value::Name(parser)]) => Ok(if named(parser, "num") {
            Descriptor::Num
        } else {
            Descriptor::Other
        }),
        (5, [Value::String(text)]) => Ok(Descriptor::Symbol(Rc::clone(text))),
        (2, [Value::Name(combinator), Value::Descriptor(left), Value::Descriptor(right)]) => {
            match (left, right) {
                (Descriptor::Symbol(text), Descriptor::Num) if named(combinator, "andthen") => {
                    Ok(Descriptor::NumeralSequence(Rc::clone(text)))
                }
                _ => Ok(Descriptor::Other),
            }
        }
        (3, [Value::Name(kind), Value::Nat(precedence), Value::Descriptor(body)]) => {
            match (precedence.to_u64(), body) {
                (Some(precedence), Descriptor::NumeralSequence(text)) => Ok(Descriptor::Prefix {
                    kind: kind.clone(),
                    precedence,
                    literal: Rc::clone(text),
                }),
                _ => Ok(Descriptor::Other),
            }
        }
        _ => Err(refusal(
            function,
            format!("invalid {} arguments", info.name),
        )),
    }
}

fn bool_case<'a>(function: &Name, tag: u8, alternatives: &'a [Alt]) -> OleanResult<&'a FnBody> {
    let mut branches = [None; 2];
    let mut fallback = None;
    for alternative in alternatives {
        let (slot, body) = match alternative {
            Alt::Ctor { info, body }
                if named(&info.name, "Bool.false") && constructor(info, 0, 0) =>
            {
                (&mut branches[0], body)
            }
            Alt::Ctor { info, body }
                if named(&info.name, "Bool.true") && constructor(info, 1, 0) =>
            {
                (&mut branches[1], body)
            }
            Alt::Ctor { info, .. } => {
                return Err(refusal(
                    function,
                    format!("unsupported case alternative {}", info.name),
                ));
            }
            Alt::Default { body } => (&mut fallback, body),
        };
        if slot.replace(body).is_some() {
            return Err(refusal(function, "duplicate Bool case alternative"));
        }
    }
    branches
        .get(usize::from(tag))
        .copied()
        .flatten()
        .or(fallback)
        .ok_or_else(|| refusal(function, "missing Bool case alternative"))
}

fn host_operation(name: &Name) -> Option<&'static str> {
    [
        "Lean.Name.mkStr1",
        "Lean.Name.mkStr2",
        "Lean.Syntax.isOfKind",
        "Lean.Syntax.getArg",
        "Lean.TSyntax.getNat",
        "Nat.add",
        "Lean.mkNatLit",
    ]
    .into_iter()
    .find(|operation| named(name, operation))
}

fn host_call<'a>(name: &Name, args: &[Value<'a>]) -> OleanResult<Value<'a>> {
    if args.iter().any(|arg| matches!(arg, Value::Unavailable)) {
        return Err(refusal(name, "call requires unavailable elaborator state"));
    }
    match (host_operation(name), args) {
        (Some("Lean.Name.mkStr1"), [Value::String(text)]) => {
            Ok(Value::Name(Name::anon().str(text.as_ref())))
        }
        (Some("Lean.Name.mkStr2"), [Value::String(first), Value::String(second)]) => Ok(
            Value::Name(Name::anon().str(first.as_ref()).str(second.as_ref())),
        ),
        (Some("Lean.Syntax.isOfKind"), [Value::Syntax(syntax), Value::Name(kind)]) => {
            Ok(Value::UInt8(u8::from(syntax.kind() == *kind)))
        }
        (Some("Lean.Syntax.getArg"), [Value::Syntax(syntax), Value::Nat(index)]) => {
            Ok(Value::Syntax(syntax.arg(index)))
        }
        (Some("Lean.TSyntax.getNat"), [Value::Syntax(Syntax::Numeral(text))]) => numeral(text)
            .map(|value| Value::Nat(Rc::new(value)))
            .ok_or_else(|| refusal(name, "invalid or oversized numeral syntax")),
        (Some("Nat.add"), [Value::Nat(a), Value::Nat(b)]) => {
            let sum = a.checked_add_big(b);
            if sum.limbs().len() > MAX_NAT_LIMBS {
                return Err(refusal(name, "Nat result exceeds execution bound"));
            }
            Ok(Value::Nat(Rc::new(sum)))
        }
        (Some("Lean.mkNatLit"), [Value::Nat(n)]) => {
            // Lean constructs OfNat.ofNat at Nat, including the actual
            // instance, over the raw kernel literal.
            let literal = Expr::bignat_lit(n.as_ref().clone());
            let instance = Expr::app(Expr::const_str("instOfNatNat"), literal.clone());
            Ok(Value::Expr(Expr::apps(
                Expr::const_(Name::from_string("OfNat.ofNat"), vec![Level::zero()]),
                [Expr::const_str("Nat"), literal, instance],
            )))
        }
        _ => Err(refusal(
            name,
            "unsupported host call or argument representation",
        )),
    }
}

fn numeral(text: &str) -> Option<BigNat> {
    let (digits, radix) =
        if let Some(digits) = text.strip_prefix("0x").or_else(|| text.strip_prefix("0X")) {
            (digits, 16)
        } else if let Some(digits) = text.strip_prefix("0o").or_else(|| text.strip_prefix("0O")) {
            (digits, 8)
        } else if let Some(digits) = text.strip_prefix("0b").or_else(|| text.strip_prefix("0B")) {
            (digits, 2)
        } else {
            (text, 10)
        };
    BigNat::from_radix_str(digits, radix)
}
