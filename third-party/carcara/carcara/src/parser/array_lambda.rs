// Copyright 2026 Clean contributors
// Licensed under the Apache License, Version 2.0

//! Untrusted, lexical lambda-role inference before the ordinary typed parse.
//!
//! This is constructor unification (Robinson's algorithm) over a finite graph,
//! not Function/Array subtyping. A hint can select only a literal lambda at its
//! exact token position. The ordinary parser still validates every real sort,
//! declaration and term. Aliases share graph nodes through lexical frames;
//! their spelling never authorizes a conversion of a declared function value.
use super::*;
use std::collections::HashSet;

type Id = usize;
struct Syntax<'s> {
    input: &'s str,
    token: Token,
    position: Position,
    children: Vec<Id>,
}
#[derive(Clone)]
enum Ty {
    Unknown,
    Atom,
    Array(Id, Id),
    Function(Vec<Id>, Id),
    Lambda(Position, Vec<Id>, Id),
}
struct Types {
    parent: Vec<Id>,
    kinds: Vec<Ty>,
    literals: Vec<(Position, Id)>,
}
impl Types {
    fn new() -> Self {
        Self {
            parent: Vec::new(),
            kinds: Vec::new(),
            literals: Vec::new(),
        }
    }
    fn add(&mut self, kind: Ty) -> Id {
        let id = self.parent.len();
        self.parent.push(id);
        if let Ty::Lambda(position, _, _) = &kind {
            self.literals.push((*position, id));
        }
        self.kinds.push(kind);
        id
    }
    fn root(&mut self, mut id: Id) -> Id {
        let start = id;
        while self.parent[id] != id {
            id = self.parent[id];
        }
        let mut current = start;
        while self.parent[current] != current {
            let next = self.parent[current];
            self.parent[current] = id;
            current = next;
        }
        id
    }
    fn unify(&mut self, left: Id, right: Id) -> Result<(), ParserError> {
        let mut pending = vec![(left, right)];
        while let Some((a, b)) = pending.pop() {
            if crate::checker::deadline::expired() {
                return Err(ParserError::DeadlineExceeded);
            }
            let (a, b) = (self.root(a), self.root(b));
            if a == b {
                continue;
            }
            let (left, right) = (self.kinds[a].clone(), self.kinds[b].clone());
            let merged = match (left, right) {
                (Ty::Unknown, other) | (other, Ty::Unknown) => other,
                (Ty::Atom, Ty::Atom) => Ty::Atom,
                (Ty::Array(x, y), Ty::Array(u, v)) => {
                    pending.extend([(x, u), (y, v)]);
                    Ty::Array(x, y)
                }
                (Ty::Function(xs, y), Ty::Function(us, v)) if xs.len() == us.len() => {
                    pending.extend(xs.iter().copied().zip(us));
                    pending.push((y, v));
                    Ty::Function(xs, y)
                }
                (Ty::Lambda(p, xs, y), Ty::Lambda(q, us, v)) if xs.len() == us.len() => {
                    // Keep both literal positions tied to the same constructor.
                    // Their role is collected from the final representative.
                    pending.extend(xs.iter().copied().zip(us));
                    pending.push((y, v));
                    let _ = q;
                    Ty::Lambda(p, xs, y)
                }
                (Ty::Lambda(_, xs, y), Ty::Array(u, v))
                | (Ty::Array(u, v), Ty::Lambda(_, xs, y))
                    if xs.len() == 1 =>
                {
                    pending.extend([(xs[0], u), (y, v)]);
                    Ty::Array(u, v)
                }
                (Ty::Lambda(_, xs, y), Ty::Function(us, v))
                | (Ty::Function(us, v), Ty::Lambda(_, xs, y))
                    if xs.len() == us.len() =>
                {
                    pending.extend(xs.iter().copied().zip(us));
                    pending.push((y, v));
                    Ty::Function(xs, y)
                }
                // Atom carries no lambda-relevant structure; exact primitive,
                // datatype and parametric equality stays with the real parser.
                (Ty::Atom, _) | (_, Ty::Atom) => return Err(invalid()),
                _ => return Err(invalid()),
            };
            self.parent[b] = a;
            self.kinds[a] = merged;
        }
        Ok(())
    }
    fn finish(mut self) -> Result<HashSet<Position>, ParserError> {
        // Propagate the representative's constructor to EVERY original literal,
        // including two lambdas equated before either acquired an Array context.
        let mut arrays = HashSet::new();
        for (position, id) in std::mem::take(&mut self.literals) {
            let root = self.root(id);
            if matches!(self.kinds[root], Ty::Array(..)) {
                arrays.insert(position);
            }
        }
        // Reject cyclic type constraints rather than producing recursive types.
        let mut color = vec![0u8; self.kinds.len()];
        let mut todo = Vec::new();
        for id in 0..self.kinds.len() {
            let root = self.root(id);
            if color[root] == 2 {
                continue;
            }
            todo.push((root, false));
            while let Some((node, closing)) = todo.pop() {
                if crate::checker::deadline::expired() {
                    return Err(ParserError::DeadlineExceeded);
                }
                let node = self.root(node);
                if closing {
                    color[node] = 2;
                    continue;
                }
                if color[node] == 2 {
                    continue;
                }
                if color[node] == 1 {
                    return Err(invalid());
                }
                color[node] = 1;
                todo.push((node, true));
                match &self.kinds[node] {
                    Ty::Array(a, b) => {
                        todo.push((*a, false));
                        todo.push((*b, false));
                    }
                    Ty::Function(args, result) | Ty::Lambda(_, args, result) => {
                        todo.push((*result, false));
                        for arg in args {
                            todo.push((*arg, false));
                        }
                    }
                    _ => {}
                }
            }
        }
        Ok(arrays)
    }
}
fn invalid() -> ParserError {
    ParserError::InvalidArrayLambda
}
struct Frame {
    parent: usize,
    names: HashMap<String, Id>,
}
struct Inference<'a, 'p, 's> {
    parser: &'a mut Parser<'p, 's>,
    syntax: Vec<Syntax<'s>>,
    types: Types,
    values: Vec<Option<Id>>,
    frames: Vec<Frame>,
    named: HashMap<String, Id>,
    sort_types: HashMap<Rc<Sort>, Id>,
}
enum Work {
    Visit(Id, usize),
    App(Id, usize),
    Alias(Id, Id),
    Binder(Id, Position, Vec<Id>, Id, Reserved),
    Named(Id, Id, Option<String>),
    Let(Id, usize, Vec<(String, Id)>, Id),
    Match(Id, Vec<Id>),
}
impl<'a, 'p, 's> Inference<'a, 'p, 's> {
    fn known(&mut self, sort: Rc<Sort>) -> Result<Id, ParserError> {
        if let Some(id) = self.sort_types.get(&sort) {
            return Ok(*id);
        }
        let mut todo = vec![(sort.clone(), false)];
        while let Some((sort, closing)) = todo.pop() {
            if self.sort_types.contains_key(&sort) {
                continue;
            }
            if crate::checker::deadline::expired() {
                return Err(ParserError::DeadlineExceeded);
            }
            if !closing {
                todo.push((sort.clone(), true));
                match sort.as_ref() {
                    Sort::Array(a, b) => {
                        todo.push((a.clone(), false));
                        todo.push((b.clone(), false));
                    }
                    Sort::Function(args) => {
                        for arg in args {
                            todo.push((arg.clone(), false));
                        }
                    }
                    Sort::Par(_, inner) => todo.push((inner.clone(), false)),
                    _ => {}
                }
                continue;
            }
            let kind = match sort.as_ref() {
                Sort::Array(a, b) => Ty::Array(self.sort_types[a], self.sort_types[b]),
                Sort::Function(args) => {
                    let Some((result, params)) = args.split_last() else {
                        return Err(invalid());
                    };
                    Ty::Function(
                        params.iter().map(|s| self.sort_types[s]).collect(),
                        self.sort_types[result],
                    )
                }
                Sort::Par(_, inner) => {
                    let id = self.sort_types[inner];
                    self.sort_types.insert(sort, id);
                    continue;
                }
                _ => Ty::Atom,
            };
            let id = self.types.add(kind);
            self.sort_types.insert(sort, id);
        }
        Ok(self.sort_types[&sort])
    }
    fn lookup(&mut self, name: &str, mut frame: usize) -> Result<Option<Id>, ParserError> {
        loop {
            if let Some(id) = self.frames[frame].names.get(name) {
                return Ok(Some(*id));
            }
            if frame == 0 {
                break;
            }
            frame = self.frames[frame].parent;
        }
        if let Some(id) = self.named.get(name) {
            return Ok(Some(*id));
        }
        if let Some(sort) = self.parser.get_symbol(name).cloned() {
            return self.known(sort).map(Some);
        }
        if let Some(definition) = self.parser.state.function_defs.get(name) {
            let params: Vec<_> = definition
                .params
                .iter()
                .map(|(_, sort)| sort.clone())
                .collect();
            let result = self.parser.pool.sort(&definition.body);
            let result = self.known(result)?;
            if params.is_empty() {
                return Ok(Some(result));
            }
            let mut arguments = Vec::new();
            for sort in params {
                arguments.push(self.known(sort)?);
            }
            return Ok(Some(self.types.add(Ty::Function(arguments, result))));
        }
        Ok(None)
    }
    fn is_bound(&self, name: &str, mut frame: usize) -> bool {
        loop {
            if self.frames[frame].names.contains_key(name) {
                return true;
            }
            if frame == 0 {
                return self.parser.local_binding_depth(name).is_some();
            }
            frame = self.frames[frame].parent;
        }
    }
    fn symbol(&self, id: Id) -> Option<&str> {
        match &self.syntax[id].token {
            Token::Symbol(name) => Some(name),
            _ => None,
        }
    }
    fn sort_hint(&mut self, id: Id) -> Result<Id, ParserError> {
        // Parse the exact immutable slice with the EXISTING sort parser and
        // declaration environment. The input frame restores even on unwind;
        // no source symbol table is cloned or replaced.
        // A sort's indexed payload can call parse_term. Do not allow that
        // speculative read to adopt a :named declaration into the namespace.
        let mut pending = vec![id];
        while let Some(node) = pending.pop() {
            if crate::checker::deadline::expired() {
                return Err(ParserError::DeadlineExceeded);
            }
            if matches!(
                &self.syntax[node].token,
                Token::ReservedWord(Reserved::Bang)
            ) {
                return Err(invalid());
            }
            pending.extend(self.syntax[node].children.iter().copied());
        }
        let input = self.syntax[id].input;
        let sort = read_sort(self.parser, input).map_err(|error| match error {
            Error::Parser(error, _) => error,
            _ => invalid(),
        })?;
        self.known(sort)
    }
    fn frame(&mut self, parent: usize, bindings: Vec<(String, Id)>) -> Result<usize, ParserError> {
        let mut names = HashMap::new();
        for (name, value) in bindings {
            if names.insert(name, value).is_some() {
                return Err(invalid());
            }
        }
        let id = self.frames.len();
        self.frames.push(Frame { parent, names });
        Ok(id)
    }
    fn infer(&mut self, root: Id) -> Result<Id, ParserError> {
        let mut work = vec![Work::Visit(root, 0)];
        while let Some(job) = work.pop() {
            if crate::checker::deadline::expired() {
                return Err(ParserError::DeadlineExceeded);
            }
            match job {
                Work::Visit(id, env) => {
                    let children = self.syntax[id].children.clone();
                    if children.is_empty() {
                        let kind = if let Some(name) = self.symbol(id).map(str::to_owned) {
                            self.lookup(&name, env)?
                        } else {
                            None
                        };
                        self.values[id] = Some(kind.unwrap_or_else(|| self.types.add(Ty::Atom)));
                        continue;
                    }
                    let head = children[0];
                    let args = &children[1..];
                    match &self.syntax[head].token {
                        Token::ReservedWord(Reserved::Let) if args.len() == 2 => {
                            let mut bindings = Vec::new();
                            for pair in self.syntax[args[0]].children.clone() {
                                let pair = self.syntax[pair].children.clone();
                                if pair.len() != 2 {
                                    return Err(invalid());
                                }
                                let name = self.symbol(pair[0]).ok_or_else(invalid)?.to_owned();
                                bindings.push((name, pair[1]));
                            }
                            work.push(Work::Let(id, env, bindings.clone(), args[1]));
                            for (_, value) in bindings.into_iter().rev() {
                                work.push(Work::Visit(value, env));
                            }
                        }
                        Token::ReservedWord(
                            Reserved::Lambda
                            | Reserved::Forall
                            | Reserved::Exists
                            | Reserved::Choice,
                        ) if args.len() == 2 => {
                            let mut bindings = Vec::new();
                            let mut params = Vec::new();
                            for pair in self.syntax[args[0]].children.clone() {
                                let pair = self.syntax[pair].children.clone();
                                if pair.len() != 2 {
                                    return Err(invalid());
                                }
                                let name = self.symbol(pair[0]).ok_or_else(invalid)?.to_owned();
                                let sort = self.sort_hint(pair[1])?;
                                bindings.push((name, sort));
                                params.push(sort);
                            }
                            let env = self.frame(env, bindings)?;
                            let Token::ReservedWord(binder) = &self.syntax[head].token else {
                                return Err(invalid());
                            };
                            work.push(Work::Binder(
                                id,
                                self.syntax[head].position,
                                params,
                                args[1],
                                *binder,
                            ));
                            work.push(Work::Visit(args[1], env));
                        }
                        Token::ReservedWord(Reserved::Bang) if !args.is_empty() => {
                            let named = args[1..].windows(2).find_map(|pair| {
                                if matches!(&self.syntax[pair[0]].token, Token::Keyword(name) if name == "named") {
                                    self.symbol(pair[1]).map(str::to_owned)
                                } else { None }
                            });
                            work.push(Work::Named(id, args[0], named));
                            work.push(Work::Visit(args[0], env));
                        }
                        Token::ReservedWord(Reserved::Match) if args.len() == 2 => {
                            let mut results = Vec::new();
                            for arm in self.syntax[args[1]].children.clone() {
                                let pair = self.syntax[arm].children.clone();
                                if pair.len() != 2 {
                                    return Err(invalid());
                                }
                                let mut bindings = Vec::new();
                                if let Some(name) = self.symbol(pair[0]) {
                                    bindings.push((name.to_owned(), self.types.add(Ty::Unknown)));
                                }
                                for variable in self.syntax[pair[0]].children.iter().skip(1) {
                                    if let Some(name) = self.symbol(*variable) {
                                        bindings
                                            .push((name.to_owned(), self.types.add(Ty::Unknown)));
                                    }
                                }
                                let scope = self.frame(env, bindings)?;
                                results.push((pair[1], scope));
                            }
                            work.push(Work::Match(
                                id,
                                results.iter().map(|(node, _)| *node).collect(),
                            ));
                            for (node, scope) in results.into_iter().rev() {
                                work.push(Work::Visit(node, scope));
                            }
                        }
                        _ => {
                            work.push(Work::App(id, env));
                            for child in children.into_iter().rev() {
                                work.push(Work::Visit(child, env));
                            }
                        }
                    }
                }
                Work::Let(id, env, bindings, body) => {
                    let bindings = bindings
                        .into_iter()
                        .map(|(name, node)| Ok((name, self.values[node].ok_or_else(invalid)?)))
                        .collect::<Result<Vec<_>, ParserError>>()?;
                    let scope = self.frame(env, bindings)?;
                    work.push(Work::Alias(id, body));
                    work.push(Work::Visit(body, scope));
                }
                Work::Alias(id, body) => self.values[id] = self.values[body],
                Work::Named(id, body, name) => {
                    let value = self.values[body].ok_or_else(invalid)?;
                    if let Some(name) = name {
                        self.named.insert(name, value);
                    }
                    self.values[id] = Some(value);
                }
                Work::Binder(id, position, params, body, binder) => {
                    let value = match binder {
                        Reserved::Lambda => self.types.add(Ty::Lambda(
                            position,
                            params,
                            self.values[body].ok_or_else(invalid)?,
                        )),
                        Reserved::Choice => *params.first().ok_or_else(invalid)?,
                        _ => self.types.add(Ty::Atom),
                    };
                    self.values[id] = Some(value);
                }
                Work::Match(id, results) => {
                    let result = self.types.add(Ty::Unknown);
                    for body in results {
                        self.types
                            .unify(result, self.values[body].ok_or_else(invalid)?)?;
                    }
                    self.values[id] = Some(result);
                }
                Work::App(id, env) => self.application(id, env)?,
            }
        }
        self.values[root].ok_or_else(invalid)
    }
    fn application(&mut self, id: Id, env: usize) -> Result<(), ParserError> {
        let children = self.syntax[id].children.clone();
        let head = children[0];
        let args = &children[1..];
        let name = self.symbol(head).map(str::to_owned);
        let builtin = name.as_ref().filter(|name| !self.is_bound(name, env));
        let value = |this: &Self, node: Id| this.values[node].ok_or_else(invalid);
        let qualified = self.syntax[head].children.clone();
        if qualified.len() == 3
            && args.len() == 1
            && matches!(
                &self.syntax[qualified[0]].token,
                Token::ReservedWord(Reserved::As)
            )
            && self.symbol(qualified[1]) == Some("const")
            && !self.is_bound("const", env)
        {
            let result = self.sort_hint(qualified[2])?;
            let root = self.types.root(result);
            let Ty::Array(_, element) = self.types.kinds[root].clone() else {
                return Err(invalid());
            };
            self.types.unify(value(self, args[0])?, element)?;
            self.values[id] = Some(result);
            return Ok(());
        }
        let result = match builtin.map(String::as_str) {
            Some("=" | "distinct") => {
                if let Some(first) = args.first() {
                    let first = value(self, *first)?;
                    for arg in &args[1..] {
                        self.types.unify(first, value(self, *arg)?)?;
                    }
                }
                self.types.add(Ty::Atom)
            }
            Some("ite") if args.len() == 3 => {
                let a = value(self, args[1])?;
                self.types.unify(a, value(self, args[2])?)?;
                a
            }
            Some("select") if args.len() == 2 => {
                let result = self.types.add(Ty::Unknown);
                let array = self.types.add(Ty::Array(value(self, args[1])?, result));
                self.types.unify(value(self, args[0])?, array)?;
                result
            }
            Some("store") if args.len() == 3 => {
                let array = self
                    .types
                    .add(Ty::Array(value(self, args[1])?, value(self, args[2])?));
                self.types.unify(value(self, args[0])?, array)?;
                array
            }
            _ => {
                let function = value(self, head)?;
                let root = self.types.root(function);
                let (params, result) = match self.types.kinds[root].clone() {
                    Ty::Function(params, result) | Ty::Lambda(_, params, result) => {
                        (params, result)
                    }
                    _ => {
                        self.values[id] = Some(self.types.add(Ty::Atom));
                        return Ok(());
                    }
                };
                if args.len() > params.len() {
                    return Err(invalid());
                }
                let expected = self.types.add(Ty::Function(params.clone(), result));
                self.types.unify(function, expected)?;
                for (node, expected) in args.iter().zip(&params) {
                    self.types.unify(value(self, *node)?, *expected)?;
                }
                if args.len() == params.len() {
                    result
                } else {
                    self.types
                        .add(Ty::Function(params[args.len()..].to_vec(), result))
                }
            }
        };
        self.values[id] = Some(result);
        Ok(())
    }
}

pub(super) fn plan(
    parser: &mut Parser<'_, '_>,
    expected: Option<Rc<Sort>>,
) -> CarcaraResult<HashSet<Position>> {
    let mut lexer = parser.lexer.clone();
    let mut current = (parser.current_token.clone(), parser.current_position);
    let mut input = parser.lexer.token_input();
    let mut syntax = Vec::new();
    let mut stack: Vec<Id> = Vec::new();
    let root;
    loop {
        parser.poll_deadline()?;
        let (token, position) = current;
        let open = matches!(token, Token::OpenParen);
        let close = matches!(token, Token::CloseParen);
        if matches!(token, Token::Eof) {
            return Err(Error::Parser(invalid(), position));
        }
        if close {
            let Some(done) = stack.pop() else {
                return Err(Error::Parser(invalid(), position));
            };
            if stack.is_empty() {
                root = done;
                break;
            }
        } else {
            let id = syntax.len();
            syntax.push(Syntax {
                input,
                token,
                position,
                children: Vec::new(),
            });
            if let Some(parent) = stack.last() {
                syntax[*parent].children.push(id);
            }
            if open {
                if stack.len() >= MAX_WRITTEN_NESTING {
                    return Err(Error::Parser(
                        ParserError::WrittenTooDeep(MAX_WRITTEN_NESTING),
                        position,
                    ));
                }
                stack.push(id);
            } else if stack.is_empty() {
                root = id;
                break;
            }
        }
        current = lexer.next_token()?;
        input = lexer.token_input();
    }
    if !syntax
        .iter()
        .any(|node| matches!(&node.token, Token::ReservedWord(Reserved::Lambda)))
    {
        return Ok(HashSet::new());
    }
    let count = syntax.len();
    let position = parser.current_position;
    let mut inference = Inference {
        parser,
        syntax,
        types: Types::new(),
        values: vec![None; count],
        frames: vec![Frame { parent: 0, names: HashMap::new() }],
        named: HashMap::new(),
        sort_types: HashMap::new(),
    };
    let result = inference
        .infer(root)
        .map_err(|error| Error::Parser(error, inference.syntax[root].position))?;
    if let Some(expected) = expected {
        let expected = inference
            .known(expected)
            .map_err(|error| Error::Parser(error, inference.syntax[root].position))?;
        inference
            .types
            .unify(result, expected)
            .map_err(|error| Error::Parser(error, inference.syntax[root].position))?;
    }
    inference
        .types
        .finish()
        .map_err(|error| Error::Parser(error, position))
}

struct SortInput<'a, 'p, 's> {
    parser: &'a mut Parser<'p, 's>,
    nesting: usize,
    saved: Option<(
        lexer::Lexer<'s>,
        Token,
        Position,
        Option<String>,
        Option<String>,
    )>,
}
impl Drop for SortInput<'_, '_, '_> {
    fn drop(&mut self) {
        self.parser.state.nesting = self.nesting;
        if let Some((lexer, token, position, number, consumed)) = self.saved.take() {
            self.parser.lexer = lexer;
            self.parser.current_token = token;
            self.parser.current_position = position;
            self.parser.current_number_symbol = number;
            self.parser.consumed_number_symbol = consumed;
        }
    }
}
fn read_sort<'p, 's>(parser: &mut Parser<'p, 's>, input: &'s str) -> CarcaraResult<Rc<Sort>> {
    let mut lexer = lexer::Lexer::new(input);
    let (token, position) = lexer.next_token()?;
    let number = lexer.take_number_symbol_reading();
    let saved = (
        std::mem::replace(&mut parser.lexer, lexer),
        std::mem::replace(&mut parser.current_token, token),
        std::mem::replace(&mut parser.current_position, position),
        std::mem::replace(&mut parser.current_number_symbol, number),
        parser.consumed_number_symbol.take(),
    );
    let nesting = parser.state.nesting;
    let frame = SortInput { parser, nesting, saved: Some(saved) };
    frame.parser.parse_sort()
}

pub(super) struct TermFrame<'a, 'p, 's> {
    pub(super) parser: &'a mut Parser<'p, 's>,
    previous_depth: usize,
    clear_plan: bool,
}
impl<'a, 'p, 's> TermFrame<'a, 'p, 's> {
    pub(super) fn enter(parser: &'a mut Parser<'p, 's>, clear_plan: bool) -> CarcaraResult<Self> {
        let previous_depth = parser.lambda_term_depth;
        parser.lambda_term_depth = previous_depth
            .checked_add(1)
            .ok_or_else(|| Error::Parser(invalid(), parser.current_position))?;
        Ok(Self { parser, previous_depth, clear_plan })
    }
}
impl Drop for TermFrame<'_, '_, '_> {
    fn drop(&mut self) {
        self.parser.lambda_term_depth = self.previous_depth;
        if self.clear_plan {
            self.parser.lambda_array_positions.clear();
        }
    }
}
