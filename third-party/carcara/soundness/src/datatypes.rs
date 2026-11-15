// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Datatype declarations as the independent evaluator reads them.
//!
//! SMT-LIB interprets a non-parametric datatype as the free term algebra of its constructors: a
//! constructor builds a value, two values are equal exactly when they are built by the same
//! constructor from equal fields, a selector projects its own constructor's field, and a tester
//! `(_ is C)` holds exactly of `C` values. A selector applied to a value built by *another*
//! constructor is unspecified: every model picks some value, as for an uninterpreted function.
//!
//! The table is read from the parsed instance (Carcara's term pool), so it describes exactly what
//! the checker was given, but none of the evaluation shares code with the checker.
//!
//! Parametric datatypes are not modelled: their sorts stay [`S::Other`], so anything built from
//! them is `Unknown`.

use crate::sort::S;
use carcara::ast::{
    pool::{PrimitivePool, TermPool},
    Rc as TRc, Sort, Term,
};
use std::collections::{BTreeMap, BTreeSet, HashSet};

/// A constructor and its fields, in order: `(selector name, field sort)`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DtCtor {
    pub name: String,
    pub fields: Vec<(String, S)>,
}

/// What a free symbol of a given name and sort denotes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DtSymbol<'a> {
    Ctor {
        datatype: &'a str,
        ctor: &'a DtCtor,
    },
    Selector {
        datatype: &'a str,
        ctor: &'a DtCtor,
        index: usize,
    },
}

/// The symbol has more than one datatype meaning; the evaluator answers `Unknown` for it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Ambiguous;

#[derive(Debug, Clone, Default)]
pub struct DtTable {
    datatypes: BTreeMap<String, Vec<DtCtor>>,
    /// Symbols that are also declared by `declare-fun`/`declare-const` with the same sort. Such a
    /// script is ill-formed; the evaluator reads the symbol as uninterpreted, the reading under
    /// which a checker that trusted the datatype meaning can be caught.
    shadowed: BTreeSet<(String, S)>,
}

fn datatype_names(sort: &Sort, acc: &mut BTreeSet<String>) {
    match sort {
        Sort::Datatype { name, args } => {
            if args.is_empty() {
                acc.insert(name.to_string());
            }
            for a in args {
                datatype_names(a, acc);
            }
        }
        Sort::Function(sorts) | Sort::Tuple(sorts) => {
            for s in sorts {
                datatype_names(s, acc);
            }
        }
        Sort::Atom(_, args) => {
            for a in args.iter() {
                datatype_names(a, acc);
            }
        }
        Sort::Array(i, e) => {
            datatype_names(i, acc);
            datatype_names(e, acc);
        }
        Sort::Set(s) | Sort::Par(_, s) => datatype_names(s, acc),
        _ => {}
    }
}

fn collect(
    pool: &PrimitivePool,
    t: &TRc<Term>,
    names: &mut BTreeSet<String>,
    seen: &mut HashSet<usize>,
) {
    if !seen.insert(TRc::as_ptr(t) as usize) {
        return;
    }
    datatype_names(&pool.sort(t), names);
    match t.as_ref() {
        Term::Const(_) => {}
        Term::Var(_, sort) => datatype_names(sort, names),
        Term::App(f, args) => {
            collect(pool, f, names, seen);
            for a in args {
                collect(pool, a, names, seen);
            }
        }
        Term::Op(_, args) | Term::AsOp(_, _, args) => {
            for a in args {
                collect(pool, a, names, seen);
            }
        }
        Term::ParamOp { op_args, args, .. } => {
            for a in op_args.iter().chain(args) {
                collect(pool, a, names, seen);
            }
        }
        Term::Binder(_, bindings, body) => {
            for (_, s) in bindings.iter() {
                datatype_names(s, names);
            }
            collect(pool, body, names, seen);
        }
        Term::Let(bindings, body) => {
            for (_, v) in bindings.iter() {
                collect(pool, v, names, seen);
            }
            collect(pool, body, names, seen);
        }
        Term::Match(scrutinee, cases) => {
            collect(pool, scrutinee, names, seen);
            for c in cases {
                collect(pool, &c.body, names, seen);
            }
        }
    }
}

impl DtTable {
    /// The non-parametric datatypes reachable from the sorts of `terms` (and of their fields).
    pub fn from_terms<'t>(
        pool: &PrimitivePool,
        terms: impl IntoIterator<Item = &'t TRc<Term>>,
    ) -> DtTable {
        let mut names = BTreeSet::new();
        let mut seen = HashSet::new();
        for t in terms {
            collect(pool, t, &mut names, &mut seen);
        }
        let mut table = DtTable::default();
        let mut work: Vec<String> = names.into_iter().collect();
        while let Some(name) = work.pop() {
            if table.datatypes.contains_key(&name) {
                continue;
            }
            // Only names taken from a `Sort::Datatype` reach here, and the parser declares every
            // such datatype in the pool.
            let datatype = pool.get_datatype(&name);
            if !datatype.params.is_empty() {
                continue;
            }
            let mut ctors = Vec::new();
            for (ctor, decl) in &datatype.constructors {
                let mut fields = Vec::new();
                for (selector, sort) in &decl.selectors {
                    let mut more = BTreeSet::new();
                    datatype_names(sort, &mut more);
                    work.extend(more);
                    fields.push((selector.clone(), S::from_sort(sort)));
                }
                ctors.push(DtCtor { name: ctor.clone(), fields });
            }
            table.datatypes.insert(name, ctors);
        }
        table
    }

    pub fn is_empty(&self) -> bool {
        self.datatypes.is_empty()
    }

    /// Reads the symbol `name : sort` as uninterpreted from now on.
    pub fn shadow(&mut self, name: &str, sort: S) {
        self.shadowed.insert((name.to_owned(), sort));
    }

    pub fn ctors(&self, datatype: &str) -> Option<&[DtCtor]> {
        self.datatypes.get(datatype).map(Vec::as_slice)
    }

    /// What the free symbol `name : sort` denotes: `Ok(None)` when it is no datatype symbol (or is
    /// shadowed by an ordinary declaration), `Err(Ambiguous)` when it has more than one datatype
    /// meaning.
    pub fn symbol(&self, name: &str, sort: &S) -> Result<Option<DtSymbol<'_>>, Ambiguous> {
        if self.datatypes.is_empty() {
            return Ok(None);
        }
        if self.shadowed.contains(&(name.to_owned(), sort.clone())) {
            return Ok(None);
        }
        let mut found = Vec::new();
        match sort {
            S::Dt(d) => {
                if let Some((datatype, ctors)) = self.datatypes.get_key_value(d) {
                    for c in ctors {
                        if c.name == name && c.fields.is_empty() {
                            found.push(DtSymbol::Ctor { datatype, ctor: c });
                        }
                    }
                }
            }
            S::Fun(args, ret) => {
                if let S::Dt(d) = ret.as_ref() {
                    if let Some((datatype, ctors)) = self.datatypes.get_key_value(d) {
                        for c in ctors {
                            let field_sorts = c.fields.iter().map(|(_, s)| s);
                            if c.name == name
                                && c.fields.len() == args.len()
                                && field_sorts.eq(args.iter())
                            {
                                found.push(DtSymbol::Ctor { datatype, ctor: c });
                            }
                        }
                    }
                }
                if let [S::Dt(d)] = args.as_slice() {
                    if let Some((datatype, ctors)) = self.datatypes.get_key_value(d) {
                        for c in ctors {
                            for (index, (selector, field)) in c.fields.iter().enumerate() {
                                if selector == name && field == ret.as_ref() {
                                    found.push(DtSymbol::Selector { datatype, ctor: c, index });
                                }
                            }
                        }
                    }
                }
            }
            _ => {}
        }
        match found.as_slice() {
            [] => Ok(None),
            [one] => Ok(Some(*one)),
            _ => Err(Ambiguous),
        }
    }
}
