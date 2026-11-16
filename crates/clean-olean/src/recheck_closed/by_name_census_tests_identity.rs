// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Conservative identity checks for the few APIs whose literal arguments are
//! metadata. This is source-discovery machinery, not a Rust name resolver or
//! a trusted validator. Unsupported or ambiguous bindings retain candidates.

use super::roles::{self, Role};
use super::scan::*;
use std::collections::{BTreeMap, BTreeSet};

enum Binding {
    Definition(String),
    Import(Option<Vec<String>>, String),
    Parameter(usize),
    Unknown,
}

struct Scope {
    parent: Option<usize>,
    module: Vec<String>,
    is_module: bool,
    bindings: BTreeMap<String, Vec<(usize, Binding)>>,
    globs: Vec<Option<Vec<String>>>,
    impl_trait: Option<usize>,
    opaque: bool,
}

impl Scope {
    fn bind(&mut self, name: &str, from: usize, binding: Binding) {
        self.bindings
            .entry(name.to_owned())
            .or_default()
            .push((from, binding));
    }
}

pub(super) struct Identity {
    scopes: Vec<Scope>,
    at_scope: Vec<Vec<usize>>,
    modules: BTreeMap<Vec<String>, Vec<usize>>,
}

impl Identity {
    pub(super) fn new(items: &Items) -> Self {
        let logical = path_attr_modules(&items.file_names, &items.files);
        let mut this = Self {
            scopes: Vec::new(),
            at_scope: Vec::new(),
            modules: BTreeMap::new(),
        };
        for (file, toks) in items.file_names.iter().zip(&items.files) {
            let module = logical
                .get(file)
                .cloned()
                .unwrap_or_else(|| module_of(file));
            let root = this.push_scope(None, module, true, None);
            let mut scope = root;
            let mut at_scope = Vec::new();
            let mut headers = BTreeMap::new();
            for (at, t) in toks.iter().enumerate() {
                at_scope.push(scope);
                // This index does not expand macros or normalize raw
                // identifiers. Either can supply an otherwise invisible local
                // binding; do not infer identity through that scope.
                if ident(Some(t)).is_some_and(|s| {
                    (is_punct(toks.get(at + 1), '!')
                        && (s == "macro_rules"
                            || matches!(toks.get(at + 2), Some(Tok::Punct('(' | '{' | '[')))))
                        || (s == "r" && is_punct(toks.get(at + 1), '#'))
                }) {
                    this.scopes[scope].opaque = true;
                }
                if is_punct(Some(t), '{') {
                    let inline_module = at
                        .checked_sub(2)
                        .filter(|&i| ident(toks.get(i)) == Some("mod"));
                    let mut module = this.scopes[scope].module.clone();
                    if let Some(i) = inline_module {
                        module.push(ident(toks.get(i + 1)).unwrap_or_default().to_owned());
                    }
                    let parent = scope;
                    scope = this.push_scope(
                        Some(parent),
                        module,
                        inline_module.is_some(),
                        headers.get(&at).copied(),
                    );
                    // Parameters and generic binders belong to the body, not
                    // the module that also contains its sibling functions.
                    if let Some(&start) = headers.get(&at) {
                        this.bind_parameters(scope, start, &toks[start..at]);
                    }
                } else if is_punct(Some(t), '}') {
                    scope = this.scopes[scope].parent.unwrap_or(root);
                } else if ident(Some(t)) == Some("use") {
                    let mut raw = Vec::new();
                    use_tree(toks, at + 1, &mut Vec::new(), &mut raw);
                    // The small use-tree parser can stop AT an unsupported
                    // raw identifier's '#'. Inspect the complete declaration,
                    // including grouped imports, before permitting fallback.
                    let end = (at..toks.len())
                        .find(|&i| is_punct(toks.get(i), ';'))
                        .unwrap_or(toks.len());
                    if toks[at..end]
                        .windows(2)
                        .any(|w| ident(w.first()) == Some("r") && is_punct(w.get(1), '#'))
                    {
                        this.scopes[scope].opaque = true;
                    }
                    for (path, name, alias) in raw {
                        let module = this.import_module(scope, &path);
                        if let Some(name) = name {
                            let bound = alias.as_deref().unwrap_or(&name);
                            this.scopes[scope].bind(
                                bound,
                                0,
                                Binding::Import(module, name.clone()),
                            );
                        } else {
                            this.scopes[scope].globs.push(module);
                        }
                    }
                } else if ident(Some(t)) == Some("let") {
                    // Pattern names before the optional type annotation. A
                    // binding is visible only after this declaration; treating
                    // its initializer conservatively as shadowed is harmless.
                    for tok in toks[at + 1..]
                        .iter()
                        .take_while(|t| !matches!(t, Tok::Punct('=' | ';' | ':')))
                    {
                        if let Some(name) = ident(Some(tok)) {
                            this.scopes[scope].bind(name, at, Binding::Unknown);
                        }
                    }
                } else if let Some(kind) = ident(Some(t)) {
                    if matches!(kind, "fn" | "impl") {
                        if let Some(open) =
                            (at + 1..toks.len()).find(|&i| matches!(toks[i], Tok::Punct('{' | ';')))
                        {
                            if is_punct(toks.get(open), '{') {
                                headers.insert(open, at);
                            }
                        }
                    }
                    if matches!(
                        kind,
                        "fn" | "struct"
                            | "enum"
                            | "union"
                            | "type"
                            | "trait"
                            | "mod"
                            | "const"
                            | "static"
                    ) {
                        if let Some(name) = ident(toks.get(at + 1)) {
                            // A definition's identity includes its module and
                            // declaration kind. A same-spelled alias is unknown.
                            let binding = if this.scopes[scope].is_module && kind != "type" {
                                Binding::Definition(format!(
                                    "{}::{kind}:{name}",
                                    this.scopes[scope].module.join("::")
                                ))
                            } else {
                                Binding::Unknown
                            };
                            this.scopes[scope].bind(name, 0, binding);
                        }
                    }
                }
            }
            this.at_scope.push(at_scope);
        }
        this
    }

    fn push_scope(
        &mut self,
        parent: Option<usize>,
        module: Vec<String>,
        is_module: bool,
        impl_trait: Option<usize>,
    ) -> usize {
        let id = self.scopes.len();
        if is_module {
            self.modules.entry(module.clone()).or_default().push(id);
        }
        self.scopes.push(Scope {
            parent,
            module,
            is_module,
            bindings: BTreeMap::new(),
            globs: Vec::new(),
            impl_trait,
            opaque: false,
        });
        id
    }

    fn bind_parameters(&mut self, scope: usize, start: usize, header: &[Tok]) {
        // A parameter/pattern followed by a type, or a generic parameter at
        // the start of a list. Extra uncertainty only retains candidates.
        for (i, t) in header.iter().enumerate() {
            let Some(name) = ident(Some(t)) else { continue };
            let colon = is_punct(header.get(i + 1), ':') && !is_punct(header.get(i + 2), ':');
            let generic = i
                .checked_sub(1)
                .is_some_and(|p| is_punct(header.get(p), '<'));
            if colon || generic {
                self.scopes[scope].bind(name, 0, Binding::Parameter(start));
            }
        }
    }

    fn import_module(&self, scope: usize, path: &[String]) -> Option<Vec<String>> {
        let mut module = self.scopes[scope].module.clone();
        let mut path = path.iter();
        match path.next().map(String::as_str) {
            Some("crate") => module.clear(),
            Some("self") => {}
            Some("super") => {
                module.pop()?;
            }
            Some(first) => module.push(first.to_owned()),
            None => return None,
        }
        for seg in path {
            if seg == "super" {
                module.pop()?;
            } else {
                module.push(seg.clone());
            }
        }
        Some(module)
    }

    // None = absent; Err = unknown/ambiguous. Explicit bindings take
    // precedence over globs. Inline modules do not inherit parent's imports.
    fn resolve(
        &self,
        scope: usize,
        at: usize,
        name: &str,
        seen: &mut BTreeSet<(usize, String)>,
    ) -> Result<Option<String>, ()> {
        if !seen.insert((scope, name.to_owned())) {
            return Err(());
        }
        let result = self.resolve_inner(scope, at, name, seen);
        seen.remove(&(scope, name.to_owned()));
        result
    }

    fn resolve_inner(
        &self,
        scope: usize,
        at: usize,
        name: &str,
        seen: &mut BTreeSet<(usize, String)>,
    ) -> Result<Option<String>, ()> {
        let s = &self.scopes[scope];
        if !s.is_module && s.opaque {
            return Err(());
        }
        let mut found = BTreeSet::new();
        for (_, binding) in s
            .bindings
            .get(name)
            .into_iter()
            .flatten()
            .filter(|(from, _)| *from <= at)
        {
            let origin = match binding {
                Binding::Definition(origin) => origin.clone(),
                Binding::Import(module, target) => {
                    self.in_module(module.as_deref(), target, seen)?.ok_or(())?
                }
                Binding::Unknown | Binding::Parameter(_) => return Err(()),
            };
            found.insert(origin);
        }
        if found.is_empty() {
            // At module scope explicit definitions/imports cannot be replaced
            // by another item in the same namespace in valid Rust. Globs can
            // be shadowed by an opaque expansion/import, so refuse fallback.
            if s.opaque {
                return Err(());
            }
            for module in &s.globs {
                if let Some(origin) = self.in_module(module.as_deref(), name, seen)? {
                    found.insert(origin);
                }
            }
        }
        if found.len() > 1 {
            return Err(());
        }
        if let Some(origin) = found.into_iter().next() {
            return Ok(Some(origin));
        }
        if !s.is_module {
            if let Some(parent) = s.parent {
                return self.resolve(parent, at, name, seen);
            }
        }
        Ok(None)
    }

    fn in_module(
        &self,
        module: Option<&[String]>,
        name: &str,
        seen: &mut BTreeSet<(usize, String)>,
    ) -> Result<Option<String>, ()> {
        let scopes = self.modules.get(module.ok_or(())?).ok_or(())?;
        if scopes.len() != 1 {
            return Err(());
        }
        self.resolve(scopes[0], usize::MAX, name, seen)
    }

    fn known(&self, item: &Item, at: usize, name: &str, origin: &str) -> bool {
        self.resolve(
            self.at_scope[item.file_idx][at],
            at,
            name,
            &mut BTreeSet::new(),
        ) == Ok(Some(origin.to_owned()))
    }

    fn unqualified(toks: &[Tok], start: usize) -> bool {
        !start.checked_sub(1).is_some_and(|i| {
            is_punct(toks.get(i), '.')
                || (is_punct(toks.get(i), ':') && i > 0 && is_punct(toks.get(i - 1), ':'))
        })
    }

    fn codec(&self, item: &Item, toks: &[Tok]) -> bool {
        let mut scope = self.at_scope[item.file_idx][item.range.0];
        loop {
            if let Some(start) = self.scopes[scope].impl_trait {
                if ident(toks.get(start)) == Some("impl") {
                    return toks.get(start..start + 3)
                        == Some(lex("impl PersistentExtEntry for").as_slice())
                        && self.known(
                            item,
                            start,
                            "PersistentExtEntry",
                            "env::persistent_ext::trait:PersistentExtEntry",
                        );
                }
            }
            let Some(parent) = self.scopes[scope].parent else {
                return false;
            };
            scope = parent;
        }
    }

    fn parameter_is_unshadowed(&self, item: &Item, at: usize, name: &str) -> bool {
        let mut scope = self.at_scope[item.file_idx][at];
        loop {
            if let Some(bindings) = self.scopes[scope].bindings.get(name) {
                let visible: Vec<_> = bindings.iter().filter(|(from, _)| *from <= at).collect();
                if !visible.is_empty() {
                    return visible.len() == 1
                        && matches!(visible[0].1, Binding::Parameter(start) if start == item.range.0);
                }
            }
            let Some(parent) = self.scopes[scope].parent else {
                return false;
            };
            scope = parent;
        }
    }

    fn decoder_parameter(&self, item: &Item, toks: &[Tok], at: usize) -> bool {
        let Some(body) = (item.range.0..at).find(|&i| is_punct(toks.get(i), '{')) else {
            return false;
        };
        // Only field reads of the original parameter. Patterns, closure
        // parameters, aliases and other uses need more analysis than this
        // role supplies and must retain the guard literal as a candidate.
        self.parameter_is_unshadowed(item, at, "entry")
            && (body..at)
                .all(|i| ident(toks.get(i)) != Some("entry") || is_punct(toks.get(i + 1), '.'))
    }

    pub(super) fn allows(&self, item: &Item, toks: &[Tok], at: usize, role: Role) -> bool {
        if !matches!(
            role,
            Role::LetBinder
                | Role::ExtensionRegistry
                | Role::ExtensionEncoding
                | Role::ExtensionDecoding
        ) {
            return true;
        }
        if !Self::unqualified(toks, at - 5) || !self.known(item, at, "Name", "name::struct:Name") {
            return false;
        }
        match role {
            Role::LetBinder => {
                Self::unqualified(toks, at - 10)
                    && self.known(item, at, "Expr", "expr::struct:Expr")
            }
            Role::ExtensionRegistry => roles::caller_start(toks, at - 6).is_some_and(|start| {
                Self::unqualified(toks, start)
                    // A mention as a value/pattern/parameter can introduce a
                    // callable binding that this small resolver cannot type.
                    && toks[item.range.0..item.range.1].iter().enumerate().all(|(i, t)| {
                        ident(Some(t)) != Some("register_persistent_ext")
                            || is_punct(toks.get(item.range.0 + i + 1), '(')
                            || toks.get(item.range.0 + i + 1..item.range.0 + i + 4) == Some(lex("::<").as_slice())
                    })
                    && self.known(
                        item,
                        at,
                        "register_persistent_ext",
                        "env::persistent_ext::fn:register_persistent_ext",
                    )
            }),
            Role::ExtensionEncoding | Role::ExtensionDecoding => {
                self.codec(item, toks) && self.known(item, at, "EnvExtensionEntry", "env::types::struct:EnvExtensionEntry")
                    // A decoder's parameter must still be the entry compared
                    // by its guard; a local binding can replace it.
                    && (role != Role::ExtensionDecoding || self.decoder_parameter(item, toks, at))
            }
            _ => true,
        }
    }
}
