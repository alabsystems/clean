// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The by-name census's reachability: which kernel items the replay's
//! entry points reach (`by_name_census_tests.rs`).

use super::scan::*;
use super::*;

// ─────────────────────────────────────────────────────────────────────────────
// Reachability.
// ─────────────────────────────────────────────────────────────────────────────

type ItemRef = (u8, String, usize);

/// The reached part of the kernel crate.
pub(super) struct Census {
    items: Items,
    reached: BTreeSet<ItemRef>,
}

const FN: u8 = 0;
const STATIC: u8 = 1;
const MACRO: u8 = 2;
const TYPE: u8 = 3;

fn is_type_like(s: &str) -> bool {
    s.chars().next().is_some_and(|c| c.is_ascii_uppercase()) && !is_screaming(s)
}

impl Census {
    pub(super) fn build() -> Self {
        let mut items = Items::default();
        for (file, text) in source_files(&kernel_src()) {
            let toks = lex(&text);
            let idx = items.files.len();
            collect_items(&file, idx, &toks, 0, None, None, &mut items);
            items.file_names.insert(file.clone());
            for w in toks.windows(2) {
                if ident(w.first()) == Some("dyn") {
                    if let Some(tr) = ident(w.get(1)) {
                        items.dyn_traits.insert(tr.to_string());
                    }
                }
            }
            items.files.push(toks);
        }
        let names = items.file_names.clone();
        let logical = path_attr_modules(&names, &items.files);
        let mut uses = BTreeMap::new();
        for (k, file) in names.iter().enumerate() {
            let here = logical
                .get(file)
                .cloned()
                .unwrap_or_else(|| module_of(file));
            uses.insert(file.clone(), parse_uses(here, &items.files[k], &names));
        }
        items.uses = uses;
        let mut census = Self {
            items,
            reached: BTreeSet::new(),
        };
        census.reach();
        census
    }

    fn body(&self, it: &Item) -> &[Tok] {
        &self.items.files[it.file_idx][it.range.0..it.range.1]
    }

    fn item(&self, r: &ItemRef) -> &Item {
        let map = match r.0 {
            FN => &self.items.fns,
            STATIC => &self.items.statics,
            MACRO => &self.items.macros,
            _ => &self.items.type_defs,
        };
        &map[&r.1][r.2]
    }

    fn reach(&mut self) {
        let mut types: BTreeSet<String> = ["Environment", "TypeChecker"]
            .iter()
            .map(|s| (*s).to_string())
            .collect();
        let mut methods: BTreeSet<String> = BTreeSet::new();
        let mut work: Vec<ItemRef> = Vec::new();
        let manifest = Path::new(env!("CARGO_MANIFEST_DIR"));
        for src in REPLAY_SOURCES {
            let text = std::fs::read_to_string(manifest.join(src)).expect("read replay source");
            let toks = lex(strip_inline_test_module(&text));
            self.scan_body(
                &format!("clean-olean/{src}"),
                None,
                &toks,
                &mut types,
                &mut methods,
                &mut work,
            );
        }
        for (owner, name) in ENTRY_POINTS {
            let found: Vec<ItemRef> = self
                .items
                .fns
                .get(*name)
                .into_iter()
                .flatten()
                .enumerate()
                .filter(|(_, it)| it.owner.as_deref() == Some(owner))
                .map(|(k, _)| (FN, (*name).to_string(), k))
                .collect();
            assert!(
                !found.is_empty(),
                "entry point {owner}::{name} not found in the kernel source"
            );
            assert!(
                found.iter().any(|r| work.contains(r)),
                "the replay sources no longer reach entry point {owner}::{name}"
            );
            work.extend(found);
        }
        loop {
            while let Some(r) = work.pop() {
                if !self.reached.insert(r.clone()) {
                    continue;
                }
                let item = self.item(&r);
                if let Some(o) = &item.owner {
                    types.insert(o.clone());
                }
                self.scan_body(
                    &item.file,
                    item.owner.as_deref(),
                    self.body(item),
                    &mut types,
                    &mut methods,
                    &mut work,
                );
            }
            // A reached type's definition is scanned (its fields' types join
            // `types`), and the traits implemented for it join `types` so
            // their default methods resolve.
            let traits: BTreeSet<String> = types
                .iter()
                .filter_map(|t| self.items.traits_of.get(t))
                .flatten()
                .cloned()
                .collect();
            types.extend(traits);
            for ((ty, tr), fns) in &self.items.impl_fns {
                if types.contains(ty) && self.items.dyn_traits.contains(tr) {
                    for (name, k) in fns {
                        let r = (FN, name.clone(), *k);
                        if !self.reached.contains(&r) {
                            work.push(r);
                        }
                    }
                }
            }
            // Implicitly-called trait methods of every reached type.
            for ((ty, tr), fns) in &self.items.impl_fns {
                if !types.contains(ty) {
                    continue;
                }
                for (name, k) in fns {
                    if IMPLICIT_METHODS.iter().any(|(t, m)| t == tr && m == name) {
                        let r = (FN, name.clone(), *k);
                        if !self.reached.contains(&r) {
                            work.push(r);
                        }
                    }
                }
            }
            // The vtable also holds the trait's DEFAULT methods.
            for (ty, trs) in &self.items.traits_of {
                if !types.contains(ty) {
                    continue;
                }
                for tr in trs.iter().filter(|t| self.items.dyn_traits.contains(*t)) {
                    for (name, list) in &self.items.fns {
                        for (k, it) in list.iter().enumerate() {
                            let r = (FN, name.clone(), k);
                            if it.owner.as_deref() == Some(tr.as_str())
                                && !self.reached.contains(&r)
                            {
                                work.push(r);
                            }
                        }
                    }
                }
            }
            for t in types.iter() {
                for k in 0..self.items.type_defs.get(t).map_or(0, Vec::len) {
                    let r = (TYPE, t.clone(), k);
                    if !self.reached.contains(&r) {
                        work.push(r);
                    }
                }
            }
            // Method calls resolve against every type reached so far; a newly
            // reached type can make an earlier call reach more.
            for (name, list) in &self.items.fns {
                if !methods.contains(name) {
                    continue;
                }
                for (k, it) in list.iter().enumerate() {
                    if it.owner.as_ref().is_some_and(|o| types.contains(o))
                        && !self.reached.contains(&(FN, name.clone(), k))
                    {
                        work.push((FN, name.clone(), k));
                    }
                }
            }
            if work.is_empty() {
                break;
            }
        }
    }

    fn scan_body(
        &self,
        file: &str,
        owner: Option<&str>,
        body: &[Tok],
        types: &mut BTreeSet<String>,
        methods: &mut BTreeSet<String>,
        work: &mut Vec<ItemRef>,
    ) {
        let fns = &self.items.fns;
        for (i, t) in body.iter().enumerate() {
            let Tok::Ident(name) = t else {
                continue;
            };
            if is_type_like(name) {
                types.insert(name.clone());
            }
            if is_screaming(name) {
                for k in 0..self.items.statics.get(name).map_or(0, Vec::len) {
                    work.push((STATIC, name.clone(), k));
                }
            }
            if is_punct(body.get(i + 1), '!') {
                for k in 0..self.items.macros.get(name).map_or(0, Vec::len) {
                    work.push((MACRO, name.clone(), k));
                }
            }
            let Some(list) = fns.get(name) else {
                continue;
            };
            // Skip a turbofish: `name::<…>(`.
            let mut next = i + 1;
            if is_punct(body.get(next), ':')
                && is_punct(body.get(next + 1), ':')
                && is_punct(body.get(next + 2), '<')
            {
                let mut depth = 0i32;
                let mut k = next + 2;
                while k < body.len() {
                    match body[k] {
                        Tok::Punct('<') => depth += 1,
                        Tok::Punct('>') => {
                            depth -= 1;
                            if depth == 0 {
                                break;
                            }
                        }
                        _ => {}
                    }
                    k += 1;
                }
                next = k + 1;
            }
            let called = is_punct(body.get(next), '(');
            let after_dot = i > 0 && is_punct(body.get(i - 1), '.');
            let after_path =
                i > 1 && is_punct(body.get(i - 1), ':') && is_punct(body.get(i - 2), ':');
            let push_where = |work: &mut Vec<ItemRef>, pred: &dyn Fn(&Item) -> bool| -> bool {
                let mut any = false;
                for (k, it) in list.iter().enumerate() {
                    if pred(it) {
                        work.push((FN, name.clone(), k));
                        any = true;
                    }
                }
                any
            };
            if after_dot {
                if called {
                    methods.insert(name.clone());
                    push_where(work, &|it| {
                        it.owner.as_ref().is_some_and(|o| types.contains(o))
                    });
                }
            } else if after_path {
                let seg = ident(body.get(i - 3)).unwrap_or("");
                let seg = if seg == "Self" {
                    owner.unwrap_or("")
                } else {
                    seg
                };
                let traits = &self.items.traits;
                if is_type_like(seg) {
                    types.insert(seg.to_string());
                    let hit = push_where(work, &|it| it.owner.as_deref() == Some(seg));
                    if !hit && self.items.owners.contains(seg) {
                        // A kernel type's method it does not define itself:
                        // a trait default. Take every trait's default of
                        // that name.
                        push_where(work, &|it| {
                            it.owner.as_ref().is_some_and(|o| traits.contains(o))
                        });
                    }
                    // A type the kernel has no `impl` for (`Vec::new`,
                    // `Arc::new`) calls no kernel code.
                } else if matches!(seg, "crate" | "super" | "self") {
                    push_where(work, &|it| it.owner.is_none());
                } else {
                    let hit = push_where(work, &|it| {
                        it.owner.is_none()
                            && (it.file.ends_with(&format!("{seg}.rs"))
                                || it.file.ends_with(&format!("{seg}/mod.rs")))
                    });
                    if !hit {
                        // Re-exported or `use`-aliased: every free function
                        // of that name.
                        push_where(work, &|it| it.owner.is_none());
                    }
                }
            } else {
                // A bare call, or a function item passed by name: defined in
                // this file, or imported by one of its `use` declarations.
                let same_file = push_where(work, &|it| it.owner.is_none() && it.file == file);
                if same_file {
                    continue;
                }
                let in_module = |it: &Item, m: &[String]| {
                    let p = m.join("/");
                    it.file == format!("{p}.rs") || it.file == format!("{p}/mod.rs")
                };
                let uses = self.items.uses.get(file).map_or(&[][..], Vec::as_slice);
                let mut resolved = false;
                for u in uses {
                    let bound = u.alias.as_ref().or(u.name.as_ref());
                    if bound != Some(name) {
                        continue;
                    }
                    resolved = true;
                    let Some(m) = &u.module else {
                        continue; // std or another crate
                    };
                    let orig = u.name.clone().unwrap_or_default();
                    let orig_list = fns.get(&orig).map_or(&[][..], Vec::as_slice);
                    let mut any = false;
                    for (k, it) in orig_list.iter().enumerate() {
                        if it.owner.is_none() && in_module(it, m) {
                            work.push((FN, orig.clone(), k));
                            any = true;
                        }
                    }
                    if !any {
                        // Re-exported or `#[path]`-mapped: every free fn of
                        // that name.
                        for (k, it) in orig_list.iter().enumerate() {
                            if it.owner.is_none() {
                                work.push((FN, orig.clone(), k));
                            }
                        }
                    }
                }
                // A glob import is followed for a function item passed BY
                // NAME as well as for a call: `register_uint_width!(self, …,
                // reduce_uint8_add, …)` stores the fn pointer, and the linker
                // keeps what it points at (census of 2026-09-29).
                if resolved {
                    continue;
                }
                for u in uses.iter().filter(|u| u.name.is_none()) {
                    if let Some(m) = &u.module {
                        self.resolve_in_module(m, name, 0, work);
                    }
                }
            }
        }
    }

    /// Push the free fn `name` as module `m` exposes it: defined there, or
    /// re-exported by one of its `use` declarations (followed, bounded). A
    /// module this scan cannot map to a file exposes every free fn of that
    /// name.
    fn resolve_in_module(&self, m: &[String], name: &str, depth: usize, work: &mut Vec<ItemRef>) {
        let p = m.join("/");
        let file = [format!("{p}.rs"), format!("{p}/mod.rs")]
            .into_iter()
            .find(|f| self.items.file_names.contains(f));
        let list = self.items.fns.get(name).map_or(&[][..], Vec::as_slice);
        let Some(file) = file else {
            for (k, it) in list.iter().enumerate() {
                if it.owner.is_none() {
                    work.push((FN, name.to_string(), k));
                }
            }
            return;
        };
        let mut any = false;
        for (k, it) in list.iter().enumerate() {
            if it.owner.is_none() && it.file == file {
                work.push((FN, name.to_string(), k));
                any = true;
            }
        }
        if any || depth > 8 {
            return;
        }
        for u in self.items.uses.get(&file).map_or(&[][..], Vec::as_slice) {
            let Some(um) = &u.module else {
                continue;
            };
            match (&u.name, &u.alias) {
                (Some(orig), alias) if alias.as_deref().unwrap_or(orig) == name => {
                    self.resolve_in_module(um, orig, depth + 1, work);
                }
                (None, _) => self.resolve_in_module(um, name, depth + 1, work),
                _ => {}
            }
        }
    }

    /// Every identifier-shaped string literal in a reached item:
    /// literal → files it appears in.
    pub(super) fn literals(&self) -> BTreeMap<String, BTreeSet<String>> {
        let mut out: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
        for r in &self.reached {
            let item = self.item(r);
            for t in self.body(item) {
                if let Tok::Str(s) = t {
                    if looks_like_a_name(s) {
                        out.entry(s.clone()).or_default().insert(item.file.clone());
                    }
                }
            }
        }
        out
    }

    /// `reached<TAB>kind<TAB>owner<TAB>name<TAB>file` for EVERY item the
    /// census found (`reached` is `1` or `0`), for the linker comparison.
    pub(super) fn dump(&self) -> String {
        let mut lines: Vec<String> = Vec::new();
        for (kind, map) in [
            (FN, &self.items.fns),
            (STATIC, &self.items.statics),
            (MACRO, &self.items.macros),
            (TYPE, &self.items.type_defs),
        ] {
            for (name, list) in map {
                for (k, it) in list.iter().enumerate() {
                    let reached = u8::from(self.reached.contains(&(kind, name.clone(), k)));
                    let kind = match kind {
                        FN => "fn",
                        STATIC => "static",
                        MACRO => "macro",
                        _ => "type",
                    };
                    lines.push(format!(
                        "{reached}\t{kind}\t{}\t{}\t{}",
                        it.owner.as_deref().unwrap_or("-"),
                        it.name,
                        it.file
                    ));
                }
            }
        }
        lines.sort();
        lines.dedup();
        lines.join("\n") + "\n"
    }

    pub(super) fn reached_count(&self) -> usize {
        self.reached.len()
    }

    /// Whether the census reached the function `owner::name`.
    pub(super) fn reaches_fn(&self, owner: &str, name: &str) -> bool {
        self.items
            .fns
            .get(name)
            .into_iter()
            .flatten()
            .enumerate()
            .any(|(k, it)| {
                it.owner.as_deref() == Some(owner)
                    && self.reached.contains(&(FN, name.to_string(), k))
            })
    }
}

/// A string that could be (part of) a constant name: identifier characters
/// and dots only, starting with a letter or `_`.
fn looks_like_a_name(s: &str) -> bool {
    let mut chars = s.chars();
    let Some(first) = chars.next() else {
        return false;
    };
    (first.is_alphabetic() || first == '_')
        && s.split('.').all(|seg| {
            !seg.is_empty()
                && seg.chars().all(|c| {
                    c.is_alphanumeric() || matches!(c, '_' | '\'' | '!' | '?') || c > '\u{7f}'
                })
        })
}
