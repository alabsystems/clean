//! Lean's `Expr.mdata` payload, decoded from a compacted region.
//!
//! `Expr.mdata (data : MData) (expr : Expr)` with `MData := KVMap` and
//! `structure KVMap where entries : List (Name × DataValue)`
//! (`Lean/Expr.lean`, `Lean/Data/KVMap.lean`, pinned v4.30.0-rc2). `KVMap` is a
//! single-field structure, which Lean's runtime represents as the field
//! itself, so the `data` field points straight at the `List`.
//!
//! Until 2026-09-30 both expression readers kept the `mdata` node and DROPPED
//! the map (`MData({}, e)`), so Clean's view of every stored Lean type carrying
//! `@& Nat` (`mdata {borrowed := true}`) or `no_index` (`mdata {noindex :=
//! true}`) disagreed with Lean's, and the prelude collision census could not
//! tell a faithful prelude statement from an unfaithful one. Measured over
//! `import Lean`: 17,429 mdata nodes; keys `noImplicitLambda`,
//! `sunfoldMatchAlt`, `save_info`, `borrowed`, `sunfoldMatch`, `_inaccessible`,
//! `noindex`, `_lhsGoal` (Bool), `uniq`, `name` (Name) and `_recApp`,
//! `_patWithRef` (Syntax, in stored TYPES as well as values).
//!
//! Every `DataValue` constructor is carried, losslessly:
//!
//! ```text
//! ofString s  (tag 0, 1 field)  -> (k, String s)                      exact
//! ofBool b    (tag 1, 1 byte)   -> (k, Bool b)                        exact
//! ofName n    (tag 2, 1 field)  -> (k, Name n)                        exact
//! ofNat n     (tag 3, 1 field)  -> (k, Nat n)  when n fits u64        exact
//!                                  (_clean_lean_mdata.nat.k, String "0x…") otherwise
//! ofInt i     (tag 4, 1 field)  -> (_clean_lean_mdata.int.k, String "<decimal>")
//!                                  (a heap, i.e. big, Int is REFUSED)
//! ofSyntax s  (tag 5, 1 field)  -> (_clean_lean_mdata.syntax.k, String <encoding>)
//! ```
//!
//! # Why three kinds ride under a reserved key, not new `MDataValue` variants
//!
//! `clean_kernel::expr::MDataValue` has exactly the four variants Clean writes
//! (`Bool`, `Nat(u64)`, `String`, `Name`), and trust-ir builds against this
//! workspace's `clean-kernel` (root `Cargo.toml` `[patch]`): its proof-DAG
//! codec (`trust-ir` `proof/clean_expr_dag/read.rs`, `shape.rs`) matches those
//! four exhaustively and serializes them as wire tags 0–3. A fifth variant
//! fails trust-ir's build and has no wire tag; adding one is a trust-ir wire
//! version, shipped in that repo's order, not an import fix. So the kinds the
//! enum cannot hold are carried as a `String` under the key
//! `_clean_lean_mdata.<kind>.<Lean key>`. That is injective: no Lean key starts
//! with `_clean_lean_mdata` (a map whose key does is REFUSED), each kind has
//! its own namespace, and every value text is canonical. Every kind Lean's
//! stored TYPES carry for the collision ratchet's rows (`borrowed`, `noindex`:
//! Bool) is represented exactly, so those types compare equal to a faithful
//! statement.
//!
//! The reader is strict, like the typed name/list readers beside it: an
//! unexpected tag, field count, or reference count refuses the expression
//! rather than guessing. `MData` is transparent to the kernel, so carrying the
//! payload changes no verdict; it changes what an imported term IS, which is
//! what the census and `Expr` equality see.
//!
//! The `Syntax` encoding is prefix-free and injective: every string and name
//! is a Rust-escaped quoted literal (names via
//! [`Name::to_unambiguous_string`]), every constructor has its own head, and
//! every position is a decimal `Nat`. Two payloads are therefore equal exactly
//! when Lean's trees are, source positions included.

use super::{is_ptr, is_scalar, tags, unbox_scalar, CompactedRegion, OleanError, OleanResult};
use clean_kernel::expr::{MDataMap, MDataValue};
use clean_kernel::name::{Name, NameInner};
use std::sync::Arc;

/// Bound on `KVMap` entries (the largest measured map has 2).
const KV_ENTRIES: usize = 4_096;
/// Bound on objects visited while encoding one `Syntax` payload (the largest
/// measured `_recApp` renders to ~39 KB of `repr`, a few thousand objects).
const SYNTAX_OBJECTS: usize = 1 << 20;
/// Bound on list length inside a `Syntax` (preresolved names, `decl` fields).
const SYNTAX_LIST_ITEMS: usize = 100_000;

/// The reserved key namespace for `DataValue` kinds `MDataValue` cannot hold.
pub(crate) const RESERVED_KEY_ROOT: &str = "_clean_lean_mdata";

/// `_clean_lean_mdata.<kind>.<every component of key>`.
fn reserved_key(kind: &str, key: &Name) -> Name {
    enum Component<'a> {
        Str(&'a str),
        Num(u64),
    }
    let mut components = Vec::new();
    let mut current = key;
    loop {
        match current.inner() {
            NameInner::Anon => break,
            NameInner::Str(parent, s) => {
                components.push(Component::Str(s));
                current = parent;
            }
            NameInner::Num(parent, n) => {
                components.push(Component::Num(*n));
                current = parent;
            }
        }
    }
    components
        .into_iter()
        .rev()
        .fold(
            Name::anon().str(RESERVED_KEY_ROOT).str(kind),
            |name, c| match c {
                Component::Str(s) => name.str(s),
                Component::Num(n) => name.num(n),
            },
        )
}

/// The first component of `key`, if it is a string.
fn root_component(key: &Name) -> Option<&str> {
    let mut current = key;
    let mut root = None;
    loop {
        match current.inner() {
            NameInner::Anon => return root,
            NameInner::Str(parent, s) => {
                root = Some(s.as_ref());
                current = parent;
            }
            NameInner::Num(parent, _) => {
                root = None;
                current = parent;
            }
        }
    }
}

/// A Lean key already in the reserved namespace would be indistinguishable
/// from a carried payload, so the map is refused.
fn refuse_reserved_lean_key(key: &Name) -> OleanResult<()> {
    if root_component(key) == Some(RESERVED_KEY_ROOT) {
        return Err(invalid(format!(
            "Lean key {} is in the reserved namespace {RESERVED_KEY_ROOT}",
            key.to_unambiguous_string()
        )));
    }
    Ok(())
}

/// How one `DataValue` is carried: under Lean's own key, or under the
/// reserved key for its kind.
#[derive(Debug, PartialEq)]
enum Carried {
    Exact(MDataValue),
    Reserved(&'static str, String),
}

/// `lean_box(n)` — a nullary constructor `n` stored as a tagged scalar.
const fn boxed(n: u64) -> u64 {
    (n << 1) | 1
}

fn invalid(message: impl Into<String>) -> OleanError {
    OleanError::Region(format!("mdata: {}", message.into()))
}

/// Push `items` so they pop in order, separated by single spaces.
fn push_seq(stack: &mut Vec<Step>, items: Vec<Step>) {
    let n = items.len();
    for (i, item) in items.into_iter().rev().enumerate() {
        stack.push(item);
        if i + 1 < n {
            stack.push(Step::Lit(" "));
        }
    }
}

/// One step of the iterative `Syntax` encoder.
enum Step {
    Syntax(u64),
    Info(u64),
    Substring(u64),
    Preresolved(u64),
    Lit(&'static str),
    Owned(String),
}

impl CompactedRegion<'_> {
    /// Decode the `MData` field of an `Expr.mdata` object.
    pub(crate) fn read_mdata_map(&self, pointer: u64) -> OleanResult<MDataMap> {
        let cells = self.mdata_list(pointer, KV_ENTRIES, "KVMap entries")?;
        let mut map = MDataMap::with_capacity(cells.len());
        for cell in cells {
            let (key, value) = self.mdata_pair(cell)?;
            let key = self.read_kernel_name_ptr(key)?;
            refuse_reserved_lean_key(&key)?;
            map.push(match self.read_data_value(value)? {
                Carried::Exact(value) => (key, value),
                Carried::Reserved(kind, text) => (
                    reserved_key(kind, &key),
                    MDataValue::String(Arc::from(text)),
                ),
            });
        }
        Ok(map)
    }

    /// `(tag, field count)` of a constructor object, refusing a non-pointer,
    /// a non-constructor, or a live reference count.
    fn mdata_ctor(&self, pointer: u64, what: &str) -> OleanResult<(usize, u8, u8)> {
        if !is_ptr(pointer) {
            return Err(invalid(format!(
                "{what}: expected an object, found {pointer:#x}"
            )));
        }
        let offset = self.ptr_to_offset(pointer)?;
        let header = self.read_header_at(offset)?;
        if header.rc != 0 || !header.is_constructor() {
            return Err(invalid(format!(
                "{what}: unexpected object (tag {}, rc {})",
                header.tag, header.rc
            )));
        }
        Ok((offset, header.tag, header.other))
    }

    /// The element pointers of a `List`: `nil` is `box(0)`, `cons` is tag 1
    /// with two fields.
    fn mdata_list(&self, pointer: u64, max: usize, what: &str) -> OleanResult<Vec<u64>> {
        let mut items = Vec::new();
        let mut current = pointer;
        while current != boxed(0) {
            if items.len() >= max {
                return Err(invalid(format!("{what}: more than {max} items")));
            }
            match self.mdata_ctor(current, what)? {
                (offset, 1, 2) => {
                    items.push(self.read_u64_at(offset + 8)?);
                    current = self.read_u64_at(offset + 16)?;
                }
                (_, tag, fields) => {
                    return Err(invalid(format!(
                        "{what}: not a List.cons (tag {tag}, {fields} fields)"
                    )))
                }
            }
        }
        Ok(items)
    }

    /// `Prod.mk a b`: tag 0, two fields.
    fn mdata_pair(&self, pointer: u64) -> OleanResult<(u64, u64)> {
        match self.mdata_ctor(pointer, "KVMap entry")? {
            (offset, 0, 2) => Ok((
                self.read_u64_at(offset + 8)?,
                self.read_u64_at(offset + 16)?,
            )),
            (_, tag, fields) => Err(invalid(format!(
                "KVMap entry: not a Prod.mk (tag {tag}, {fields} fields)"
            ))),
        }
    }

    fn read_data_value(&self, pointer: u64) -> OleanResult<Carried> {
        let (offset, tag, fields) = self.mdata_ctor(pointer, "DataValue")?;
        let field = |i: usize| self.read_u64_at(offset + 8 + 8 * i);
        match (tag, fields) {
            (0, 1) => Ok(Carried::Exact(MDataValue::String(Arc::from(
                self.mdata_string(field(0)?)?,
            )))),
            (1, 0) => match self.bytes_at(offset + 8, 1)?[0] {
                0 => Ok(Carried::Exact(MDataValue::Bool(false))),
                1 => Ok(Carried::Exact(MDataValue::Bool(true))),
                byte => Err(invalid(format!("DataValue.ofBool: non-Bool byte {byte}"))),
            },
            (2, 1) => Ok(Carried::Exact(MDataValue::Name(
                self.read_kernel_name_ptr(field(0)?)?,
            ))),
            (3, 1) => {
                let value = self.read_bignat_value(field(0)?)?;
                // `BigNat`'s Display is canonical: `0x` + zero-padded limbs
                // for a value at or above 2^64, the only case reaching it.
                Ok(match value.to_u64() {
                    Some(small) => Carried::Exact(MDataValue::Nat(small)),
                    None => Carried::Reserved("nat", value.to_string()),
                })
            }
            (4, 1) => {
                let int = field(0)?;
                if !is_scalar(int) {
                    return Err(invalid(
                        "DataValue.ofInt: a heap (big) Int is not decoded; refusing rather \
                         than dropping it",
                    ));
                }
                // `lean_box((size_t)(int)v)`: the low 32 bits carry the value.
                #[allow(clippy::cast_possible_truncation)]
                let small = unbox_scalar(int) as u32 as i32;
                Ok(Carried::Reserved("int", small.to_string()))
            }
            (5, 1) => Ok(Carried::Reserved("syntax", self.encode_syntax(field(0)?)?)),
            _ => Err(invalid(format!(
                "unknown DataValue constructor (tag {tag}, {fields} fields)"
            ))),
        }
    }

    fn mdata_string(&self, pointer: u64) -> OleanResult<&str> {
        if !is_ptr(pointer) {
            return Err(invalid(format!(
                "expected a String object, found {pointer:#x}"
            )));
        }
        self.read_lean_string_at(self.ptr_to_offset(pointer)?)
    }

    /// `String.Pos.Raw` is a single-field structure: a bare `Nat`.
    fn mdata_pos(&self, pointer: u64, out: &mut String) -> OleanResult<()> {
        let value = self.read_bignat_value(pointer)?;
        match value.to_u64() {
            Some(n) => out.push_str(&n.to_string()),
            None => return Err(invalid("Syntax position does not fit u64")),
        }
        Ok(())
    }

    fn mdata_name(&self, pointer: u64, out: &mut String) -> OleanResult<()> {
        let name = self.read_kernel_name_ptr(pointer)?;
        out.push_str(&format!("{:?}", name.to_unambiguous_string()));
        Ok(())
    }

    fn mdata_quoted(&self, pointer: u64, out: &mut String) -> OleanResult<()> {
        out.push_str(&format!("{:?}", self.mdata_string(pointer)?));
        Ok(())
    }

    /// The canonical encoding of a Lean `Syntax` tree (module doc).
    ///
    /// ```text
    /// Syntax       missing                 M
    ///              node info kind args     (N <info> <name> [<syntax>…])
    ///              atom info val           (A <info> <string>)
    ///              ident info raw val pre  (I <info> <substring> <name> [<pre>…])
    /// SourceInfo   original l p t e        (o <substring> <pos> <substring> <pos>)
    ///              synthetic p e canonical (s <pos> <pos> <0|1>)
    ///              none                    _
    /// Substring    str start stop          (<string> <pos> <pos>)
    /// Preresolved  namespace ns            (ns <name>)
    ///              decl n fields           (decl <name> [<string>…])
    /// ```
    fn encode_syntax(&self, pointer: u64) -> OleanResult<String> {
        let mut out = String::new();
        let mut stack = vec![Step::Syntax(pointer)];
        let mut visited = 0usize;
        while let Some(step) = stack.pop() {
            visited += 1;
            if visited > SYNTAX_OBJECTS {
                return Err(invalid(format!(
                    "Syntax larger than {SYNTAX_OBJECTS} steps"
                )));
            }
            match step {
                Step::Lit(text) => out.push_str(text),
                Step::Owned(text) => out.push_str(&text),
                Step::Syntax(p) if p == boxed(0) => out.push('M'),
                Step::Syntax(p) => self.syntax_step(p, &mut out, &mut stack)?,
                Step::Info(p) if p == boxed(2) => out.push('_'),
                Step::Info(p) => self.info_step(p, &mut out, &mut stack)?,
                Step::Substring(p) => self.substring_step(p, &mut out)?,
                Step::Preresolved(p) => self.preresolved_step(p, &mut out)?,
            }
        }
        Ok(out)
    }

    /// Open one `Syntax` constructor: write its head, push the rest in reverse.
    fn syntax_step(&self, p: u64, out: &mut String, stack: &mut Vec<Step>) -> OleanResult<()> {
        let (offset, tag, fields) = self.mdata_ctor(p, "Syntax")?;
        let field = |i: usize| self.read_u64_at(offset + 8 + 8 * i);
        match (tag, fields) {
            (1, 3) => {
                out.push_str("(N ");
                stack.push(Step::Lit("])"));
                let args = self.mdata_array(field(2)?)?;
                push_seq(stack, args.into_iter().map(Step::Syntax).collect());
                let mut kind = String::from(" ");
                self.mdata_name(field(1)?, &mut kind)?;
                kind.push_str(" [");
                stack.push(Step::Owned(kind));
                stack.push(Step::Info(field(0)?));
            }
            (2, 2) => {
                out.push_str("(A ");
                let mut val = String::from(" ");
                self.mdata_quoted(field(1)?, &mut val)?;
                val.push(')');
                stack.push(Step::Owned(val));
                stack.push(Step::Info(field(0)?));
            }
            (3, 4) => {
                out.push_str("(I ");
                stack.push(Step::Lit("])"));
                let pre =
                    self.mdata_list(field(3)?, SYNTAX_LIST_ITEMS, "Syntax.ident preresolved")?;
                push_seq(stack, pre.into_iter().map(Step::Preresolved).collect());
                let mut val = String::from(" ");
                self.mdata_name(field(2)?, &mut val)?;
                val.push_str(" [");
                stack.push(Step::Owned(val));
                stack.push(Step::Substring(field(1)?));
                stack.push(Step::Lit(" "));
                stack.push(Step::Info(field(0)?));
            }
            _ => {
                return Err(invalid(format!(
                    "unknown Syntax constructor (tag {tag}, {fields} fields)"
                )))
            }
        }
        Ok(())
    }

    fn info_step(&self, p: u64, out: &mut String, stack: &mut Vec<Step>) -> OleanResult<()> {
        let (offset, tag, fields) = self.mdata_ctor(p, "SourceInfo")?;
        let field = |i: usize| self.read_u64_at(offset + 8 + 8 * i);
        match (tag, fields) {
            (0, 4) => {
                out.push_str("(o ");
                let mut end = String::from(" ");
                self.mdata_pos(field(3)?, &mut end)?;
                end.push(')');
                stack.push(Step::Owned(end));
                stack.push(Step::Substring(field(2)?));
                let mut pos = String::from(" ");
                self.mdata_pos(field(1)?, &mut pos)?;
                pos.push(' ');
                stack.push(Step::Owned(pos));
                stack.push(Step::Substring(field(0)?));
            }
            (1, 2) => {
                out.push_str("(s ");
                self.mdata_pos(field(0)?, out)?;
                out.push(' ');
                self.mdata_pos(field(1)?, out)?;
                match self.bytes_at(offset + 8 + 16, 1)?[0] {
                    0 => out.push_str(" 0)"),
                    1 => out.push_str(" 1)"),
                    byte => {
                        return Err(invalid(format!(
                            "SourceInfo.synthetic: non-Bool canonical byte {byte}"
                        )))
                    }
                }
            }
            _ => {
                return Err(invalid(format!(
                    "unknown SourceInfo constructor (tag {tag}, {fields} fields)"
                )))
            }
        }
        Ok(())
    }

    fn substring_step(&self, p: u64, out: &mut String) -> OleanResult<()> {
        match self.mdata_ctor(p, "Substring.Raw")? {
            (offset, 0, 3) => {
                out.push('(');
                self.mdata_quoted(self.read_u64_at(offset + 8)?, out)?;
                out.push(' ');
                self.mdata_pos(self.read_u64_at(offset + 16)?, out)?;
                out.push(' ');
                self.mdata_pos(self.read_u64_at(offset + 24)?, out)?;
                out.push(')');
                Ok(())
            }
            (_, tag, fields) => Err(invalid(format!(
                "Substring.Raw: unexpected object (tag {tag}, {fields} fields)"
            ))),
        }
    }

    fn preresolved_step(&self, p: u64, out: &mut String) -> OleanResult<()> {
        match self.mdata_ctor(p, "Syntax.Preresolved")? {
            (offset, 0, 1) => {
                out.push_str("(ns ");
                self.mdata_name(self.read_u64_at(offset + 8)?, out)?;
                out.push(')');
                Ok(())
            }
            (offset, 1, 2) => {
                out.push_str("(decl ");
                self.mdata_name(self.read_u64_at(offset + 8)?, out)?;
                out.push_str(" [");
                let strs = self.mdata_list(
                    self.read_u64_at(offset + 16)?,
                    SYNTAX_LIST_ITEMS,
                    "Preresolved.decl fields",
                )?;
                for (i, s) in strs.iter().enumerate() {
                    if i > 0 {
                        out.push(' ');
                    }
                    self.mdata_quoted(*s, out)?;
                }
                out.push_str("])");
                Ok(())
            }
            (_, tag, fields) => Err(invalid(format!(
                "unknown Syntax.Preresolved constructor (tag {tag}, {fields} fields)"
            ))),
        }
    }

    /// The element pointers of an `Array Syntax`.
    fn mdata_array(&self, pointer: u64) -> OleanResult<Vec<u64>> {
        if !is_ptr(pointer) {
            return Err(invalid(format!("expected an Array, found {pointer:#x}")));
        }
        let offset = self.ptr_to_offset(pointer)?;
        let header = self.read_header_at(offset)?;
        if header.tag != tags::ARRAY || header.rc != 0 {
            return Err(invalid(format!(
                "expected an Array, found tag {}",
                header.tag
            )));
        }
        let size = self.read_usize_at(offset + 8, "Syntax args")?;
        let capacity = self.read_u64_at(offset + 16)?;
        if size > SYNTAX_LIST_ITEMS || size as u64 > capacity {
            return Err(invalid(format!(
                "Syntax args: size {size}, capacity {capacity}"
            )));
        }
        self.validate_array_bounds(offset, size)?;
        (0..size)
            .map(|i| self.read_u64_at(self.array_elem_offset(offset, i, "Syntax args")?))
            .collect()
    }
}

#[cfg(test)]
#[path = "mdata_tests.rs"]
mod tests;
