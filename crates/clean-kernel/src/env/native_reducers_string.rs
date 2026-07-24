// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended String/Char native reducers for the kernel type checker.
//!
//! O(1) computation for String/Char operations on literal values, avoiding
//! expensive expansion to constructor form. Part of #3134.

use crate::env::Environment;
use crate::expr::{Expr, ExprKind, Literal};
use crate::name::Name;
use std::sync::LazyLock;

/// Well-known names for extended string/char native reducers.
pub(crate) mod names {
    use crate::name::Name;
    use std::sync::LazyLock;

    pub(crate) static STRING_GET: LazyLock<Name> =
        LazyLock::new(|| Name::from_string("String.get"));
    pub(crate) static STRING_NEXT: LazyLock<Name> =
        LazyLock::new(|| Name::from_string("String.next"));
    pub(crate) static STRING_PREV: LazyLock<Name> =
        LazyLock::new(|| Name::from_string("String.prev"));
    pub(crate) static STRING_UTF8_AT_END: LazyLock<Name> =
        LazyLock::new(|| Name::from_string("String.atEnd"));
    pub(crate) static STRING_UTF8_EXTRACT: LazyLock<Name> =
        LazyLock::new(|| Name::from_string("String.extract"));
    pub(crate) static STRING_INTERCALATE: LazyLock<Name> =
        LazyLock::new(|| Name::from_string("String.intercalate"));
    pub(crate) static STRING_IS_PREFIX_OF: LazyLock<Name> =
        LazyLock::new(|| Name::from_string("String.isPrefixOf"));
    pub(crate) static STRING_FRONT: LazyLock<Name> =
        LazyLock::new(|| Name::from_string("String.front"));
    pub(crate) static STRING_DEC_LT: LazyLock<Name> =
        LazyLock::new(|| Name::from_string("String.decLt"));
    pub(crate) static STRING_HASH: LazyLock<Name> =
        LazyLock::new(|| Name::from_string("String.hash"));
    pub(crate) static STRING_SINGLETON: LazyLock<Name> =
        LazyLock::new(|| Name::from_string("String.singleton"));
    pub(crate) static STRING_TAKE: LazyLock<Name> =
        LazyLock::new(|| Name::from_string("String.take"));
    pub(crate) static STRING_DROP: LazyLock<Name> =
        LazyLock::new(|| Name::from_string("String.drop"));
    pub(crate) static STRING_TO_LOWER: LazyLock<Name> =
        LazyLock::new(|| Name::from_string("String.toLower"));
    pub(crate) static STRING_TO_UPPER: LazyLock<Name> =
        LazyLock::new(|| Name::from_string("String.toUpper"));
}

/// Constructor names used in result building.
mod ctor_names {
    use crate::name::Name;
    use std::sync::LazyLock;

    pub(crate) static CHAR_OF_NAT: LazyLock<Name> =
        LazyLock::new(|| Name::from_string("Char.ofNat"));
    pub(crate) static BOOL_TRUE: LazyLock<Name> = LazyLock::new(|| Name::from_string("Bool.true"));
    pub(crate) static BOOL_FALSE: LazyLock<Name> =
        LazyLock::new(|| Name::from_string("Bool.false"));
}

/// Extract a String value from an expression.
pub(crate) fn get_string_val(e: &Expr) -> Option<&str> {
    match e.kind() {
        ExprKind::Lit(Literal::String(s)) => Some(s),
        _ => None,
    }
}

/// Extract a Nat value from an expression.
pub(crate) fn get_nat_val(e: &Expr) -> Option<u64> {
    match e.kind() {
        ExprKind::Lit(Literal::Nat(n)) => n.to_u64(),
        _ => None,
    }
}

/// Extract a Char value from a `Char.mk …` constructor application.
///
/// Delegates to [`super::native_reducers_char::char_code_point`], which
/// recognizes BOTH the pure-clean 1-field `Char.mk <nat>` and the real-olean
/// 2-field `Char.mk (UInt32.ofBitVec (BitVec…)) valid` constructor shapes (and
/// bare Nat literals). Declines when the field is not yet a recognizable literal
/// so the kernel falls back to δ/ι reduction.
pub(crate) fn get_char_val(e: &Expr) -> Option<char> {
    char::from_u32(super::native_reducers_char::char_code_point(e)? as u32)
}

/// Build a Char expression from a Rust char value.
///
/// Emits **`Char.ofNat <code_point>`** — the spelling Lean's own kernel emits
/// (`string_lit_to_constructor`); it δ-unfolds to the genuine constructor in
/// both the pure-clean (1-field `Char.mk : Nat → Char`) and real-olean (2-field
/// `Char.mk : UInt32 → … → Char`) environments. The prior bare `Char.mk <nat>`
/// was ill-typed against the genuine 2-field ctor. Code points reaching here are
/// always valid (chars extracted from a valid `String`), so the `Char.ofNat`
/// validity gate is a no-op for them.
pub(crate) fn mk_char_expr(c: char) -> Expr {
    Expr::app(
        Expr::const_(ctor_names::CHAR_OF_NAT.clone(), vec![]),
        Expr::nat_lit(c as u64),
    )
}

/// Build a Bool expression.
pub(crate) fn mk_bool_expr(val: bool) -> Expr {
    if val {
        Expr::const_(ctor_names::BOOL_TRUE.clone(), vec![])
    } else {
        Expr::const_(ctor_names::BOOL_FALSE.clone(), vec![])
    }
}

// === String.get : String → String.Pos → Char ===
// In Lean 4, String.Pos is a structure wrapping a Nat (byte offset).
// String.get s ⟨n⟩ returns the character at byte offset n.

/// Native reducer for `String.get : String → String.Pos → Char`.
///
/// String.Pos is `{ byteIdx : Nat }`, so after WHNF the position argument
/// reduces to a Nat literal representing the byte offset.
pub(crate) fn reduce_string_get(args: &[&Expr]) -> Option<Expr> {
    if args.len() < 2 {
        return None;
    }
    let s = get_string_val(args[0])?;
    let byte_pos = get_nat_val(args[1])? as usize;

    // Get character at byte position
    if byte_pos >= s.len() {
        // Out of bounds: return default char (Lean 4 returns '\x00' / Char.mk 0)
        return Some(mk_char_expr('\0'));
    }
    // SOUNDNESS: byte_pos is a proof-controlled Nat (String.Pos) with no
    // char-boundary guarantee; slicing `s[byte_pos..]` at an interior UTF-8 byte
    // panics the trusted kernel mid-whnf. `str::get` returns None on a non-boundary
    // index, so the native reducer declines and the kernel falls back to
    // definitional unfolding (mirrors reduce_string_extract's is_char_boundary guard).
    let c = s.get(byte_pos..)?.chars().next()?;
    Some(mk_char_expr(c))
}

/// Native reducer for `String.next : String → String.Pos → String.Pos`.
///
/// Advances the byte position past the current character.
/// Returns the byte offset of the next character.
pub(crate) fn reduce_string_next(args: &[&Expr]) -> Option<Expr> {
    if args.len() < 2 {
        return None;
    }
    let s = get_string_val(args[0])?;
    let byte_pos = get_nat_val(args[1])? as usize;

    if byte_pos >= s.len() {
        // Past the end: return byte_pos + 1 (Lean 4 semantics)
        return Some(Expr::nat_lit(byte_pos as u64 + 1));
    }
    // SOUNDNESS: see reduce_string_get — `str::get` declines on a non-char-boundary
    // byte_pos instead of panicking the slice (e.g. `String.next "é" ⟨1⟩`, byte 1 interior).
    let c = s.get(byte_pos..)?.chars().next()?;
    let next_pos = byte_pos + c.len_utf8();
    Some(Expr::nat_lit(next_pos as u64))
}

/// Native reducer for `String.prev : String → String.Pos → String.Pos`.
///
/// Moves the byte position back one character.
pub(crate) fn reduce_string_prev(args: &[&Expr]) -> Option<Expr> {
    if args.len() < 2 {
        return None;
    }
    let s = get_string_val(args[0])?;
    let byte_pos = get_nat_val(args[1])? as usize;

    if byte_pos == 0 {
        return Some(Expr::nat_lit(0));
    }

    // Find the start of the previous character.
    // SOUNDNESS: a non-char-boundary cut would panic `&s[..cut]`; `str::get`
    // declines (returns None) instead, so the kernel falls back to unfolding.
    let cut = std::cmp::min(byte_pos, s.len());
    let prefix = s.get(..cut)?;
    if let Some(c) = prefix.chars().next_back() {
        let prev_pos = prefix.len() - c.len_utf8();
        Some(Expr::nat_lit(prev_pos as u64))
    } else {
        Some(Expr::nat_lit(0))
    }
}

/// Native reducer for `String.atEnd : String → String.Pos → Bool`.
///
/// Returns true if the position is at or past the end of the string.
pub(crate) fn reduce_string_at_end(args: &[&Expr]) -> Option<Expr> {
    if args.len() < 2 {
        return None;
    }
    let s = get_string_val(args[0])?;
    let byte_pos = get_nat_val(args[1])? as usize;
    Some(mk_bool_expr(byte_pos >= s.len()))
}

/// Native reducer for `String.extract : String → String.Pos → String.Pos → String`.
///
/// Extracts a substring between two byte positions.
pub(crate) fn reduce_string_extract(args: &[&Expr]) -> Option<Expr> {
    if args.len() < 3 {
        return None;
    }
    let s = get_string_val(args[0])?;
    let start = get_nat_val(args[1])? as usize;
    let stop = get_nat_val(args[2])? as usize;

    let start = std::cmp::min(start, s.len());
    let stop = std::cmp::min(stop, s.len());

    if start >= stop {
        return Some(Expr::str_lit(""));
    }

    // Validate that start and stop are on character boundaries
    if !s.is_char_boundary(start) || !s.is_char_boundary(stop) {
        return None;
    }

    Some(Expr::str_lit(&s[start..stop]))
}

/// Native reducer for `String.intercalate : String → List String → String`.
///
/// Joins a list of strings with a separator. The list argument must be
/// in constructor form: `List.cons s1 (List.cons s2 ... List.nil)`.
///
/// Since native reducers receive arguments BEFORE WHNF, this reducer
/// works only when the list is already fully reduced to string literals.
/// For nested list forms, it returns None and lets the kernel unfold normally.
pub(crate) fn reduce_string_intercalate(args: &[&Expr]) -> Option<Expr> {
    if args.len() < 2 {
        return None;
    }
    let sep = get_string_val(args[0])?;

    // Extract strings from the list. The list is: List.cons {String} s1 (List.cons ...)
    // or List.nil {String}
    let mut strings: Vec<&str> = Vec::new();
    let mut current = args[1];

    loop {
        let head = current.get_app_fn();
        let list_args = current.get_app_args();

        if let ExprKind::Const(name, _) = head.kind() {
            static LIST_NIL: LazyLock<Name> = LazyLock::new(|| Name::from_string("List.nil"));
            static LIST_CONS: LazyLock<Name> = LazyLock::new(|| Name::from_string("List.cons"));

            if *name == *LIST_NIL {
                break;
            }
            if *name == *LIST_CONS {
                // List.cons has args: [type, element, tail]
                if list_args.len() < 3 {
                    return None;
                }
                let s = get_string_val(list_args[1])?;
                strings.push(s);
                current = list_args[2];
                continue;
            }
        }
        return None; // Not a concrete list
    }

    let result = strings.join(sep);
    Some(Expr::str_lit(&result))
}

/// Native reducer for `String.isPrefixOf : String → String → Bool`.
pub(crate) fn reduce_string_is_prefix_of(args: &[&Expr]) -> Option<Expr> {
    if args.len() < 2 {
        return None;
    }
    let prefix = get_string_val(args[0])?;
    let s = get_string_val(args[1])?;
    Some(mk_bool_expr(s.starts_with(prefix)))
}

/// Native reducer for `String.front : String → Char`.
///
/// Returns the first character of the string, or '\0' for empty string.
pub(crate) fn reduce_string_front(args: &[&Expr]) -> Option<Expr> {
    if args.is_empty() {
        return None;
    }
    let s = get_string_val(args[0])?;
    let c = s.chars().next().unwrap_or('\0');
    Some(mk_char_expr(c))
}

/// Native reducer for `String.decLt : (a b : String) → Decidable (a < b)`.
///
/// String lexicographic ordering is not backed by an in-kernel order proof, so
/// this *declines* (returns `None`) rather than emit a `Decidable sorryAx`
/// witness (false branch) or a type-incorrect `Decidable.isTrue (Eq.refl …)`
/// for the `<` proposition (true branch). Sound by omission.
pub(crate) fn reduce_string_dec_lt(_args: &[&Expr]) -> Option<Expr> {
    None
}

/// Native reducer for `String.singleton : Char → String`.
///
/// Creates a single-character string from a Char value.
pub(crate) fn reduce_string_singleton(args: &[&Expr]) -> Option<Expr> {
    if args.is_empty() {
        return None;
    }
    let c = get_char_val(args[0])?;
    let mut s = String::with_capacity(c.len_utf8());
    s.push(c);
    Some(Expr::str_lit(&s))
}

/// Native reducer for `String.take : String → Nat → String`.
///
/// Returns the first n characters of the string.
pub(crate) fn reduce_string_take(args: &[&Expr]) -> Option<Expr> {
    if args.len() < 2 {
        return None;
    }
    let s = get_string_val(args[0])?;
    let n = get_nat_val(args[1])? as usize;
    let result: String = s.chars().take(n).collect();
    Some(Expr::str_lit(&result))
}

/// Native reducer for `String.drop : String → Nat → String`.
///
/// Returns the string with the first n characters removed.
pub(crate) fn reduce_string_drop(args: &[&Expr]) -> Option<Expr> {
    if args.len() < 2 {
        return None;
    }
    let s = get_string_val(args[0])?;
    let n = get_nat_val(args[1])? as usize;
    let result: String = s.chars().skip(n).collect();
    Some(Expr::str_lit(&result))
}

/// MurmurHash64A — full implementation matching Lean 4's `hash_str` in runtime/hash.cpp.
///
/// This is the standard MurmurHash2-64A by Austin Appleby, used by Lean 4 for
/// `lean_string_hash` (seed=11) and `lean_name_hash` (via `String.hash`).
/// Reference: Lean 4 src/runtime/hash.cpp lines 15-55.
//
// Trust: infrastructure (a content hash for Name/String caching & dedup), NOT part of
// the proof-soundness TCB. Rewritten so the verifier DISCHARGES it (no `#[trust::skip]`):
// the 8-byte blocks come from `slice::as_chunks::<8>()`, whose `&[[u8; 8]]` element TYPE
// guarantees 8 bytes — every block read is in-bounds by construction, with no BoundsCheck
// and no `try_into().unwrap()`. The <8-byte tail is folded by iterator (no indexing), and
// its shift amount is masked (`& 63`, provably < 64) with `wrapping_mul` for the index
// arithmetic — so there is no overflow, shift, or bounds panic path left to refute.
pub(crate) fn murmur_hash_64a(data: &[u8], seed: u64) -> u64 {
    const M: u64 = 0xc6a4_a793_5bd1_e995;
    const R: u32 = 47;
    let len = data.len();
    let mut h: u64 = seed ^ (len as u64).wrapping_mul(M);

    // Process 8-byte chunks. `as_chunks::<8>()` => (`&[[u8; 8]]`, `&[u8]` remainder<8).
    let (blocks, tail) = data.as_chunks::<8>();
    for block in blocks {
        let mut k: u64 = u64::from_le_bytes(*block);
        k = k.wrapping_mul(M);
        // `R & 63` is identical to `R` (R = 47 < 64) but makes the shift amount
        // SYNTACTICALLY `< 64`, so the verifier discharges the Shr-overflow VC
        // directly (same trick as the tail `& 63` mask below).
        k ^= k >> (R & 63);
        k = k.wrapping_mul(M);
        h ^= k;
        h = h.wrapping_mul(M);
    }

    // Process the remaining <8 bytes. Forward iteration is XOR-equivalent to the C
    // switch fallthrough: each byte `b` at index `i` contributes `b << (8*i)`, and XOR
    // is order-independent; `h *= M` runs once iff the tail is non-empty.
    for (i, &b) in tail.iter().enumerate() {
        h ^= (b as u64) << (i.wrapping_mul(8) & 63);
    }
    if !tail.is_empty() {
        h = h.wrapping_mul(M);
    }

    h ^= h >> (R & 63);
    h = h.wrapping_mul(M);
    h ^= h >> (R & 63);
    h
}

/// Native reducer for `String.hash : String → UInt64`.
///
/// Uses Lean 4's MurmurHash64A with seed 11, matching `lean_string_hash`
/// from runtime/object.cpp (which calls `hash_str(sz, str, 11)`).
/// Reference: Lean 4 src/runtime/object.cpp:2412-2416, src/runtime/hash.cpp:57-59.
pub(crate) fn reduce_string_hash(args: &[&Expr]) -> Option<Expr> {
    if args.is_empty() {
        return None;
    }
    let s = get_string_val(args[0])?;
    let h = murmur_hash_64a(s.as_bytes(), 11);
    Some(Expr::nat_lit(h))
}

/// Native reducer for `String.toLower : String → String`.
pub(crate) fn reduce_string_to_lower(args: &[&Expr]) -> Option<Expr> {
    if args.is_empty() {
        return None;
    }
    let s = get_string_val(args[0])?;
    Some(Expr::str_lit(s.to_lowercase()))
}

/// Native reducer for `String.toUpper : String → String`.
pub(crate) fn reduce_string_to_upper(args: &[&Expr]) -> Option<Expr> {
    if args.is_empty() {
        return None;
    }
    let s = get_string_val(args[0])?;
    Some(Expr::str_lit(s.to_uppercase()))
}

/// Register all extended String native reducers on the environment.
impl Environment {
    pub(crate) fn init_string_native_reducers(&mut self) {
        // String operations
        self.register_native_reducer(names::STRING_GET.clone(), reduce_string_get);
        self.register_native_reducer(names::STRING_NEXT.clone(), reduce_string_next);
        self.register_native_reducer(names::STRING_PREV.clone(), reduce_string_prev);
        self.register_native_reducer(names::STRING_UTF8_AT_END.clone(), reduce_string_at_end);
        self.register_native_reducer(names::STRING_UTF8_EXTRACT.clone(), reduce_string_extract);
        self.register_native_reducer(names::STRING_INTERCALATE.clone(), reduce_string_intercalate);
        self.register_native_reducer(
            names::STRING_IS_PREFIX_OF.clone(),
            reduce_string_is_prefix_of,
        );
        self.register_native_reducer(names::STRING_FRONT.clone(), reduce_string_front);
        self.register_native_reducer(names::STRING_DEC_LT.clone(), reduce_string_dec_lt);
        self.register_native_reducer(names::STRING_HASH.clone(), reduce_string_hash);
        self.register_native_reducer(names::STRING_SINGLETON.clone(), reduce_string_singleton);
        self.register_native_reducer(names::STRING_TAKE.clone(), reduce_string_take);
        self.register_native_reducer(names::STRING_DROP.clone(), reduce_string_drop);
        self.register_native_reducer(names::STRING_TO_LOWER.clone(), reduce_string_to_lower);
        self.register_native_reducer(names::STRING_TO_UPPER.clone(), reduce_string_to_upper);
    }
}

#[cfg(test)]
#[path = "native_reducers_string_tests.rs"]
mod tests;
