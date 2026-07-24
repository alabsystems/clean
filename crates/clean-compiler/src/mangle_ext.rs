// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended name mangling with support for C, Rust, and LLVM targets, plus demangling.

use std::collections::HashMap;

use clean_kernel::name::NameInner;
use clean_kernel::Name;

use crate::mangle::mangle_string;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum MangleTarget {
    C,
    Rust,
    Llvm,
}

impl MangleTarget {
    fn prefix(self) -> &'static str {
        match self {
            Self::C => "l_",
            Self::Rust => "clean_",
            Self::Llvm => "@clean_",
        }
    }

    fn separator(self) -> &'static str {
        match self {
            Self::Rust => "__",
            Self::C | Self::Llvm => "_",
        }
    }
}

#[derive(Debug, Clone)]
pub(crate) struct MangleConfig {
    pub(crate) target: MangleTarget,
    pub(crate) encode_namespaces: bool,
    pub(crate) encode_type_suffix: bool,
    pub(crate) max_length: Option<usize>,
    pub(crate) export_override: Option<String>,
}

impl Default for MangleConfig {
    fn default() -> Self {
        Self {
            target: MangleTarget::C,
            encode_namespaces: true,
            encode_type_suffix: false,
            max_length: None,
            export_override: None,
        }
    }
}

#[derive(Debug, Clone, Default)]
pub(crate) struct MangleStats {
    pub(crate) total_mangled: usize,
    pub(crate) collisions_detected: usize,
    pub(crate) max_name_length: usize,
    pub(crate) unicode_names: usize,
}

pub(crate) type CollisionMap = HashMap<String, Vec<Name>>;

pub(crate) fn mangle_ext(name: &Name, config: &MangleConfig) -> String {
    if let Some(export) = &config.export_override {
        return export.clone();
    }

    let mut result = String::from(config.target.prefix());
    let stem = if config.encode_namespaces {
        namespace_encode_for_target(name, config.target)
    } else {
        name.last_component()
            .map_or_else(String::new, |last| mangle_string(&last))
    };
    result.push_str(&stem);

    if config.encode_type_suffix {
        // Use the printable name as a stable fallback until typed overload
        // information is threaded through code generation.
        result.push_str(&encode_type_suffix(&name.to_string()));
    }

    match config.max_length {
        Some(max_length) if result.len() > max_length => truncate_and_hash(&result, max_length),
        _ => result,
    }
}

pub(crate) fn mangle_c(name: &Name) -> String {
    mangle_ext(name, &MangleConfig::default())
}

pub(crate) fn mangle_rust(name: &Name) -> String {
    let config = MangleConfig {
        target: MangleTarget::Rust,
        ..MangleConfig::default()
    };
    mangle_ext(name, &config)
}

pub(crate) fn mangle_llvm(name: &Name) -> String {
    let config = MangleConfig {
        target: MangleTarget::Llvm,
        ..MangleConfig::default()
    };
    mangle_ext(name, &config)
}

pub(crate) fn namespace_encode(name: &Name) -> String {
    namespace_encode_for_target(name, MangleTarget::C)
}

pub(crate) fn demangle(mangled: &str) -> Option<String> {
    let (body, target) = if let Some(rest) = mangled.strip_prefix("@clean_") {
        (rest, MangleTarget::Llvm)
    } else if let Some(rest) = mangled.strip_prefix("clean_") {
        (rest, MangleTarget::Rust)
    } else {
        let rest = mangled.strip_prefix("l_")?;
        (rest, MangleTarget::C)
    };

    demangle_body(body, target)
}

pub(crate) fn encode_type_suffix(suffix: &str) -> String {
    format!("_T_{}", mangle_string(suffix))
}

pub(crate) fn detect_collisions(names: &[Name], config: &MangleConfig) -> CollisionMap {
    let mut collisions: CollisionMap = HashMap::new();
    for name in names {
        collisions
            .entry(mangle_ext(name, config))
            .or_default()
            .push(name.clone());
    }
    collisions.retain(|_, originals| originals.len() > 1);
    collisions
}

pub(crate) fn resolve_collision(name: &Name, index: usize, config: &MangleConfig) -> String {
    format!("{}_C{}", mangle_ext(name, config), index)
}

pub(crate) fn collect_stats(names: &[Name], config: &MangleConfig) -> MangleStats {
    let collisions = detect_collisions(names, config);
    let mut stats = MangleStats {
        total_mangled: names.len(),
        collisions_detected: collisions
            .values()
            .map(|group| group.len().saturating_sub(1))
            .sum(),
        ..MangleStats::default()
    };

    for name in names {
        let mangled = mangle_ext(name, config);
        stats.max_name_length = stats.max_name_length.max(mangled.len());
        if name_has_unicode(name) {
            stats.unicode_names += 1;
        }
    }

    stats
}

pub(crate) fn encode_unicode_safe(s: &str) -> String {
    let mut result = String::with_capacity(s.len());
    for ch in s.chars() {
        if ch.is_ascii() {
            result.push(ch);
        } else {
            let code = ch as u32;
            if code <= 0xffff {
                result.push_str(&format!("_u{:04x}", code));
            } else {
                result.push_str(&format!("_U{:08x}", code));
            }
        }
    }
    result
}

pub(crate) fn is_valid_c_ident(s: &str) -> bool {
    let mut chars = s.chars();
    match chars.next() {
        Some(ch) if ch.is_ascii_alphabetic() || ch == '_' => {
            chars.all(|c| c.is_ascii_alphanumeric() || c == '_')
        }
        _ => false,
    }
}

pub(crate) fn is_valid_rust_ident(s: &str) -> bool {
    let mut chars = s.chars();
    match chars.next() {
        Some(ch) if ch.is_ascii_alphabetic() || ch == '_' => {
            chars.all(|c| c.is_ascii_alphanumeric() || c == '_')
        }
        _ => false,
    }
}

fn namespace_encode_for_target(name: &Name, target: MangleTarget) -> String {
    let components = collect_components(name);
    let mut encoded = String::new();
    let separator = target.separator();

    for (idx, raw) in components.iter().enumerate() {
        let prev = idx
            .checked_sub(1)
            .and_then(|prev_idx| components.get(prev_idx));
        if idx > 0 {
            encoded.push_str(separator);
        }
        encoded.push_str(&encode_component(raw, prev.map(String::as_str), target));
    }

    encoded
}

fn collect_components(name: &Name) -> Vec<String> {
    fn go(name: &Name, acc: &mut Vec<String>) {
        match name.inner() {
            NameInner::Anon => {}
            NameInner::Str(parent, s) => {
                go(parent, acc);
                acc.push(s.to_string());
            }
            NameInner::Num(parent, n) => {
                go(parent, acc);
                acc.push(n.to_string());
            }
        }
    }

    let mut components = Vec::new();
    go(name, &mut components);
    components
}

fn encode_component(raw: &str, prev: Option<&str>, target: MangleTarget) -> String {
    let mut mangled = mangle_string(raw);
    if matches!(target, MangleTarget::Rust) {
        mangled = mangled.replace("__", "____");
    }
    if needs_disambiguation(prev, &mangled) {
        format!("_00{mangled}")
    } else {
        mangled
    }
}

fn needs_disambiguation(prev: Option<&str>, mangled: &str) -> bool {
    prev.is_some_and(|component| component.ends_with('_')) || check_disambiguation_pattern(mangled)
}

fn check_disambiguation_pattern(s: &str) -> bool {
    let chars: Vec<char> = s.chars().collect();
    if chars.is_empty() {
        return true;
    }

    match chars[0] {
        '_' => chars
            .get(1)
            .is_none_or(|c| *c == 'x' || *c == 'u' || *c == 'U' || c.is_ascii_digit()),
        c if c.is_ascii_digit() => true,
        _ => false,
    }
}

fn truncate_and_hash(s: &str, max_length: usize) -> String {
    if max_length == 0 {
        return String::new();
    }

    let hash = stable_hash_hex(s);
    if max_length <= hash.len() {
        return hash[..max_length].to_string();
    }

    let keep = max_length - hash.len() - 1;
    format!("{}_{hash}", &s[..keep])
}

fn stable_hash_hex(s: &str) -> String {
    let mut hash = 0xcbf29ce484222325_u64;
    for byte in s.bytes() {
        hash ^= u64::from(byte);
        hash = hash.wrapping_mul(0x100000001b3);
    }
    format!("{hash:016x}")
}

fn decode_c_like_components(body: &str) -> Option<Vec<String>> {
    let bytes = body.as_bytes();
    let mut components = Vec::new();
    let mut current = String::new();
    let mut i = 0;

    while i < bytes.len() {
        if current.is_empty() && bytes[i..].starts_with(b"_00") {
            i += 3;
            continue;
        }

        if let Some((ch, consumed)) = decode_escape(body, i) {
            current.push(ch);
            i += consumed;
            continue;
        }

        if !current.is_empty()
            && (bytes[i..].starts_with(b"__00") || bytes[i..].starts_with(b"___"))
        {
            components.push(std::mem::take(&mut current));
            i += 1;
            continue;
        }

        if bytes[i..].starts_with(b"__") {
            current.push('_');
            i += 2;
            continue;
        }

        if bytes[i] == b'_' {
            components.push(std::mem::take(&mut current));
            i += 1;
            continue;
        }

        current.push(bytes[i] as char);
        i += 1;
    }

    if !current.is_empty() || body.is_empty() {
        components.push(current);
    }

    Some(components)
}

fn decode_rust_components(body: &str) -> Option<Vec<String>> {
    let bytes = body.as_bytes();
    let mut components = Vec::new();
    let mut current = String::new();
    let mut i = 0;

    while i < bytes.len() {
        if current.is_empty() && bytes[i..].starts_with(b"_00") {
            i += 3;
            continue;
        }

        if let Some((ch, consumed)) = decode_escape(body, i) {
            current.push(ch);
            i += consumed;
            continue;
        }

        if !current.is_empty()
            && (bytes[i..].starts_with(b"___00") || bytes[i..].starts_with(b"______"))
        {
            components.push(std::mem::take(&mut current));
            i += 2;
            continue;
        }

        if bytes[i..].starts_with(b"____") {
            current.push('_');
            i += 4;
            continue;
        }

        if bytes[i..].starts_with(b"__") {
            components.push(std::mem::take(&mut current));
            i += 2;
            continue;
        }

        if bytes[i] == b'_' {
            return None;
        }

        current.push(bytes[i] as char);
        i += 1;
    }

    if !current.is_empty() || body.is_empty() {
        components.push(current);
    }

    Some(components)
}

fn decode_escape(body: &str, start: usize) -> Option<(char, usize)> {
    let rest = &body[start..];
    if rest.starts_with("_x") {
        return decode_hex_escape(body, start + 2, 2).map(|ch| (ch, 4));
    }
    if rest.starts_with("_u") {
        return decode_hex_escape(body, start + 2, 4).map(|ch| (ch, 6));
    }
    if rest.starts_with("_U") {
        return decode_hex_escape(body, start + 2, 8).map(|ch| (ch, 10));
    }
    None
}

fn decode_hex_escape(body: &str, start: usize, digits: usize) -> Option<char> {
    let end = start.checked_add(digits)?;
    let hex = body.get(start..end)?;
    let value = u32::from_str_radix(hex, 16).ok()?;
    char::from_u32(value)
}

fn name_has_unicode(name: &Name) -> bool {
    match name.inner() {
        NameInner::Anon => false,
        NameInner::Str(parent, s) => name_has_unicode(parent) || !s.is_ascii(),
        NameInner::Num(parent, _) => name_has_unicode(parent),
    }
}

fn demangle_body(body: &str, target: MangleTarget) -> Option<String> {
    if let Some(idx) = body.rfind("_T_") {
        let prefix = &body[..idx];
        let suffix = &body[idx + 3..];
        if let Some(base) = decode_components(prefix, target) {
            if suffix == mangle_string(&base) {
                return Some(base);
            }
        }
    }

    decode_components(body, target)
}

fn decode_components(body: &str, target: MangleTarget) -> Option<String> {
    let components = match target {
        MangleTarget::Rust => decode_rust_components(body)?,
        MangleTarget::C | MangleTarget::Llvm => decode_c_like_components(body)?,
    };
    Some(components.join("."))
}
