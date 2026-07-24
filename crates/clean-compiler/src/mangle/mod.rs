// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Name mangling for code generation
//!
//! Converts Lean `Name` values to valid C/LLVM/Rust identifiers.
//! Implements the Lean 4 mangling algorithm for compatibility.
//!
//! # Algorithm
//!
//! - Alphanumeric characters pass through unchanged
//! - Underscores double to `__` (to avoid collision with escape sequences)
//! - ASCII non-alnum: `_xHH` (e.g., `+` → `_x2b`)
//! - Unicode < 0x100: `_xHH` (e.g., `é` → `_xe9`)
//! - Unicode < 0x10000: `_uHHHH` (e.g., `α` → `_u03b1`)
//! - Unicode ≥ 0x10000: `_UHHHHHHHH` (e.g., `𝕊` → `_U0001d54a`)
//!
//! # Reference
//!
//! Lean 4: `src/Lean/Compiler/NameMangling.lean` (240 lines)
//! Authors: Leonardo de Moura, Robin Arnez
//!
//! Part of #995

use clean_kernel::name::NameInner;
use clean_kernel::Name;

/// Mangle a string to a valid C identifier component.
///
/// This handles individual characters:
/// - `[a-zA-Z0-9]` → unchanged
/// - `_` → `__`
/// - ASCII non-alnum → `_xHH`
/// - Unicode < 0x100 → `_xHH`
/// - Unicode < 0x10000 → `_uHHHH`
/// - Unicode ≥ 0x10000 → `_UHHHHHHHH`
pub fn mangle_string(s: &str) -> String {
    let mut result = String::with_capacity(s.len() * 2);

    for c in s.chars() {
        if c.is_ascii_alphanumeric() {
            result.push(c);
        } else if c == '_' {
            result.push_str("__");
        } else {
            let code = c as u32;
            if code < 0x100 {
                result.push_str(&format!("_x{:02x}", code));
            } else if code < 0x10000 {
                result.push_str(&format!("_u{:04x}", code));
            } else {
                result.push_str(&format!("_U{:08x}", code));
            }
        }
    }

    result
}

/// Check if a mangled string starts with a disambiguation pattern.
///
/// Patterns that need disambiguation prefix:
/// - Starts with `_x`, `_u`, `_U` (escape sequences)
/// - Starts with `_` followed by digit
/// - Starts with digit
/// - Empty string
fn check_disambiguation_pattern(s: &str) -> bool {
    let chars: Vec<char> = s.chars().collect();
    if chars.is_empty() {
        return true;
    }

    match chars[0] {
        '_' => {
            // Check for _x, _u, _U patterns or digit
            chars
                .get(1)
                .is_none_or(|c| *c == 'x' || *c == 'u' || *c == 'U' || c.is_ascii_digit())
        }
        c if c.is_ascii_digit() => true, // Starts with digit
        _ => false,
    }
}

/// Check if disambiguation is needed for this component.
///
/// Disambiguation (`_00` prefix) is needed when:
/// - Previous component ends with underscore
/// - Current component starts with a disambiguation pattern
fn needs_disambiguation(prev: Option<&Name>, mangled: &str) -> bool {
    // Previous component ends with underscore
    let prev_ends_underscore = match prev.map(|n| n.inner()) {
        Some(NameInner::Str(_, s)) => s.ends_with('_'),
        _ => false,
    };

    // Current starts with disambiguation pattern
    let starts_with_pattern = check_disambiguation_pattern(mangled);

    prev_ends_underscore || starts_with_pattern
}

/// Mangle a name component with disambiguation if needed.
fn mangle_name_component(prev: Option<&Name>, s: &str) -> String {
    let mangled = mangle_string(s);

    // Check if disambiguation needed
    if needs_disambiguation(prev, &mangled) {
        format!("_00{}", mangled)
    } else {
        mangled
    }
}

/// Internal helper for name mangling with configurable prefix.
fn mangle_name_aux(name: &Name, prefix: &str) -> String {
    match name.inner() {
        NameInner::Anon => prefix.to_string(),
        NameInner::Str(parent, s) => {
            let parent_mangled = mangle_name_aux(parent, prefix);
            let component = mangle_name_component(Some(parent), s);
            if parent.is_anon() {
                format!("{}{}", prefix, component)
            } else {
                format!("{}_{}", parent_mangled, component)
            }
        }
        NameInner::Num(parent, n) => {
            let parent_mangled = mangle_name_aux(parent, prefix);
            if parent.is_anon() {
                format!("{}{}_", prefix, n) // Numeric-only name with prefix
            } else {
                format!("{}_{}__", parent_mangled, n)
            }
        }
    }
}

/// Mangle a Lean Name to a valid C identifier.
///
/// The mangled name is prefixed with `l_` to avoid C reserved word collisions.
///
/// # Examples
///
/// ```
/// use clean_compiler::mangle::mangle_name;
/// use clean_kernel::Name;
///
/// assert_eq!(mangle_name(&Name::from_string("foo")), "l_foo");
/// assert_eq!(mangle_name(&Name::from_string("Nat.add")), "l_Nat_add");
/// ```
pub fn mangle_name(name: &Name) -> String {
    mangle_name_aux(name, "l_")
}

/// Mangle name for boxed version of function (interpreter support).
///
/// Appends `___boxed` (or `_00__boxed` if mangled ends with `__`).
pub fn mangle_boxed_name(mangled: &str) -> String {
    if mangled.ends_with("__") {
        format!("{}_00__boxed", mangled)
    } else {
        format!("{}___boxed", mangled)
    }
}

/// Mangle name for module initialization function.
///
/// Format: `initialize_<mangled_name>`
pub fn mangle_module_init(module: &Name) -> String {
    format!("initialize_{}", mangle_name_aux(module, ""))
}

/// Mangle name for static initializer.
///
/// Format: `_init_<mangled_name>`
pub fn mangle_init_name(name: &Name) -> String {
    format!("_init_{}", mangle_name_aux(name, ""))
}

/// Mangle name for constant value.
///
/// Format: `_val_<mangled_name>`
pub fn mangle_const_name(name: &Name) -> String {
    format!("_val_{}", mangle_name_aux(name, ""))
}

#[cfg(test)]
mod tests;
