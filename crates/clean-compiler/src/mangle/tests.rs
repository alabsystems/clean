// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn test_mangle_string_simple() {
    assert_eq!(mangle_string("foo"), "foo");
    assert_eq!(mangle_string("FooBar"), "FooBar");
    assert_eq!(mangle_string("foo123"), "foo123");
}

#[test]
fn test_mangle_string_underscore() {
    // Underscore doubles to avoid collision
    assert_eq!(mangle_string("foo_bar"), "foo__bar");
    assert_eq!(mangle_string("_"), "__");
    assert_eq!(mangle_string("__"), "____");
}

#[test]
fn test_mangle_string_ascii_special() {
    assert_eq!(mangle_string("+"), "_x2b");
    assert_eq!(mangle_string("-"), "_x2d");
    assert_eq!(mangle_string("."), "_x2e");
    assert_eq!(mangle_string("*"), "_x2a");
    assert_eq!(mangle_string("'"), "_x27");
}

#[test]
fn test_mangle_string_unicode() {
    assert_eq!(mangle_string("α"), "_u03b1");
    assert_eq!(mangle_string("β"), "_u03b2");
    assert_eq!(mangle_string("é"), "_xe9");
    // High unicode (emoji, math symbols)
    assert_eq!(mangle_string("𝕊"), "_U0001d54a");
}

#[test]
fn test_mangle_name_simple() {
    assert_eq!(mangle_name(&Name::from_string("foo")), "l_foo");
    assert_eq!(mangle_name(&Name::from_string("Nat")), "l_Nat");
}

#[test]
fn test_mangle_name_dotted() {
    assert_eq!(mangle_name(&Name::from_string("Nat.add")), "l_Nat_add");
    assert_eq!(
        mangle_name(&Name::from_string("List.map.impl")),
        "l_List_map_impl"
    );
}

#[test]
fn test_mangle_name_no_collision() {
    // foo_bar and foo.bar must produce different results
    // foo.bar = Nat.Str("foo").Str("bar") → l_foo_bar
    // foo_bar = Nat.Str("foo_bar") → l_foo__bar (double underscore)
    let foo_bar = Name::from_string("foo_bar");
    let foo_dot_bar = Name::from_string("foo.bar");

    let mangled1 = mangle_name(&foo_bar);
    let mangled2 = mangle_name(&foo_dot_bar);

    assert_ne!(
        mangled1, mangled2,
        "foo_bar and foo.bar must not collide: {} vs {}",
        mangled1, mangled2
    );
}

#[test]
fn test_mangle_name_unicode() {
    // Greek letters - needs disambiguation because _u03b1 looks like escape sequence
    let alpha = Name::from_string("α");
    assert_eq!(mangle_name(&alpha), "l__00_u03b1");

    // Name with unicode component
    let nat_alpha = Name::anon().str("Nat").str("α");
    // After "Nat_", the "_u03b1" needs _00 prefix since it looks like escape
    assert_eq!(mangle_name(&nat_alpha), "l_Nat__00_u03b1");
}

#[test]
fn test_mangle_name_numeric() {
    // Numeric-only name (anonymous parent) - still gets prefix
    let n = Name::anon().num(42);
    assert_eq!(mangle_name(&n), "l_42_");

    // Name with numeric suffix
    let foo_42 = Name::anon().str("foo").num(42);
    assert_eq!(mangle_name(&foo_42), "l_foo_42__");
}

#[test]
fn test_mangle_name_anonymous() {
    assert_eq!(mangle_name(&Name::anon()), "l_");
}

#[test]
fn test_mangle_boxed_name() {
    assert_eq!(mangle_boxed_name("l_foo"), "l_foo___boxed");
    // If ends with __, need disambiguation
    assert_eq!(mangle_boxed_name("l_foo_42__"), "l_foo_42___00__boxed");
}

#[test]
fn test_mangle_module_init() {
    let name = Name::from_string("Init.Data.List");
    assert_eq!(mangle_module_init(&name), "initialize_Init_Data_List");
}

#[test]
fn test_mangle_init_name() {
    let name = Name::from_string("Nat.add");
    assert_eq!(mangle_init_name(&name), "_init_Nat_add");
}

#[test]
fn test_mangle_const_name() {
    let name = Name::from_string("Nat.zero");
    assert_eq!(mangle_const_name(&name), "_val_Nat_zero");
}

#[test]
fn test_disambiguation_underscore_suffix() {
    // If previous component ends with _, next needs _00 prefix
    let name = Name::anon().str("foo_").str("bar");
    let mangled = mangle_name(&name);
    // "foo_" mangles to "foo__", then "bar" needs disambiguation
    assert!(
        mangled.contains("_00"),
        "Expected disambiguation: {}",
        mangled
    );
}

#[test]
fn test_disambiguation_digit_start() {
    // Component starting with digit needs disambiguation
    let name = Name::anon().str("foo").str("123");
    let mangled = mangle_name(&name);
    assert!(
        mangled.contains("_00"),
        "Digit-starting component needs disambiguation: {}",
        mangled
    );
}

#[test]
fn test_check_disambiguation_pattern() {
    assert!(check_disambiguation_pattern("")); // Empty
    assert!(check_disambiguation_pattern("123")); // Starts with digit
    assert!(check_disambiguation_pattern("_x")); // Escape pattern
    assert!(check_disambiguation_pattern("_u")); // Escape pattern
    assert!(check_disambiguation_pattern("_U")); // Escape pattern
    assert!(check_disambiguation_pattern("_1")); // Underscore + digit

    assert!(!check_disambiguation_pattern("foo")); // Normal
    assert!(!check_disambiguation_pattern("_foo")); // Underscore + letter (ok)
}

#[test]
fn test_reserved_word_safety() {
    // C reserved words are safe due to l_ prefix
    let if_name = Name::from_string("if");
    assert_eq!(mangle_name(&if_name), "l_if");

    let while_name = Name::from_string("while");
    assert_eq!(mangle_name(&while_name), "l_while");
}

// ========================================================================
// Collision Resistance Tests (#1037)
// ========================================================================

#[test]
fn test_collision_resistance_string_variants() {
    // Test that string names with similar patterns don't collide
    let names = [
        Name::from_string("foo"),
        Name::from_string("foo_"),
        Name::from_string("_foo"),
        Name::from_string("foo__"),
        Name::from_string("__foo"),
        Name::from_string("foo.bar"),       // Str("foo").Str("bar")
        Name::from_string("foo_bar"),       // Str("foo_bar") - single component
        Name::from_string("foo_.bar"),      // Str("foo_").Str("bar")
        Name::from_string("foo._bar"),      // Str("foo").Str("_bar")
        Name::from_string("foo_x2b"),       // Contains escape-like pattern
        Name::from_string("foo_u03b1"),     // Contains escape-like pattern
        Name::from_string("foo_U00010000"), // Contains escape-like pattern
    ];

    let mangled: Vec<_> = names.iter().map(mangle_name).collect();

    // Check all pairs for collisions
    for (i, m1) in mangled.iter().enumerate() {
        for (j, m2) in mangled.iter().enumerate() {
            if i != j {
                assert_ne!(
                    m1, m2,
                    "Collision detected between {:?} and {:?}: both mangle to {}",
                    names[i], names[j], m1
                );
            }
        }
    }
}

#[test]
fn test_collision_resistance_numeric_variants() {
    // Test that numeric names don't collide
    let names = [
        Name::anon().num(0),
        Name::anon().num(1),
        Name::anon().num(42),
        Name::anon().str("foo").num(0),
        Name::anon().str("foo").num(1),
        Name::anon().str("foo0"),         // String "foo0"
        Name::anon().str("foo").str("0"), // Str("foo").Str("0")
    ];

    let mangled: Vec<_> = names.iter().map(mangle_name).collect();

    for (i, m1) in mangled.iter().enumerate() {
        for (j, m2) in mangled.iter().enumerate() {
            if i != j {
                assert_ne!(
                    m1, m2,
                    "Collision detected between {:?} and {:?}: both mangle to {}",
                    names[i], names[j], m1
                );
            }
        }
    }
}

#[test]
fn test_collision_resistance_unicode_boundary() {
    // Test the 0x10000 boundary (where encoding switches from _u to _U)
    let names = [
        Name::from_string("\u{FFFF}"),     // Last 4-digit unicode
        Name::from_string("\u{10000}"),    // First 8-digit unicode
        Name::from_string("\u{FFFE}"),     // Near boundary
        Name::from_string("\u{10001}"),    // Just past boundary
        Name::from_string("foo\u{FFFF}"),  // Mixed with ASCII
        Name::from_string("foo\u{10000}"), // Mixed with ASCII
    ];

    let mangled: Vec<_> = names.iter().map(mangle_name).collect();

    for (i, m1) in mangled.iter().enumerate() {
        for (j, m2) in mangled.iter().enumerate() {
            if i != j {
                assert_ne!(
                    m1, m2,
                    "Collision detected between {:?} and {:?}: both mangle to {}",
                    names[i], names[j], m1
                );
            }
        }
    }
}

#[test]
fn test_collision_resistance_deeply_nested() {
    // Test deeply nested names - verify nesting depth affects mangling
    // Note: Name::from_string("a.b") parses to Str("a").Str("b")
    let names = [
        Name::from_string("a.b.c.d"),       // 4 components
        Name::from_string("a.b.c_d"),       // 3 components, last is "c_d"
        Name::from_string("a.b_c.d"),       // 3 components, middle is "b_c"
        Name::from_string("a_b.c.d"),       // 3 components, first is "a_b"
        Name::from_string("a_b_c_d"),       // Single component
        Name::anon().str("a_b").str("c_d"), // 2 components
    ];

    let mangled: Vec<_> = names.iter().map(mangle_name).collect();

    for (i, m1) in mangled.iter().enumerate() {
        for (j, m2) in mangled.iter().enumerate() {
            if i != j {
                assert_ne!(
                    m1, m2,
                    "Collision detected between {:?} and {:?}: both mangle to {}",
                    names[i], names[j], m1
                );
            }
        }
    }
}

#[test]
fn test_collision_resistance_escape_patterns() {
    // Test that names containing escape-like patterns don't collide
    // with names that would actually produce those escapes
    let plus = Name::from_string("+"); // Mangles to l__00_x2b (due to _x pattern)
    let fake = Name::from_string("_x2b"); // String "_x2b" mangles to l___x2b (double underscore)

    assert_ne!(
        mangle_name(&plus),
        mangle_name(&fake),
        "'+' and '_x2b' must not collide"
    );

    // Same for unicode escape patterns
    let alpha = Name::from_string("α"); // Mangles to l__00_u03b1
    let fake_u = Name::from_string("_u03b1"); // Mangles to l___u03b1

    assert_ne!(
        mangle_name(&alpha),
        mangle_name(&fake_u),
        "'α' and '_u03b1' must not collide"
    );
}

#[test]
fn test_collision_resistance_c_keywords() {
    // All C reserved words must produce unique manglings
    let c_keywords = [
        "auto",
        "break",
        "case",
        "char",
        "const",
        "continue",
        "default",
        "do",
        "double",
        "else",
        "enum",
        "extern",
        "float",
        "for",
        "goto",
        "if",
        "int",
        "long",
        "register",
        "return",
        "short",
        "signed",
        "sizeof",
        "static",
        "struct",
        "switch",
        "typedef",
        "union",
        "unsigned",
        "void",
        "volatile",
        "while",
        // C99 additions
        "_Bool",
        "_Complex",
        "_Imaginary",
        "inline",
        "restrict",
        // C11 additions
        "_Alignas",
        "_Alignof",
        "_Atomic",
        "_Generic",
        "_Noreturn",
        "_Static_assert",
        "_Thread_local",
    ];

    let names: Vec<_> = c_keywords.iter().map(|s| Name::from_string(s)).collect();
    let mangled: Vec<_> = names.iter().map(mangle_name).collect();

    // All should be prefixed with l_
    for m in &mangled {
        assert!(
            m.starts_with("l_"),
            "All manglings should start with l_: {}",
            m
        );
    }

    // No duplicates
    let mut seen = std::collections::HashSet::new();
    for (i, m) in mangled.iter().enumerate() {
        assert!(
            seen.insert(m),
            "C keyword '{}' produces duplicate mangling: {}",
            c_keywords[i],
            m
        );
    }
}
