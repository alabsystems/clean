// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Semantic token classification — maps parser tokens and identifiers to
//! LSP semantic token types and modifier bitsets.

use super::modifier_bits;
use crate::document::CommandKind;
use clean_parser::lexer::TokenKind;
use std::collections::HashMap;

/// Map a parser TokenKind to a semantic token type index
/// Returns None for tokens that shouldn't be highlighted semantically
pub(crate) fn token_kind_to_semantic_type(kind: &TokenKind) -> Option<u32> {
    match kind {
        // Keywords (index 0)
        TokenKind::Def
        | TokenKind::Theorem
        | TokenKind::Lemma
        | TokenKind::Axiom
        | TokenKind::Example
        | TokenKind::Let
        | TokenKind::In
        | TokenKind::Fun
        | TokenKind::Forall
        | TokenKind::If
        | TokenKind::Then
        | TokenKind::Else
        | TokenKind::Match
        | TokenKind::With
        | TokenKind::Where
        | TokenKind::Do
        | TokenKind::Return
        | TokenKind::Structure
        | TokenKind::Class
        | TokenKind::Instance
        | TokenKind::Inductive
        | TokenKind::Deriving
        | TokenKind::Namespace
        | TokenKind::Section
        | TokenKind::End
        | TokenKind::Open
        | TokenKind::Variable
        | TokenKind::Universe
        | TokenKind::Import
        | TokenKind::Mutual
        | TokenKind::SetOption
        | TokenKind::By
        | TokenKind::Have
        | TokenKind::Show
        | TokenKind::Suffices
        | TokenKind::From
        | TokenKind::Rfl
        | TokenKind::Sorry
        | TokenKind::Extends
        | TokenKind::Private
        | TokenKind::Protected
        | TokenKind::Partial
        | TokenKind::Unsafe
        | TokenKind::Noncomputable
        | TokenKind::Abbrev
        | TokenKind::Attribute
        | TokenKind::Syntax
        | TokenKind::Macro
        | TokenKind::MacroRules
        | TokenKind::Elab
        | TokenKind::Infixl
        | TokenKind::Infixr
        | TokenKind::Prefix
        | TokenKind::Postfix
        | TokenKind::Notation
        | TokenKind::Scoped => Some(0), // KEYWORD

        // Types (index 1)
        TokenKind::Type | TokenKind::Prop | TokenKind::Sort => Some(1), // TYPE

        // Numbers (index 4)
        TokenKind::NatLit(_) => Some(4), // NUMBER

        // Strings (index 5)
        TokenKind::StringLit(_) => Some(5), // STRING

        // Operators (index 7)
        TokenKind::Arrow
        | TokenKind::FatArrow
        | TokenKind::Lambda
        | TokenKind::Eq
        | TokenKind::DoubleEq
        | TokenKind::Ne
        | TokenKind::Lt
        | TokenKind::Le
        | TokenKind::Gt
        | TokenKind::Ge
        | TokenKind::Plus
        | TokenKind::Minus
        | TokenKind::Star
        | TokenKind::Slash
        | TokenKind::Percent
        | TokenKind::Caret
        | TokenKind::And
        | TokenKind::Or
        | TokenKind::Not
        | TokenKind::Tilde
        | TokenKind::Bind
        | TokenKind::Seq
        | TokenKind::AndThen
        | TokenKind::OrElse
        | TokenKind::Pipe
        | TokenKind::BackwardPipe
        | TokenKind::ColonColon
        | TokenKind::Dollar
        | TokenKind::DollarArrow
        | TokenKind::LeftDollar
        | TokenKind::LeftDollarArrow
        | TokenKind::HEq
        | TokenKind::Equiv
        | TokenKind::Iff
        | TokenKind::Times
        | TokenKind::LeftArrow
        | TokenKind::Exists
        | TokenKind::Elem
        | TokenKind::NotElem
        | TokenKind::Subset
        | TokenKind::ProperSubset
        | TokenKind::Inter
        | TokenKind::Union
        | TokenKind::Top
        | TokenKind::Bot
        | TokenKind::Compose
        | TokenKind::Cdot => Some(7), // OPERATOR

        // Identifiers could be functions, variables, etc.
        // For now, we mark them as VARIABLE (index 3)
        // A more sophisticated implementation would look up the identifier
        // in the environment to determine if it's a function, type, etc.
        TokenKind::Ident(_) => Some(3), // VARIABLE

        // Delimiters, punctuation, and other tokens don't need semantic highlighting
        _ => None,
    }
}

/// Find the byte span of the definition name within a command
/// Returns (start, end) byte offsets if found
pub(crate) fn find_definition_name_span(
    text: &str,
    cmd_start: usize,
    cmd_end: usize,
    name: &str,
) -> Option<(usize, usize)> {
    if cmd_start >= text.len() || cmd_end > text.len() || cmd_start >= cmd_end {
        return None;
    }
    let cmd_text = &text[cmd_start..cmd_end];

    let mut search_start = 0;
    while let Some(found) = cmd_text.get(search_start..)?.find(name) {
        let pos = search_start + found;
        let end_pos = pos + name.len();
        let is_start_boundary = pos == 0
            || !cmd_text[..pos]
                .chars()
                .next_back()
                .is_some_and(is_identifier_continue);
        let is_end_boundary = end_pos >= cmd_text.len()
            || !cmd_text[end_pos..]
                .chars()
                .next()
                .is_some_and(is_identifier_continue);

        if is_start_boundary && is_end_boundary {
            return Some((cmd_start + pos, cmd_start + end_pos));
        }

        search_start = end_pos;
    }

    None
}

fn is_identifier_continue(ch: char) -> bool {
    ch.is_alphanumeric() || ch == '_' || ch == '\'' || ch == '.'
}

/// Classify an identifier and compute modifiers
/// Returns (token_type, modifiers_bitset)
pub(crate) fn classify_identifier_with_modifiers(
    name: &str,
    definition_kinds: &HashMap<String, CommandKind>,
    is_definition_site: bool,
) -> (Option<u32>, u32) {
    let mut modifiers = 0u32;

    // Check if this is a definition site
    if is_definition_site {
        modifiers |= modifier_bits::DECLARATION;
        modifiers |= modifier_bits::DEFINITION;
    }

    // Check if identifier is a known definition
    if let Some(kind) = definition_kinds.get(name) {
        return (Some(command_kind_to_semantic_type(kind)), modifiers);
    }

    // Check for built-in types (they get DEFAULT_LIBRARY modifier)
    if is_builtin_type(name) {
        modifiers |= modifier_bits::DEFAULT_LIBRARY;
        return (Some(1), modifiers); // TYPE
    }

    // Check for common type names (capitalized identifiers often are types)
    if is_likely_type_name(name) {
        return (Some(1), modifiers); // TYPE
    }

    // Default: VARIABLE (local variables are readonly in Lean - immutable bindings)
    modifiers |= modifier_bits::READONLY;
    (Some(3), modifiers)
}

/// Check if a name is a built-in type from the standard library
pub(crate) fn is_builtin_type(name: &str) -> bool {
    const BUILTIN_TYPES: &[&str] = &[
        // Core types
        "Nat",
        "Int",
        "Bool",
        "String",
        "Char",
        "Float",
        "Unit",
        "Empty",
        "True",
        "False",
        "Prop",
        "Type",
        "Sort",
        // Collections
        "List",
        "Array",
        "Option",
        "Sum",
        "Prod",
        "Fin",
        "Subtype",
        // Numeric types
        "UInt8",
        "UInt16",
        "UInt32",
        "UInt64",
        "USize",
        "Int8",
        "Int16",
        "Int32",
        "Int64",
        // Monads and transformers
        "IO",
        "Except",
        "EStateM",
        "StateT",
        "ReaderT",
        "ExceptT",
        "OptionT",
        "StateM",
        "ReaderM",
        "ExceptM",
        "Id",
        // Other common types
        "Decidable",
        "DecidableEq",
        "BEq",
        "Hashable",
        "Repr",
        "ToString",
        "Inhabited",
        "Nonempty",
        "Functor",
        "Monad",
        "Applicative",
    ];
    BUILTIN_TYPES.contains(&name)
}

/// Map CommandKind to semantic token type index
pub(crate) fn command_kind_to_semantic_type(kind: &CommandKind) -> u32 {
    match kind {
        // Functions (theorems, lemmas, definitions, axioms produce terms)
        CommandKind::Definition
        | CommandKind::Theorem
        | CommandKind::Lemma
        | CommandKind::Axiom
        | CommandKind::Example => 2, // FUNCTION

        // Types (inductive/coinductive types, structures)
        CommandKind::Inductive | CommandKind::Coinductive | CommandKind::Structure => 1, // TYPE

        // Classes
        CommandKind::Class => 9, // CLASS

        // Instances (like properties/methods)
        CommandKind::Instance => 10, // PROPERTY

        // Namespaces
        CommandKind::Namespace => 8, // NAMESPACE

        // Variables, universes, and everything else default to variable
        CommandKind::Variable
        | CommandKind::Universe
        | CommandKind::Import
        | CommandKind::Open
        | CommandKind::Section
        | CommandKind::End
        | CommandKind::Other(_) => 3, // VARIABLE
    }
}

/// Heuristic: check if a name is likely a type name
/// In Lean, type names typically start with an uppercase letter
pub(crate) fn is_likely_type_name(name: &str) -> bool {
    // Common built-in types
    const BUILTIN_TYPES: &[&str] = &[
        "Nat", "Int", "Bool", "String", "Char", "Float", "Unit", "Empty", "True", "False", "List",
        "Array", "Option", "Sum", "Prod", "Fin", "UInt8", "UInt16", "UInt32", "UInt64", "USize",
        "IO", "Except", "EStateM", "StateT", "ReaderT", "ExceptT", "OptionT",
    ];

    if BUILTIN_TYPES.contains(&name) {
        return true;
    }

    // Identifiers starting with uppercase are often types (but not always)
    // Only apply this heuristic for simple identifiers without dots
    if !name.contains('.') {
        if let Some(first_char) = name.chars().next() {
            return first_char.is_uppercase();
        }
    }

    false
}
