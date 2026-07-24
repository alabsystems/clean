// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Built-in attribute macro implementations.
//!
//! Provides concrete [`AttrMacro`] implementations for all standard Lean 5
//! attributes (`@[simp]`, `@[ext]`, `@[inline]`, `@[reducible]`, etc.) and
//! the [`register_builtins`] function that populates an [`AttrMacroRegistry`].

use clean_kernel::Name;
use clean_parser::Attribute;

use crate::error::ElabError;

use super::{
    AttrMacro, AttrMacroRegistry, AttrMacroResult, InlineKind, ReducibilityLevel, SpecializeKind,
};

/// Default priority for built-in attribute macros.
const BUILTIN_PRIORITY: u32 = 100;

/// Reducibility macros run before other macros (affects elaboration behavior).
const REDUCIBILITY_PRIORITY: u32 = 50;

/// Inline macros run at normal priority.
const INLINE_PRIORITY: u32 = 100;

// ============================================================================
// Tactic / lemma registration macros
// ============================================================================

pub(crate) struct SimpAttrMacro;
impl AttrMacro for SimpAttrMacro {
    fn expand(&self, _decl_name: &Name, attr: &Attribute) -> Result<AttrMacroResult, ElabError> {
        let priority = match attr {
            Attribute::Simp { priority } => priority.map(|p| match p {
                clean_parser::SimpPriority::Low => 500,
                clean_parser::SimpPriority::Normal => 1000,
                clean_parser::SimpPriority::High => 1500,
            }),
            _ => None,
        };
        Ok(AttrMacroResult::RegisterSimpLemma { priority })
    }
}

pub(crate) struct ExtAttrMacro;
impl AttrMacro for ExtAttrMacro {
    fn expand(&self, _decl_name: &Name, _attr: &Attribute) -> Result<AttrMacroResult, ElabError> {
        Ok(AttrMacroResult::RegisterExtLemma)
    }
}

pub(crate) struct CongrAttrMacro;
impl AttrMacro for CongrAttrMacro {
    fn expand(&self, _decl_name: &Name, _attr: &Attribute) -> Result<AttrMacroResult, ElabError> {
        Ok(AttrMacroResult::RegisterCongrLemma)
    }
}

pub(crate) struct ReflAttrMacro;
impl AttrMacro for ReflAttrMacro {
    fn expand(&self, _decl_name: &Name, _attr: &Attribute) -> Result<AttrMacroResult, ElabError> {
        Ok(AttrMacroResult::RegisterReflLemma)
    }
}

pub(crate) struct SymmAttrMacro;
impl AttrMacro for SymmAttrMacro {
    fn expand(&self, _decl_name: &Name, _attr: &Attribute) -> Result<AttrMacroResult, ElabError> {
        Ok(AttrMacroResult::RegisterSymmLemma)
    }
}

pub(crate) struct CsimpAttrMacro;
impl AttrMacro for CsimpAttrMacro {
    fn expand(&self, _decl_name: &Name, _attr: &Attribute) -> Result<AttrMacroResult, ElabError> {
        Ok(AttrMacroResult::RegisterCsimpLemma)
    }
}

// ============================================================================
// Reducibility macros
// ============================================================================

pub(crate) struct ReducibleAttrMacro;
impl AttrMacro for ReducibleAttrMacro {
    fn expand(&self, _decl_name: &Name, _attr: &Attribute) -> Result<AttrMacroResult, ElabError> {
        Ok(AttrMacroResult::SetReducibility(
            ReducibilityLevel::Reducible,
        ))
    }
}

pub(crate) struct SemireducibleAttrMacro;
impl AttrMacro for SemireducibleAttrMacro {
    fn expand(&self, _decl_name: &Name, _attr: &Attribute) -> Result<AttrMacroResult, ElabError> {
        Ok(AttrMacroResult::SetReducibility(
            ReducibilityLevel::Semireducible,
        ))
    }
}

pub(crate) struct IrreducibleAttrMacro;
impl AttrMacro for IrreducibleAttrMacro {
    fn expand(&self, _decl_name: &Name, _attr: &Attribute) -> Result<AttrMacroResult, ElabError> {
        Ok(AttrMacroResult::SetReducibility(
            ReducibilityLevel::Irreducible,
        ))
    }
}

// ============================================================================
// Inline / specialize macros
// ============================================================================

pub(crate) struct InlineAttrMacro {
    pub(crate) kind: InlineKind,
}
impl AttrMacro for InlineAttrMacro {
    fn expand(&self, _decl_name: &Name, _attr: &Attribute) -> Result<AttrMacroResult, ElabError> {
        Ok(AttrMacroResult::SetInline(self.kind))
    }
}

pub(crate) struct SpecializeAttrMacro {
    pub(crate) kind: SpecializeKind,
}
impl AttrMacro for SpecializeAttrMacro {
    fn expand(&self, _decl_name: &Name, _attr: &Attribute) -> Result<AttrMacroResult, ElabError> {
        Ok(AttrMacroResult::SetSpecialize(self.kind))
    }
}

// ============================================================================
// FFI macros
// ============================================================================

pub(crate) struct ExternAttrMacro;
impl AttrMacro for ExternAttrMacro {
    fn expand(&self, _decl_name: &Name, attr: &Attribute) -> Result<AttrMacroResult, ElabError> {
        match attr {
            Attribute::Extern(name) => Ok(AttrMacroResult::RegisterExtern {
                extern_name: name.clone(),
            }),
            _ => Err(ElabError::Unsupported {
                feature: "extern attribute requires a string argument".to_owned(),
            }),
        }
    }
}

pub(crate) struct ExportAttrMacro;
impl AttrMacro for ExportAttrMacro {
    fn expand(&self, _decl_name: &Name, attr: &Attribute) -> Result<AttrMacroResult, ElabError> {
        match attr {
            Attribute::Export(name) => Ok(AttrMacroResult::RegisterExport {
                export_name: name.clone(),
            }),
            _ => Err(ElabError::Unsupported {
                feature: "export attribute requires a string argument".to_owned(),
            }),
        }
    }
}

pub(crate) struct ImplementedByAttrMacro;
impl AttrMacro for ImplementedByAttrMacro {
    fn expand(&self, _decl_name: &Name, attr: &Attribute) -> Result<AttrMacroResult, ElabError> {
        match attr {
            Attribute::ImplementedBy(name) => Ok(AttrMacroResult::RegisterImplementedBy {
                impl_name: name.clone(),
            }),
            _ => Err(ElabError::Unsupported {
                feature: "implementedBy attribute requires a name argument".to_owned(),
            }),
        }
    }
}

// ============================================================================
// Other built-in macros
// ============================================================================

pub(crate) struct DeprecatedAttrMacro;
impl AttrMacro for DeprecatedAttrMacro {
    fn expand(&self, _decl_name: &Name, attr: &Attribute) -> Result<AttrMacroResult, ElabError> {
        let message = match attr {
            Attribute::Deprecated(msg) => msg.clone(),
            _ => None,
        };
        Ok(AttrMacroResult::RegisterDeprecated { message })
    }
}

pub(crate) struct CoeAttrMacro;
impl AttrMacro for CoeAttrMacro {
    fn expand(&self, _decl_name: &Name, _attr: &Attribute) -> Result<AttrMacroResult, ElabError> {
        Ok(AttrMacroResult::RegisterCoercion)
    }
}

pub(crate) struct MatchPatternAttrMacro;
impl AttrMacro for MatchPatternAttrMacro {
    fn expand(&self, _decl_name: &Name, _attr: &Attribute) -> Result<AttrMacroResult, ElabError> {
        Ok(AttrMacroResult::RegisterMatchPattern)
    }
}

pub(crate) struct ClassAttrMacro;
impl AttrMacro for ClassAttrMacro {
    fn expand(&self, _decl_name: &Name, _attr: &Attribute) -> Result<AttrMacroResult, ElabError> {
        Ok(AttrMacroResult::RegisterClass)
    }
}

pub(crate) struct InitAttrMacro;
impl AttrMacro for InitAttrMacro {
    fn expand(&self, _decl_name: &Name, _attr: &Attribute) -> Result<AttrMacroResult, ElabError> {
        Ok(AttrMacroResult::RegisterInit)
    }
}

pub(crate) struct InstanceAttrMacro;
impl AttrMacro for InstanceAttrMacro {
    fn expand(&self, _decl_name: &Name, attr: &Attribute) -> Result<AttrMacroResult, ElabError> {
        let priority = match attr {
            Attribute::InstancePriority(p) => *p,
            _ => 1000, // default instance priority
        };
        Ok(AttrMacroResult::RegisterInstance { priority })
    }
}

pub(crate) struct DefaultInstanceAttrMacro;
impl AttrMacro for DefaultInstanceAttrMacro {
    fn expand(&self, _decl_name: &Name, _attr: &Attribute) -> Result<AttrMacroResult, ElabError> {
        Ok(AttrMacroResult::RegisterDefaultInstance)
    }
}

// ============================================================================
// Registration
// ============================================================================

/// Register all built-in attribute macros into the given registry.
pub(crate) fn register_builtins(registry: &mut AttrMacroRegistry) {
    let builtins: Vec<(&str, u32, Box<dyn AttrMacro>)> = vec![
        // Tactic/lemma registration
        ("simp", BUILTIN_PRIORITY, Box::new(SimpAttrMacro)),
        ("ext", BUILTIN_PRIORITY, Box::new(ExtAttrMacro)),
        ("congr", BUILTIN_PRIORITY, Box::new(CongrAttrMacro)),
        ("refl", BUILTIN_PRIORITY, Box::new(ReflAttrMacro)),
        ("symm", BUILTIN_PRIORITY, Box::new(SymmAttrMacro)),
        ("csimp", BUILTIN_PRIORITY, Box::new(CsimpAttrMacro)),
        // Reducibility (higher priority — affects elaboration)
        (
            "reducible",
            REDUCIBILITY_PRIORITY,
            Box::new(ReducibleAttrMacro),
        ),
        (
            "semireducible",
            REDUCIBILITY_PRIORITY,
            Box::new(SemireducibleAttrMacro),
        ),
        (
            "irreducible",
            REDUCIBILITY_PRIORITY,
            Box::new(IrreducibleAttrMacro),
        ),
        // Inlining
        (
            "inline",
            INLINE_PRIORITY,
            Box::new(InlineAttrMacro {
                kind: InlineKind::Inline,
            }),
        ),
        (
            "always_inline",
            INLINE_PRIORITY,
            Box::new(InlineAttrMacro {
                kind: InlineKind::AlwaysInline,
            }),
        ),
        (
            "noinline",
            INLINE_PRIORITY,
            Box::new(InlineAttrMacro {
                kind: InlineKind::Noinline,
            }),
        ),
        (
            "macro_inline",
            INLINE_PRIORITY,
            Box::new(InlineAttrMacro {
                kind: InlineKind::MacroInline,
            }),
        ),
        (
            "inline_if_reduce",
            INLINE_PRIORITY,
            Box::new(InlineAttrMacro {
                kind: InlineKind::InlineIfReduce,
            }),
        ),
        // Specialization
        (
            "specialize",
            INLINE_PRIORITY,
            Box::new(SpecializeAttrMacro {
                kind: SpecializeKind::Specialize,
            }),
        ),
        (
            "nospecialize",
            INLINE_PRIORITY,
            Box::new(SpecializeAttrMacro {
                kind: SpecializeKind::Nospecialize,
            }),
        ),
        // FFI
        ("extern", BUILTIN_PRIORITY, Box::new(ExternAttrMacro)),
        ("export", BUILTIN_PRIORITY, Box::new(ExportAttrMacro)),
        (
            "implementedBy",
            BUILTIN_PRIORITY,
            Box::new(ImplementedByAttrMacro),
        ),
        // Other
        (
            "deprecated",
            BUILTIN_PRIORITY,
            Box::new(DeprecatedAttrMacro),
        ),
        ("coe", BUILTIN_PRIORITY, Box::new(CoeAttrMacro)),
        (
            "match_pattern",
            BUILTIN_PRIORITY,
            Box::new(MatchPatternAttrMacro),
        ),
        ("class", BUILTIN_PRIORITY, Box::new(ClassAttrMacro)),
        ("init", BUILTIN_PRIORITY, Box::new(InitAttrMacro)),
        ("instance", BUILTIN_PRIORITY, Box::new(InstanceAttrMacro)),
        (
            "default_instance",
            BUILTIN_PRIORITY,
            Box::new(DefaultInstanceAttrMacro),
        ),
    ];

    for (name, priority, handler) in builtins {
        registry
            .register(name, priority, handler)
            .expect("invariant: builtin names are unique");
    }
}
