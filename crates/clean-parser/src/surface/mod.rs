// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Surface syntax AST
//!
//! The AST produced by the parser, before elaboration.
//! Named bindings, optional type annotations, no de Bruijn indices.

mod attr;
mod binder;
mod decl;
mod expr;
mod guard_msgs;
pub mod modifiers;
mod name;
pub use modifiers::*;
mod span;
mod syntax;
mod template_hygiene;

pub use attr::*;
pub use binder::*;
pub use decl::*;
pub use expr::*;
pub use guard_msgs::*;
pub use name::*;
pub use span::*;
pub use syntax::*;
pub use template_hygiene::{
    instantiate_notation_template, instantiate_tactic_template,
    instantiate_unhygienic_notation_template, mark_template_free_references,
    template_free_reference_spellings, TemplateRefusal,
};

// Tactic surface syntax types are in crate::surface_tactic, re-exported here
// for backward compatibility so that `use crate::surface::SurfaceTactic` etc. still works.
pub use crate::surface_tactic::*;
pub use crate::surface_tactic_types::*;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_surface_expr_construction() {
        let id = SurfaceExpr::ident("x");
        assert!(
            matches!(id, SurfaceExpr::Ident(_, s) if (s).name() == SurfaceName::generated_path("x").name())
        );

        let ty = SurfaceExpr::type_();
        assert!(matches!(ty, SurfaceExpr::Universe(_, UniverseExpr::Type)));

        let prop = SurfaceExpr::prop();
        assert!(matches!(prop, SurfaceExpr::Universe(_, UniverseExpr::Prop)));
    }

    #[test]
    fn test_span_merge() {
        let s1 = Span::new(0, 5);
        let s2 = Span::new(10, 20);
        let merged = s1.merge(s2);
        assert_eq!(merged.start, 0);
        assert_eq!(merged.end, 20);
    }

    #[test]
    fn test_binder_construction() {
        let b = SurfaceBinder::explicit("x", SurfaceExpr::type_());
        assert_eq!((b.name).name(), SurfaceName::generated_path("x").name());
        assert!(b.ty.is_some(), "explicit binder should have a type");
        assert_eq!(b.info, SurfaceBinderInfo::Explicit);

        let b = SurfaceBinder::implicit("y", SurfaceExpr::prop());
        assert_eq!(b.info, SurfaceBinderInfo::Implicit);
    }
}
