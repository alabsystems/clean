// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Stable read-back query for a registered inductive family.
//!
//! `add_inductive` mints the inductive type, its constructors, and the
//! auto-derived recursor (`.rec` / `.casesOn`) into the environment side
//! tables, and `register_structure_fields` records the named field
//! (projection) order for a single-constructor structure. The individual
//! lookups (`get_inductive`, `get_constructor`, `get_recursor`,
//! `get_structure_field_names`) already expose those pieces, but a consumer
//! that wants to *resolve a reflected struct* needs them together: the
//! constructor name to build a value, the field names to resolve `p.field`,
//! and the recursor name to eliminate.
//!
//! [`Environment::inductive_info`] is that single stable read-back. It returns
//! `None` for any name that is not a registered inductive (including
//! constructor / recursor names — resolve those to their inductive first).
//!
//! This is a *read-only* query: it never mutates the environment and performs
//! no checker calls, so it is safe to call repeatedly inside a grounding loop.

use crate::inductive::InductiveVal;
use crate::name::Name;

use super::Environment;

/// A consolidated, read-only view of one registered inductive type — exactly
/// the data a consumer needs to resolve a reflected struct/enum to its real
/// Clean inductive: the constructor name(s), the named-projection order, and
/// the recursor / `casesOn` names the kernel auto-derived.
///
/// All names are owned clones (the underlying side tables stay borrowed-free),
/// so the result outlives any later `&mut Environment` use.
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub struct InductiveInfo {
    /// The inductive type's name (e.g. `Trust.Adt.Wrapper`).
    pub name: Name,
    /// Number of parameters (the shared prefix in the type and constructors).
    pub num_params: u32,
    /// Number of indices (arguments after the parameters).
    pub num_indices: u32,
    /// Constructor names, in declaration order (e.g. `[Wrapper.mk]`).
    pub constructor_names: Vec<Name>,
    /// Named field (projection) order for a registered structure, if any.
    ///
    /// Present iff the inductive was registered as a structure via
    /// [`Environment::register_structure_fields`] (single constructor with
    /// named fields). For a one-constructor struct `Wrapper { value : Int }`
    /// this is `[value]`, so `p.value` resolves to field index 0. `None` when
    /// no field names were registered (e.g. a multi-constructor enum, or a
    /// structure whose fields were never named).
    pub field_names: Option<Vec<Name>>,
    /// The auto-derived recursor name (`<name>.rec`), if present.
    pub recursor_name: Option<Name>,
    /// The auto-derived case-analysis eliminator name (`<name>.casesOn`), if
    /// present.
    pub cases_on_name: Option<Name>,
    /// Whether the inductive is recursive.
    pub is_recursive: bool,
}

impl InductiveInfo {
    /// The single constructor name, iff this inductive has exactly one
    /// constructor (i.e. it is a structure / record shape). `None` for an
    /// enum with zero or multiple constructors.
    #[must_use]
    pub fn sole_constructor(&self) -> Option<&Name> {
        match self.constructor_names.as_slice() {
            [only] => Some(only),
            _ => None,
        }
    }

    /// The field index of a named projection, iff a field list was registered
    /// and `field` is one of its names.
    #[must_use]
    pub fn field_index(&self, field: &Name) -> Option<u32> {
        let fields = self.field_names.as_ref()?;
        fields
            .iter()
            .position(|f| f == field)
            .and_then(|p| u32::try_from(p).ok())
    }
}

impl Environment {
    /// Read back a consolidated [`InductiveInfo`] for a registered inductive.
    ///
    /// `add_inductive` already mints the type, constructors, and recursor; this
    /// stitches their names together with the structure field order so a single
    /// call gives a consumer everything needed to resolve a reflected
    /// struct/enum (build with the constructor, project a field, eliminate with
    /// the recursor).
    ///
    /// # Returns
    /// - `Some(InductiveInfo)` when `name` is a declared inductive type.
    /// - `None` otherwise — including constructor / recursor names (resolve
    ///   those to their inductive first via [`Self::get_constructor`] /
    ///   [`Self::get_recursor`]).
    ///
    /// This is read-only: it never mutates the environment and makes no checker
    /// calls.
    ///
    /// ENSURES: Returns a value consistent with the function's documented semantics.
    /// REQUIRES: none
    #[must_use]
    pub fn inductive_info(&self, name: &Name) -> Option<InductiveInfo> {
        let ind: &InductiveVal = self.get_inductive(name)?;

        let rec_name = Name::append(name, "rec");
        let recursor_name = self.get_recursor(&rec_name).map(|_| rec_name);

        let cases_name = Name::append(name, "casesOn");
        let cases_on_name = self.get_recursor(&cases_name).map(|_| cases_name);

        let field_names = self.get_structure_field_names(name).map(<[Name]>::to_vec);

        Some(InductiveInfo {
            name: ind.name.clone(),
            num_params: ind.num_params,
            num_indices: ind.num_indices,
            constructor_names: ind.constructor_names.clone(),
            field_names,
            recursor_name,
            cases_on_name,
            is_recursive: ind.is_recursive,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::expr::Expr;
    use crate::inductive::{Constructor, InductiveDecl, InductiveType};

    /// Build a one-constructor structure `Wrapper { value : Int }` as an
    /// inductive: `Wrapper : Type`, `Wrapper.mk : Int -> Wrapper`.
    fn wrapper_decl() -> InductiveDecl {
        let wrapper = Name::from_string("Wrapper");
        let int_ty = Expr::const_(Name::from_string("Int"), crate::expr::LevelVec::new());
        InductiveDecl {
            level_params: vec![],
            num_params: 0,
            types: vec![InductiveType {
                name: wrapper.clone(),
                type_: Expr::type_(),
                constructors: vec![Constructor {
                    name: Name::from_string("Wrapper.mk"),
                    // Int -> Wrapper
                    type_: Expr::pi(
                        crate::expr::BinderData::default(),
                        int_ty,
                        Expr::const_(wrapper, crate::expr::LevelVec::new()),
                    ),
                }],
            }],
        }
    }

    /// Register a 1-constructor inductive and read back its constructor,
    /// projection, and recursor names through the new stable query.
    #[test]
    fn inductive_info_reads_back_ctor_projection_and_recursor() {
        let mut env = Environment::with_prelude();
        // `Int` must exist for the constructor type to check.
        assert!(env.get_inductive(&Name::from_string("Int")).is_some());

        env.add_inductive(wrapper_decl())
            .expect("Wrapper inductive registers");
        env.register_structure_fields(
            Name::from_string("Wrapper"),
            vec![Name::from_string("value")],
        )
        .expect("structure fields register");

        let info = env
            .inductive_info(&Name::from_string("Wrapper"))
            .expect("Wrapper is a registered inductive");

        // Constructor read-back.
        assert_eq!(
            info.constructor_names,
            vec![Name::from_string("Wrapper.mk")]
        );
        assert_eq!(
            info.sole_constructor(),
            Some(&Name::from_string("Wrapper.mk"))
        );

        // Projection (named field) read-back.
        assert_eq!(info.field_names, Some(vec![Name::from_string("value")]));
        assert_eq!(info.field_index(&Name::from_string("value")), Some(0));
        assert_eq!(info.field_index(&Name::from_string("nope")), None);

        // Recursor read-back: `add_inductive` auto-derives `Wrapper.rec` and
        // `Wrapper.casesOn`.
        assert_eq!(info.recursor_name, Some(Name::from_string("Wrapper.rec")));
        assert_eq!(
            info.cases_on_name,
            Some(Name::from_string("Wrapper.casesOn"))
        );
        assert!(!info.is_recursive);
    }

    /// A name that is not an inductive (a constructor name, an undeclared name)
    /// reads back `None` — the query is closed.
    #[test]
    fn inductive_info_is_none_for_non_inductive_names() {
        let mut env = Environment::with_prelude();
        env.add_inductive(wrapper_decl())
            .expect("Wrapper inductive registers");

        // The constructor itself is not an inductive.
        assert!(env
            .inductive_info(&Name::from_string("Wrapper.mk"))
            .is_none());
        // The recursor is not an inductive.
        assert!(env
            .inductive_info(&Name::from_string("Wrapper.rec"))
            .is_none());
        // An undeclared name.
        assert!(env
            .inductive_info(&Name::from_string("Nonexistent"))
            .is_none());
    }
}
