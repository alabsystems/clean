// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `variant_shape!` — the payload-free `Copy` projection of a data-carrying
//! enum, generated from ONE variant list.
//!
//! A decision table over `&Inst` / `&ObligationKind` / `&ProofEvidence` cannot
//! be a proved Trust contract: the verified lane leaves a discriminant read
//! through a reference UNKNOWN (measured 2026-09-29, `trust-ir-laws` crate
//! docs). The table is therefore stated over the variant's SHAPE — a fieldless
//! `Copy` enum with the same variant names — and the by-reference API
//! delegates to it (`Inst::is_terminator` is `self.shape().is_terminator()`).
//!
//! The projection itself is TYPE-LEVEL, not proved: the macro writes the shape
//! enum and the `shape()` match from the same list, with no wildcard arm, so
//!
//! * a variant of the data enum missing from the list is a non-exhaustive
//!   match (rustc refuses the crate);
//! * a list entry naming no variant of the data enum is an unresolved path;
//! * a duplicate entry is a duplicate enum variant;
//!
//! and the projection is a bijection on variant names by construction. The
//! `Enum::Variant { .. }` pattern is legal for struct, tuple and unit
//! variants alike, so the list carries names only.

/// Generate `$shape`, a fieldless `Copy` enum with exactly the listed
/// variants, plus `$data::shape(&self) -> $shape`, `$shape::ALL` (every shape
/// in list order) and `$shape::name(self)` (the variant's identifier).
///
/// See the module docs for why the projection cannot drift from `$data`.
macro_rules! variant_shape {
    (
        $(#[$meta:meta])*
        $vis:vis enum $shape:ident for $data:ident {
            $($variant:ident),+ $(,)?
        }
    ) => {
        $(#[$meta])*
        #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
        $vis enum $shape {
            $(
                #[doc = concat!("The shape of [`", stringify!($data), "::", stringify!($variant), "`].")]
                $variant,
            )+
        }

        impl $shape {
            /// Every shape, in the declaration order of the data enum's
            /// variants.
            pub const ALL: &'static [$shape] = &[$($shape::$variant),+];

            /// The variant's identifier, spelled exactly as in the data enum.
            #[must_use]
            pub const fn name(self) -> &'static str {
                match self {
                    $($shape::$variant => stringify!($variant),)+
                }
            }
        }

        impl $data {
            #[doc = concat!(
                "The payload-free shape of this value: its variant, as a `Copy` [`",
                stringify!($shape),
                "`]. Exhaustive with no wildcard arm, generated from the same list as the \
                 shape enum (see `variant_shape!`), so it cannot drift."
            )]
            #[inline]
            #[must_use]
            pub const fn shape(&self) -> $shape {
                match self {
                    $($data::$variant { .. } => $shape::$variant,)+
                }
            }
        }
    };
}
