// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Source-language releases known to this build. Artifact identities and their
//! admission states remain measured by `clean-olean`'s world registry.

/// A known Lean source language, not a claim of whole-language compatibility.
/// Unknown releases cannot inherit a previous release's feature decisions.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub enum LeanWorld {
    /// The historical 4.8 frontend.
    Lean408,
    /// Historical readable artifacts.
    Lean413,
    /// Historical readable artifacts.
    Lean426,
    /// The unchanged oracle and default source language.
    #[default]
    Lean430Rc2,
    /// Explicitly selected measured artifacts.
    Lean435,
    /// Explicitly selected measured artifacts and variable visibility syntax.
    Lean436Rc2,
    /// Stable Lean 4.36.0, explicitly selected with matching artifacts.
    Lean436,
}

/// A world's state (R38).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LeanWorldState {
    /// The authority: the `lean-toolchain` pin. Exactly one row.
    Oracle,
    /// Readable, with no new claims.
    Historical,
    /// v4.8.0, for M1 under OD4's built-in prelude.
    FrontendOnly,
    /// Readable only by an environment that declared it.
    Measured,
    /// Seen only by format canaries: its `.olean` files are refused by name.
    Canary,
}

impl LeanWorldState {
    /// The `lean_worlds.tsv` spelling.
    pub const fn label(self) -> &'static str {
        match self {
            Self::Oracle => "oracle",
            Self::Historical => "historical",
            Self::FrontendOnly => "frontend-only",
            Self::Measured => "measured",
            Self::Canary => "canary",
        }
    }

    /// Whether a part of a world in this state loads into an environment
    /// that has declared no world.
    pub const fn implicit(self) -> bool {
        matches!(self, Self::Oracle | Self::Historical | Self::FrontendOnly)
    }
}

/// A source release this build has no feature decision for.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[error("unsupported Lean world `{0}`")]
pub struct UnknownLeanWorld(pub String);

impl LeanWorld {
    /// Every release with an explicit source-language decision.
    pub const ALL: [Self; 7] = [
        Self::Lean408,
        Self::Lean413,
        Self::Lean426,
        Self::Lean430Rc2,
        Self::Lean435,
        Self::Lean436Rc2,
        Self::Lean436,
    ];

    /// The oracle stays at the repository's Lean 4.30 release candidate.
    pub const ORACLE: Self = Self::Lean430Rc2;

    /// The canonical `lean-toolchain` tag.
    #[must_use]
    pub const fn tag(self) -> &'static str {
        match self {
            Self::Lean408 => "v4.8.0",
            Self::Lean413 => "v4.13.0",
            Self::Lean426 => "v4.26.0",
            Self::Lean430Rc2 => "v4.30.0-rc2",
            Self::Lean435 => "v4.35.0",
            Self::Lean436Rc2 => "v4.36.0-rc2",
            Self::Lean436 => "v4.36.0",
        }
    }

    /// Version without the toolchain tag's leading `v`.
    #[must_use]
    pub const fn version(self) -> &'static str {
        self.tag().split_at(1).1
    }

    /// Qualified universe algebra for this exact world. The historical
    /// profiles and the measured recent profiles keep their existing mapping.
    #[must_use]
    pub const fn level_profile(self) -> crate::level::LeanLevelProfile {
        match self {
            Self::Lean408 | Self::Lean413 => crate::level::LeanLevelProfile::Lean48,
            Self::Lean426 | Self::Lean430Rc2 | Self::Lean435 | Self::Lean436Rc2 | Self::Lean436 => {
                crate::level::LeanLevelProfile::Lean430
            }
        }
    }

    /// Source elaboration in these worlds imports and checks the release's
    /// `Init` over a bare replay environment. An explicit `prelude` header
    /// starts without `Init`.
    #[must_use]
    pub const fn requires_genuine_init(self) -> bool {
        matches!(self, Self::Lean435 | Self::Lean436Rc2 | Self::Lean436)
    }

    /// Whether `public/private variable` is accepted. In the admitted 4.36
    /// releases `BuiltinCommand.elabVariable` discards the modifier.
    #[must_use]
    pub const fn variable_visibility(self) -> bool {
        matches!(self, Self::Lean436Rc2 | Self::Lean436)
    }
}

impl std::str::FromStr for LeanWorld {
    type Err = UnknownLeanWorld;

    fn from_str(tag: &str) -> Result<Self, Self::Err> {
        Self::ALL
            .into_iter()
            .find(|world| world.tag() == tag)
            .ok_or_else(|| UnknownLeanWorld(tag.to_owned()))
    }
}

impl std::fmt::Display for LeanWorld {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.tag())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn lean_worlds_are_closed_and_default_to_the_oracle() {
        assert_eq!(LeanWorld::default(), LeanWorld::ORACLE);
        for world in LeanWorld::ALL {
            assert_eq!(world.tag().parse::<LeanWorld>(), Ok(world));
            assert_eq!(
                world.variable_visibility(),
                matches!(world, LeanWorld::Lean436Rc2 | LeanWorld::Lean436)
            );
        }
        for unknown in ["v4.31.0", "v4.36.0-rc1", "v4.99.0", ""] {
            assert_eq!(
                unknown.parse::<LeanWorld>(),
                Err(UnknownLeanWorld(unknown.to_owned()))
            );
        }
    }
}
