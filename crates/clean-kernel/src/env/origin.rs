// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Per-constant origin and trust metadata.

use crate::name::Name;
use serde::{Deserialize, Serialize};

use super::Environment;

/// How a constant's declaration was validated before it entered this
/// environment.
///
/// This is deliberately distinct from [`ConstantOrigin`]: origin answers
/// *where* an object came from, while this answers *which kernel gate* the
/// exact type/value pair passed.  Certification must never infer the latter
/// from a declaration's name or kind.
///
/// The map carrying this value is transient (`serde(skip)`).  A deserialized
/// environment therefore has `None`/unknown provenance, never an implicitly
/// trusted default.  Trust-sensitive callers either reject that state or run
/// the declaration through a fresh full read-only kernel check.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum DeclarationVerification {
    /// Type and value passed the same full kernel checks as [`Environment::add_decl`].
    FullKernelCheck,
    /// Only structural invariants were checked (`add_decl_structural`).
    StructuralOnly,
    /// The declaration was inserted through an explicitly unchecked path.
    Unchecked,
}

/// Trust status attached to a constant origin.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum OriginTrust {
    /// Added through a Clean kernel path that performed its normal checks.
    KernelChecked,
    /// Imported from a `.olean` without a validated external pin/hash policy.
    OleanUnpinned,
    /// Imported from a Clean payload embedded in a `.olean`, also without a pin policy.
    CleanPayloadUnpinned,
}

impl OriginTrust {
    /// Returns true for imported artifacts that still need a later pin policy.
    #[must_use]
    pub fn is_unpinned(self) -> bool {
        matches!(
            self,
            OriginTrust::OleanUnpinned | OriginTrust::CleanPayloadUnpinned
        )
    }

    /// Returns true for structurally-imported constants that were admitted
    /// WITHOUT a Clean-kernel type-check and therefore still need a genuine
    /// `add_decl`-equivalent re-check before any code may treat them as
    /// kernel-verified.
    ///
    /// This is the G5 (Pillar-2) "needs_recheck" marker: the `.olean`/mathverse
    /// STRUCTURAL import lanes register constants via
    /// `extend_constants_structural` (only O(1) structural checks: no free vars,
    /// no metavariables, correct level scope) and TRUST the imported type/value
    /// as already-checked-on-export. Such a constant is stored `OleanUnpinned`
    /// or `CleanPayloadUnpinned`, both of which report `needs_recheck() == true`.
    /// A `KernelChecked` constant (added through the kernel's own checking path)
    /// reports `false`.
    ///
    /// The soundness invariant enforced on top of this predicate (see
    /// [`Environment::set_constant_origins`]) is: a `needs_recheck` constant can
    /// only be PROMOTED to `KernelChecked` through the gated
    /// [`Environment::promote_origin_kernel_checked`] path, which is wired ONLY
    /// from an actual kernel re-check (`typecheck_constants_full` / the bootstrap
    /// re-verify lane). No path may raise a `needs_recheck` constant's trust
    /// without that re-check — fail-closed.
    #[must_use]
    pub fn needs_recheck(self) -> bool {
        // Currently exactly the unpinned import set. Kept as a distinct,
        // intention-revealing predicate so the promotion gate reads as a
        // soundness invariant, not an incidental alias.
        self.is_unpinned()
    }
}

/// Where a constant came from, stored separately from `ConstantInfo`.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum ConstantOrigin {
    /// Locally/kernel-created declaration.
    Kernel { trust: OriginTrust },
    /// Constant converted from a Lean `.olean` module.
    Olean {
        module: Option<String>,
        trust: OriginTrust,
    },
    /// Kernel object loaded from Clean's payload trailer inside a `.olean`.
    CleanPayload {
        module: Option<String>,
        trust: OriginTrust,
    },
}

impl ConstantOrigin {
    /// Origin for kernel-checked local declarations.
    #[must_use]
    pub fn kernel_checked() -> Self {
        Self::Kernel {
            trust: OriginTrust::KernelChecked,
        }
    }

    /// Origin for a converted Lean `.olean` declaration.
    #[must_use]
    pub fn olean_import(module: Option<String>) -> Self {
        Self::Olean {
            module,
            trust: OriginTrust::OleanUnpinned,
        }
    }

    /// Origin for a Clean payload declaration embedded in a `.olean`.
    #[must_use]
    pub fn clean_payload(module: Option<String>) -> Self {
        Self::CleanPayload {
            module,
            trust: OriginTrust::CleanPayloadUnpinned,
        }
    }

    /// The trust status for this origin.
    #[must_use]
    pub fn trust(&self) -> OriginTrust {
        match self {
            ConstantOrigin::Kernel { trust }
            | ConstantOrigin::Olean { trust, .. }
            | ConstantOrigin::CleanPayload { trust, .. } => *trust,
        }
    }

    /// Imported module name, when known.
    #[must_use]
    pub fn module_name(&self) -> Option<&str> {
        match self {
            ConstantOrigin::Olean { module, .. } | ConstantOrigin::CleanPayload { module, .. } => {
                module.as_deref()
            }
            ConstantOrigin::Kernel { .. } => None,
        }
    }

    /// Returns true for constants imported from `.olean` without a pin policy.
    #[must_use]
    pub fn is_unpinned_olean_import(&self) -> bool {
        matches!(self, ConstantOrigin::Olean { .. }) && self.trust().is_unpinned()
    }

    /// Returns true when this origin marks a structurally-imported constant that
    /// has NOT been Clean-kernel re-checked (the G5 "needs_recheck" marker).
    ///
    /// See [`OriginTrust::needs_recheck`] for the full soundness contract. Any
    /// `.olean`/mathverse structural import (`extend_constants_structural`)
    /// carries such an origin; a kernel-checked local declaration does not.
    #[must_use]
    pub fn needs_recheck(&self) -> bool {
        self.trust().needs_recheck()
    }

    /// Whether this origin marks a genuinely kernel-checked constant.
    #[must_use]
    pub fn is_kernel_checked(&self) -> bool {
        matches!(self.trust(), OriginTrust::KernelChecked)
    }

    /// The same origin but with its trust raised to [`OriginTrust::KernelChecked`],
    /// preserving the module provenance. Used by the gated promotion path only.
    #[must_use]
    fn to_kernel_checked(&self) -> Self {
        match self {
            ConstantOrigin::Kernel { .. } => ConstantOrigin::Kernel {
                trust: OriginTrust::KernelChecked,
            },
            ConstantOrigin::Olean { module, .. } => ConstantOrigin::Olean {
                module: module.clone(),
                trust: OriginTrust::KernelChecked,
            },
            ConstantOrigin::CleanPayload { module, .. } => ConstantOrigin::CleanPayload {
                module: module.clone(),
                trust: OriginTrust::KernelChecked,
            },
        }
    }
}

impl Environment {
    /// Return the validation provenance recorded for `name`.
    ///
    /// `None` is conservative/unknown.  In particular, provenance is not
    /// serialized, so loading an older or external environment can never mint
    /// a `FullKernelCheck` claim merely because metadata was absent.
    #[must_use]
    pub fn declaration_verification(&self, name: &Name) -> Option<DeclarationVerification> {
        self.declaration_verification.get(name).copied()
    }

    /// Record origin metadata for an existing constant.
    ///
    /// Returns false if `name` is not currently registered as a constant.
    pub fn set_constant_origin(&mut self, name: Name, origin: ConstantOrigin) -> bool {
        self.set_constant_origins([name], origin) == 1
    }

    /// Record the same origin metadata for multiple existing constants.
    ///
    /// Names that are not registered constants are skipped. The environment
    /// generation is bumped once when at least one origin entry changes.
    ///
    /// # SOUNDNESS — G5 fail-closed promotion gate
    ///
    /// This is the ONE general origin-writing path, so it enforces the Pillar-2
    /// invariant: a constant whose CURRENT origin is `needs_recheck` (a
    /// structurally-imported `.olean`/mathverse constant admitted WITHOUT a
    /// Clean-kernel type-check) can NOT be silently PROMOTED to a
    /// `KernelChecked` origin through this path. Attempting to do so leaves the
    /// constant at its existing `needs_recheck` origin (the promotion is
    /// DROPPED, not applied) — fail-closed. The only way to raise such a
    /// constant to `KernelChecked` is [`Environment::promote_origin_kernel_checked`],
    /// which requires the caller to have first passed the constant through the
    /// kernel's `add_decl`-equivalent re-check.
    ///
    /// This gate can never LOWER the trust of a genuinely-rechecked constant
    /// (it only refuses an *unearned raise*), and it does not touch the normal
    /// import path (which writes an unpinned origin over a no-origin or same
    /// unpinned origin — never a `KernelChecked` upgrade of a `needs_recheck`
    /// constant). Returns the number of origin entries actually changed.
    pub fn set_constant_origins(
        &mut self,
        names: impl IntoIterator<Item = Name>,
        origin: ConstantOrigin,
    ) -> usize {
        let mut changed = 0usize;
        let raises_to_kernel_checked = origin.is_kernel_checked();
        for name in names {
            if !self.constants.contains_key(&name) {
                continue;
            }
            if self.constant_origins.get(&name) == Some(&origin) {
                continue;
            }
            // G5 fail-closed: refuse to promote a still-needs-recheck import to a
            // KernelChecked origin through the general path. Such a raise is only
            // legitimate via `promote_origin_kernel_checked` (post-recheck).
            if raises_to_kernel_checked
                && self
                    .constant_origins
                    .get(&name)
                    .is_some_and(ConstantOrigin::needs_recheck)
            {
                debug_assert!(
                    false,
                    "unearned KernelChecked promotion of needs_recheck constant {name:?}; \
                     route through promote_origin_kernel_checked after a kernel re-check"
                );
                continue;
            }
            self.constant_origins.insert(name, origin.clone());
            changed += 1;
        }

        if changed > 0 {
            self.generation += 1;
        }

        changed
    }

    /// Promote a structurally-imported (`needs_recheck`) constant's origin to
    /// [`OriginTrust::KernelChecked`] AFTER it has passed a genuine Clean-kernel
    /// re-check.
    ///
    /// # SOUNDNESS — the ONLY sanctioned `needs_recheck` → `KernelChecked` path
    ///
    /// The caller MUST have just re-derived this constant with the kernel's
    /// `add_decl`-equivalent checker (`typecheck_constants_full`: `infer_sort` on
    /// the type + `check_type` on the value with `infer_only=false`) and observed
    /// a PASS. This method does not itself re-check — it records the earned
    /// promotion — so it is `pub(crate)`-narrow in spirit and every call site
    /// carries a `// SOUNDNESS:` note pinning it to a preceding passing re-check.
    ///
    /// Fail-closed properties:
    /// * Only ever RAISES trust (`needs_recheck` → `KernelChecked`); it can never
    ///   lower a constant's trust.
    /// * A no-op for a constant that is not registered, has no recorded origin,
    ///   or is already `KernelChecked` — returns `false` in those cases.
    /// * It preserves the module provenance (only the trust byte changes).
    ///
    /// Returns `true` iff a `needs_recheck` origin was actually promoted.
    pub fn promote_origin_kernel_checked(&mut self, name: &Name) -> bool {
        if !self.constants.contains_key(name) {
            return false;
        }
        let Some(current) = self.constant_origins.get(name) else {
            // No recorded origin ⇒ not a structural import ⇒ nothing to promote.
            return false;
        };
        if !current.needs_recheck() {
            return false;
        }
        let promoted = current.to_kernel_checked();
        self.constant_origins.insert(name.clone(), promoted);
        self.generation += 1;
        true
    }

    /// Promote a batch of `needs_recheck` constants to `KernelChecked` after a
    /// passing kernel re-check. Convenience over
    /// [`Environment::promote_origin_kernel_checked`]; returns the count promoted.
    ///
    /// SOUNDNESS: identical contract — every `name` passed here MUST have just
    /// passed the kernel's `add_decl`-equivalent re-check.
    pub fn promote_origins_kernel_checked<'a>(
        &mut self,
        names: impl IntoIterator<Item = &'a Name>,
    ) -> usize {
        names
            .into_iter()
            .filter(|n| self.promote_origin_kernel_checked(n))
            .count()
    }

    /// Look up recorded origin metadata for a constant.
    #[must_use]
    pub fn get_constant_origin(&self, name: &Name) -> Option<&ConstantOrigin> {
        self.constant_origins.get(name)
    }

    /// Look up only the trust status for a constant origin.
    #[must_use]
    pub fn constant_origin_trust(&self, name: &Name) -> Option<OriginTrust> {
        self.get_constant_origin(name).map(ConstantOrigin::trust)
    }

    /// Whether the constant was tagged as an unpinned `.olean` import.
    #[must_use]
    pub fn is_unpinned_olean_import(&self, name: &Name) -> bool {
        self.get_constant_origin(name)
            .is_some_and(ConstantOrigin::is_unpinned_olean_import)
    }

    /// Whether this constant was structurally imported and still needs a genuine
    /// Clean-kernel re-check before it may be treated as kernel-verified (the G5
    /// "needs_recheck" marker). A constant with no recorded origin (a
    /// kernel-checked local declaration) reports `false`.
    #[must_use]
    pub fn constant_needs_recheck(&self, name: &Name) -> bool {
        self.get_constant_origin(name)
            .is_some_and(ConstantOrigin::needs_recheck)
    }

    /// Whether this constant's origin is genuinely `KernelChecked` (either an
    /// original kernel declaration or a structural import that was promoted
    /// through [`Environment::promote_origin_kernel_checked`] after a passing
    /// re-check).
    #[must_use]
    pub fn constant_is_kernel_checked(&self, name: &Name) -> bool {
        self.get_constant_origin(name)
            .is_some_and(ConstantOrigin::is_kernel_checked)
    }
}
