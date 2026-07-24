// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended macro hygiene (level 3): scope coloring, capture analysis,
//! violation reporting with fix suggestions, name binding analysis,
//! hygiene invariant validation, and cross-scope reference tracking.

use std::collections::{HashMap, HashSet};
use std::fmt;
use std::sync::atomic::{AtomicU64, Ordering};

use clean_kernel::Name;

static SCOPE_COLOR_COUNTER: AtomicU64 = AtomicU64::new(1);

/// A unique color assigned to a macro expansion scope for tracking.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct ScopeColor(u64);

impl ScopeColor {
    #[must_use]
    pub(crate) fn transparent() -> Self {
        Self(0)
    }
    #[must_use]
    pub(crate) fn fresh() -> Self {
        Self(SCOPE_COLOR_COUNTER.fetch_add(1, Ordering::Relaxed))
    }
    #[must_use]
    pub(crate) fn id(self) -> u64 {
        self.0
    }
    #[must_use]
    pub(crate) fn is_transparent(self) -> bool {
        self.0 == 0
    }
}

impl fmt::Display for ScopeColor {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_transparent() {
            f.write_str("color:transparent")
        } else {
            write!(f, "color#{}", self.0)
        }
    }
}

/// Whether a name is bound or free relative to its enclosing scope.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub(crate) enum BindingStatus {
    Bound,
    Free,
}

impl fmt::Display for BindingStatus {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Bound => f.write_str("bound"),
            Self::Free => f.write_str("free"),
        }
    }
}

/// A reference to a name that crosses a scope boundary.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CrossScopeRef {
    pub(crate) name: Name,
    pub(crate) reference_scope: ScopeColor,
    pub(crate) definition_scope: ScopeColor,
}

impl fmt::Display for CrossScopeRef {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "`{}` referenced in {} but defined in {}",
            self.name, self.reference_scope, self.definition_scope
        )
    }
}

/// A detected accidental name capture.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CaptureReport {
    pub(crate) captured_name: Name,
    pub(crate) capturer_scope: ScopeColor,
    pub(crate) original_scope: ScopeColor,
    pub(crate) fix_suggestion: String,
}

impl fmt::Display for CaptureReport {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "capture: `{}` (defined in {}) shadowed by {} -- {}",
            self.captured_name, self.original_scope, self.capturer_scope, self.fix_suggestion
        )
    }
}

/// Kinds of hygiene violations detected by ext3 analysis.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub(crate) enum Ext3ViolationKind {
    AccidentalCapture,
    ScopeLeak,
    UnboundReference,
    ColorBoundaryViolation,
    InvariantBroken,
}

impl fmt::Display for Ext3ViolationKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::AccidentalCapture => f.write_str("AccidentalCapture"),
            Self::ScopeLeak => f.write_str("ScopeLeak"),
            Self::UnboundReference => f.write_str("UnboundReference"),
            Self::ColorBoundaryViolation => f.write_str("ColorBoundaryViolation"),
            Self::InvariantBroken => f.write_str("InvariantBroken"),
        }
    }
}

/// A detailed hygiene violation with a fix suggestion.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Ext3Violation {
    pub(crate) name: Name,
    pub(crate) kind: Ext3ViolationKind,
    pub(crate) scope: ScopeColor,
    pub(crate) message: String,
    pub(crate) fix_suggestion: Option<String>,
}

impl fmt::Display for Ext3Violation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[{}] {} in {}", self.kind, self.message, self.scope)?;
        if let Some(fix) = &self.fix_suggestion {
            write!(f, " -- fix: {fix}")?;
        }
        Ok(())
    }
}

/// Aggregate statistics about scope activity and violations.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub(crate) struct ScopeStatistics {
    pub(crate) max_depth_reached: usize,
    pub(crate) total_colors_allocated: u64,
    pub(crate) total_bindings_introduced: u64,
    pub(crate) total_references_tracked: u64,
    pub(crate) total_captures_detected: u64,
    pub(crate) total_violations: u64,
    pub(crate) cross_scope_refs: u64,
}

/// Errors returned by the ext3 hygiene API.
#[derive(Debug, Clone, thiserror::Error)]
#[non_exhaustive]
pub(crate) enum HygieneExt3Error {
    #[error("scope stack underflow: cannot leave the root scope")]
    ScopeUnderflow,
    #[error("unknown color {color}: not on the scope stack")]
    UnknownColor { color: ScopeColor },
    #[error("unresolved name `{name}` in scope {scope}")]
    Unresolved { name: String, scope: ScopeColor },
    #[error("max scope depth {max} exceeded")]
    DepthExceeded { max: usize },
}

/// A name binding annotated with scope color information.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ColoredBinding {
    pub(crate) name: Name,
    pub(crate) color: ScopeColor,
    pub(crate) macro_generated: bool,
}

const MAX_SCOPE_DEPTH: usize = 256;

/// Extended macro hygiene context (level 3): scope coloring, capture analysis,
/// violation reporting, name binding analysis, and cross-scope reference tracking.
pub(crate) struct HygieneExt3Ctx {
    color_stack: Vec<ScopeColor>,
    bindings: HashMap<String, Vec<ColoredBinding>>,
    cross_scope_refs: Vec<CrossScopeRef>,
    captures: Vec<CaptureReport>,
    violations: Vec<Ext3Violation>,
    stats: ScopeStatistics,
}

impl Default for HygieneExt3Ctx {
    fn default() -> Self {
        Self::new()
    }
}

impl HygieneExt3Ctx {
    #[must_use]
    pub(crate) fn new() -> Self {
        Self {
            color_stack: vec![ScopeColor::transparent()],
            bindings: HashMap::new(),
            cross_scope_refs: Vec::new(),
            captures: Vec::new(),
            violations: Vec::new(),
            stats: ScopeStatistics::default(),
        }
    }

    pub(crate) fn enter_colored_scope(&mut self) -> Result<ScopeColor, HygieneExt3Error> {
        if self.color_stack.len() >= MAX_SCOPE_DEPTH {
            return Err(HygieneExt3Error::DepthExceeded {
                max: MAX_SCOPE_DEPTH,
            });
        }
        let color = ScopeColor::fresh();
        self.color_stack.push(color);
        self.stats.total_colors_allocated += 1;
        if self.color_stack.len() > self.stats.max_depth_reached {
            self.stats.max_depth_reached = self.color_stack.len();
        }
        Ok(color)
    }

    pub(crate) fn leave_colored_scope(&mut self) -> Result<ScopeColor, HygieneExt3Error> {
        if self.color_stack.len() <= 1 {
            return Err(HygieneExt3Error::ScopeUnderflow);
        }
        Ok(self.color_stack.pop().expect("invariant: len > 1"))
    }

    #[must_use]
    pub(crate) fn current_color(&self) -> ScopeColor {
        self.color_stack
            .last()
            .copied()
            .unwrap_or_else(ScopeColor::transparent)
    }

    #[must_use]
    pub(crate) fn scope_depth(&self) -> usize {
        self.color_stack.len()
    }

    #[must_use]
    pub(crate) fn color_stack(&self) -> &[ScopeColor] {
        &self.color_stack
    }

    #[must_use]
    pub(crate) fn is_color_active(&self, color: ScopeColor) -> bool {
        color.is_transparent() || self.color_stack.contains(&color)
    }

    pub(crate) fn introduce_binding(&mut self, name: &Name, macro_generated: bool) {
        let color = self.current_color();
        let binding = ColoredBinding {
            name: name.clone(),
            color,
            macro_generated,
        };
        let entries = self.bindings.entry(name.to_string()).or_default();
        if !entries.iter().any(|b| b.color == color && b.name == *name) {
            entries.push(binding);
        }
        self.stats.total_bindings_introduced += 1;
    }

    #[must_use]
    pub(crate) fn bindings_for(&self, name: &Name) -> &[ColoredBinding] {
        self.bindings
            .get(&name.to_string())
            .map_or(&[], Vec::as_slice)
    }

    #[must_use]
    pub(crate) fn names_in_color(&self, color: ScopeColor) -> Vec<Name> {
        let mut names: Vec<Name> = self
            .bindings
            .values()
            .flatten()
            .filter(|b| b.color == color)
            .map(|b| b.name.clone())
            .collect();
        names.sort_by_key(|a| a.to_string());
        names.dedup_by(|a, b| a.to_string() == b.to_string());
        names
    }

    #[must_use]
    pub(crate) fn binding_status(&self, name: &Name) -> BindingStatus {
        let Some(entries) = self.bindings.get(&name.to_string()) else {
            return BindingStatus::Free;
        };
        if entries.iter().any(|b| self.is_color_active(b.color)) {
            BindingStatus::Bound
        } else {
            BindingStatus::Free
        }
    }

    pub(crate) fn resolve_name(&mut self, name: &Name) -> Result<ColoredBinding, HygieneExt3Error> {
        self.stats.total_references_tracked += 1;
        let key = name.to_string();
        let Some(entries) = self.bindings.get(&key) else {
            return Err(HygieneExt3Error::Unresolved {
                name: key,
                scope: self.current_color(),
            });
        };
        let visible: Vec<&ColoredBinding> = entries
            .iter()
            .filter(|b| self.is_color_active(b.color))
            .collect();
        match visible.last() {
            Some(b) => Ok((*b).clone()),
            None => Err(HygieneExt3Error::Unresolved {
                name: key,
                scope: self.current_color(),
            }),
        }
    }

    pub(crate) fn track_reference(&mut self, name: &Name) {
        self.stats.total_references_tracked += 1;
        let ref_color = self.current_color();
        let key = name.to_string();
        let def_color = self
            .bindings
            .get(&key)
            .and_then(|entries| entries.iter().rfind(|b| self.is_color_active(b.color)))
            .map(|b| b.color);
        if let Some(dc) = def_color {
            if dc != ref_color {
                self.cross_scope_refs.push(CrossScopeRef {
                    name: name.clone(),
                    reference_scope: ref_color,
                    definition_scope: dc,
                });
                self.stats.cross_scope_refs += 1;
            }
        } else {
            self.push_violation(
                name,
                Ext3ViolationKind::UnboundReference,
                &format!("`{name}` has no visible binding"),
                Some(&format!("introduce `{name}` in an enclosing scope")),
            );
        }
    }

    #[must_use]
    pub(crate) fn cross_scope_refs(&self) -> &[CrossScopeRef] {
        &self.cross_scope_refs
    }

    pub(crate) fn detect_capture(&mut self, name: &Name) -> Option<CaptureReport> {
        let entries = self.bindings.get(&name.to_string())?;
        let visible: Vec<&ColoredBinding> = entries
            .iter()
            .filter(|b| self.is_color_active(b.color))
            .collect();
        let user_binding = visible.iter().find(|b| !b.macro_generated)?;
        let macro_binding = visible.iter().find(|b| b.macro_generated)?;
        let report = CaptureReport {
            captured_name: name.clone(),
            capturer_scope: macro_binding.color,
            original_scope: user_binding.color,
            fix_suggestion: format!(
                "rename macro-generated `{name}` to a gensym (e.g. `{name}_hyg`)"
            ),
        };
        self.captures.push(report.clone());
        self.stats.total_captures_detected += 1;
        Some(report)
    }

    pub(crate) fn detect_all_captures(&mut self) -> Vec<CaptureReport> {
        let keys: Vec<String> = self.bindings.keys().cloned().collect();
        let mut reports = Vec::new();
        for key in &keys {
            if let Some(r) = self.detect_capture(&Name::from_string(key)) {
                reports.push(r);
            }
        }
        reports
    }

    #[must_use]
    pub(crate) fn captures(&self) -> &[CaptureReport] {
        &self.captures
    }

    pub(crate) fn record_violation(
        &mut self,
        name: &Name,
        kind: Ext3ViolationKind,
        message: &str,
        fix_suggestion: Option<&str>,
    ) {
        self.push_violation(name, kind, message, fix_suggestion);
    }

    #[must_use]
    pub(crate) fn violations(&self) -> &[Ext3Violation] {
        &self.violations
    }

    pub(crate) fn take_violations(&mut self) -> Vec<Ext3Violation> {
        std::mem::take(&mut self.violations)
    }

    #[must_use]
    pub(crate) fn violation_report(&self) -> String {
        if self.violations.is_empty() {
            return "No hygiene violations detected.".to_owned();
        }
        let mut report = format!("{} hygiene violation(s):\n", self.violations.len());
        for (i, v) in self.violations.iter().enumerate() {
            report.push_str(&format!("  {}. {v}\n", i + 1));
        }
        report
    }

    /// Validate hygiene invariants: root at bottom, no duplicate colors, depth bounded.
    pub(crate) fn validate_invariants(&mut self) -> Vec<Ext3Violation> {
        let mut inv = Vec::new();
        let dummy = Name::from_string("<invariant>");
        if self.color_stack.first().is_none_or(|c| !c.is_transparent()) {
            inv.push(Ext3Violation {
                name: dummy.clone(),
                kind: Ext3ViolationKind::InvariantBroken,
                scope: ScopeColor::transparent(),
                message: "root color is not at the bottom of the stack".to_owned(),
                fix_suggestion: Some("ensure the root scope is never removed".to_owned()),
            });
        }
        let mut seen = HashSet::new();
        for color in &self.color_stack {
            if !seen.insert(*color) {
                inv.push(Ext3Violation {
                    name: dummy.clone(),
                    kind: Ext3ViolationKind::InvariantBroken,
                    scope: *color,
                    message: format!("duplicate color {color} on the stack"),
                    fix_suggestion: Some("each scope should have a unique color".to_owned()),
                });
            }
        }
        if self.color_stack.len() > MAX_SCOPE_DEPTH {
            inv.push(Ext3Violation {
                name: dummy.clone(),
                kind: Ext3ViolationKind::InvariantBroken,
                scope: self.current_color(),
                message: format!(
                    "scope depth {} exceeds maximum {MAX_SCOPE_DEPTH}",
                    self.color_stack.len()
                ),
                fix_suggestion: Some("reduce macro nesting depth".to_owned()),
            });
        }
        self.violations.extend(inv.clone());
        self.stats.total_violations += inv.len() as u64;
        inv
    }

    /// Full audit: invariants + captures + scope leak detection.
    pub(crate) fn full_audit(&mut self) -> Vec<Ext3Violation> {
        self.validate_invariants();
        self.detect_all_captures();
        self.audit_binding_leaks();
        self.violations.clone()
    }

    #[must_use]
    pub(crate) fn statistics(&self) -> &ScopeStatistics {
        &self.stats
    }

    fn push_violation(
        &mut self,
        name: &Name,
        kind: Ext3ViolationKind,
        message: &str,
        fix_suggestion: Option<&str>,
    ) {
        self.violations.push(Ext3Violation {
            name: name.clone(),
            kind,
            scope: self.current_color(),
            message: message.to_owned(),
            fix_suggestion: fix_suggestion.map(str::to_owned),
        });
        self.stats.total_violations += 1;
    }

    fn audit_binding_leaks(&mut self) {
        let current = self.current_color();
        let keys: Vec<String> = self.bindings.keys().cloned().collect();
        for key in &keys {
            let entries = self.bindings.get(key).cloned().unwrap_or_default();
            for entry in &entries {
                if !entry.color.is_transparent() && !self.color_stack.contains(&entry.color) {
                    let v = Ext3Violation {
                        name: entry.name.clone(),
                        kind: Ext3ViolationKind::ScopeLeak,
                        scope: entry.color,
                        message: format!(
                            "`{}` from {} not visible from {}",
                            entry.name, entry.color, current
                        ),
                        fix_suggestion: Some(format!(
                            "move binding `{}` to a shared ancestor scope",
                            entry.name
                        )),
                    };
                    if !self.violations.contains(&v) {
                        self.violations.push(v);
                        self.stats.total_violations += 1;
                    }
                }
            }
        }
    }
}
