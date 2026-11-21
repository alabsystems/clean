// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The commands inside one top-level surface declaration, in source order.
//!
//! The driver flattens a `namespace` / `section` / `mutual` block to its
//! leaves and reports each leaf with the TOP-LEVEL declaration; Lean logs each
//! member's messages at the member. These are the members a leaf or a command
//! output is matched back to, so its message lands where Lean puts it.

use clean_elab::module_driver::{surface_decl_name, surface_decl_span};
use clean_elab::{CommandOutput, ElabResult};
use clean_parser::SurfaceDecl;

/// What a member is, for matching outcomes to it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum MemberKind {
    /// A named declaration (`def`, `theorem`, `structure`, …).
    Decl,
    /// An `example`.
    Example,
    /// An `instance`.
    Instance,
    /// A command whose output is a message (`#eval`, `#check`, `#print`,
    /// `#print axioms`, `#guard_msgs`).
    Command,
    /// Anything else (`open`, `variable`, `#guard`, …).
    Other,
}

/// One member of a top-level declaration.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Member {
    pub(crate) start: usize,
    pub(crate) end: usize,
    pub(crate) kind: MemberKind,
    /// The written name, for named declarations.
    pub(crate) name: Option<String>,
    /// The command a `#guard_msgs` wraps (or a member of it): a message it
    /// logs is checked by the `#guard_msgs`, not logged, when that matches.
    pub(crate) guarded: bool,
}

impl Member {
    /// `decl` itself as one member.
    pub(crate) fn whole(decl: &SurfaceDecl, start: usize, end: usize) -> Self {
        Self {
            start,
            end,
            kind: kind_of(decl),
            name: surface_decl_name(decl),
            guarded: false,
        }
    }

    /// Whether the elaborated name `name` (namespace-qualified) is this
    /// member's written name.
    pub(crate) fn matches_name(&self, name: &str) -> bool {
        self.name
            .as_deref()
            .is_some_and(|written| name == written || name.ends_with(&format!(".{written}")))
    }

    /// Whether the checked leaf `leaf`, named `name`, is this member's.
    pub(crate) fn matches_leaf(&self, name: &str, leaf: &ElabResult) -> bool {
        match leaf {
            ElabResult::Diagnosed { result, .. } => self.matches_leaf(name, result),
            ElabResult::Example { .. } => self.kind == MemberKind::Example,
            ElabResult::Command(CommandOutput::GuardMsgs(_)) => self.kind == MemberKind::Command,
            ElabResult::Instance { .. }
                if self.kind == MemberKind::Instance && self.name.is_none() =>
            {
                true
            }
            _ => {
                matches!(self.kind, MemberKind::Decl | MemberKind::Instance)
                    && self.matches_name(name)
            }
        }
    }
}

fn kind_of(decl: &SurfaceDecl) -> MemberKind {
    match decl {
        SurfaceDecl::Def { .. }
        | SurfaceDecl::Theorem { .. }
        | SurfaceDecl::Axiom { .. }
        | SurfaceDecl::Opaque { .. }
        | SurfaceDecl::Inductive { .. }
        | SurfaceDecl::Coinductive { .. }
        | SurfaceDecl::Codata { .. }
        | SurfaceDecl::Codef { .. }
        | SurfaceDecl::Structure { .. }
        | SurfaceDecl::Class { .. } => MemberKind::Decl,
        SurfaceDecl::Example { .. } => MemberKind::Example,
        SurfaceDecl::Instance { .. } => MemberKind::Instance,
        SurfaceDecl::Check { .. }
        | SurfaceDecl::Eval { .. }
        | SurfaceDecl::Reduce { .. }
        | SurfaceDecl::Print { .. }
        | SurfaceDecl::PrintAxioms { .. }
        | SurfaceDecl::PrintEquations { .. }
        | SurfaceDecl::GuardMsgs { .. } => MemberKind::Command,
        _ => MemberKind::Other,
    }
}

/// Every member of `decl`, blocks and `… in` wrappers opened, in source
/// order. A `#guard_msgs` is a member itself (its passthrough output) and is
/// followed by the command it wraps.
pub(crate) fn flatten_members(decl: &SurfaceDecl) -> Vec<Member> {
    let mut out = Vec::new();
    push_members(decl, false, &mut out);
    out
}

fn push_members(decl: &SurfaceDecl, guarded: bool, out: &mut Vec<Member>) {
    match decl {
        SurfaceDecl::Namespace { decls, .. }
        | SurfaceDecl::Section { decls, .. }
        | SurfaceDecl::Mutual { decls, .. } => {
            for inner in decls {
                push_members(inner, guarded, out);
            }
        }
        SurfaceDecl::SetOption {
            body: Some(body), ..
        }
        | SurfaceDecl::Open {
            body: Some(body), ..
        } => push_members(body, guarded, out),
        SurfaceDecl::GuardMsgs { cmd, .. } => {
            out.push(whole(decl, guarded));
            push_members(cmd, true, out);
        }
        _ => out.push(whole(decl, guarded)),
    }
}

fn whole(decl: &SurfaceDecl, guarded: bool) -> Member {
    let (start, end) = surface_decl_span(decl).map_or((0, 0), |span| (span.start, span.end));
    Member {
        guarded,
        ..Member::whole(decl, start, end)
    }
}

/// The member whose span holds byte `offset`, innermost (last) first.
pub(crate) fn member_at(members: &[Member], offset: usize) -> Option<&Member> {
    members
        .iter()
        .rev()
        .find(|member| member.start <= offset && offset < member.end)
}
