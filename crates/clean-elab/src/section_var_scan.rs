// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The surface scan behind [`super::select_section_binders`]: the free
//! identifiers of exactly the parts of a declaration its Lean rule reads, and
//! whether the scan saw all of them.

use std::collections::HashSet;

use clean_parser::{SurfaceBinder, SurfaceDecl, SurfaceExpr, SurfaceName, WhereLocalDef};

use super::SectionVarRule;
use crate::where_desugar_ext::collect_free_idents_detailed;

/// The surface free identifiers of the parts of a declaration its rule reads,
/// accumulated together with whether the scan saw all of them.
pub(super) struct ScanAcc {
    pub(super) free: HashSet<SurfaceName>,
    pub(super) complete: bool,
    /// The names a declaration binder's type (or `optParam` default) mentions
    /// BEFORE any binder of the declaration's own binds them. A telescope
    /// binds left to right, so in `theorem t (h : a = a) (a : Bool) : …` the
    /// `a` of `h`'s type is the SECTION variable — the declaration's own `a`
    /// only shadows it from there on (see [`ScanAcc::decl_binders`]).
    pub(super) before_own_binder: HashSet<SurfaceName>,
    /// Section variables a user template's free reference denotes
    /// (`clean_parser::mark_template_free_references`): used, and never
    /// shadowed by a binder of the declaration (Lean resolves the reference
    /// through `sectionFVars`, past every local).
    pub(super) template_section: HashSet<SurfaceName>,
}

impl ScanAcc {
    fn new() -> Self {
        Self {
            free: HashSet::new(),
            complete: true,
            before_own_binder: HashSet::new(),
            template_section: HashSet::new(),
        }
    }

    /// A template's free reference that does not denote a section variable
    /// never resolves to one, so only `plain` occurrences count as uses.
    fn expr(&mut self, expr: &SurfaceExpr) {
        let (free, complete) = collect_free_idents_detailed(expr);
        self.free.extend(free.plain);
        self.template_section.extend(free.template_section);
        self.complete &= complete;
    }

    /// A `where` helper: its binder types and return type, then its body
    /// with its own parameters bound (they shadow any section variable of
    /// the same name inside the body).
    fn where_decl(&mut self, w: &WhereLocalDef) {
        self.binders(&w.binders);
        if let Some(rt) = &w.ret_ty {
            self.expr(rt);
        }
        let (free, complete) = collect_free_idents_detailed(&w.body);
        let mut plain = free.plain;
        for b in &w.binders {
            plain.remove(&b.name);
        }
        self.free.extend(plain);
        self.template_section.extend(free.template_section);
        self.complete &= complete;
    }

    /// The declaration's OWN binders, left to right: [`ScanAcc::binders`] per
    /// binder, recording in `before_own_binder` every name a binder mentions
    /// that no EARLIER binder of the telescope binds. The selection removes a
    /// declaration's own binder names from the used set (they shadow the
    /// section variable of the same name) — but a mention that precedes the
    /// shadowing binder is a use of the section variable, and Lean includes
    /// it. Measured on the pinned v4.30.0-rc2 (2026-09-20), with `variable (a :
    /// Nat)`: `theorem shadow_late (h : a = a) (a : Bool) : a = a` is `∀ (a :
    /// Nat), a = a → ∀ (a : Bool), a = a`. Removed by name alone, the section
    /// `a` was dropped, `h`'s `a` was auto-bound, and the theorem died with
    /// `unsolved metavariables` — or, where the auto-bound type could be
    /// inferred (`(n : Nat := a)`), registered with an IMPLICIT `a` where Lean
    /// has an explicit one.
    fn decl_binders(&mut self, binders: &[SurfaceBinder]) {
        let mut bound: HashSet<&SurfaceName> = HashSet::new();
        for b in binders {
            let mut one = Self::new();
            one.binders(std::slice::from_ref(b));
            self.before_own_binder
                .extend(one.free.iter().filter(|n| !bound.contains(n)).cloned());
            self.free.extend(one.free);
            self.template_section.extend(one.template_section);
            self.complete &= one.complete;
            bound.insert(&b.name);
        }
    }

    /// Binder types, and `optParam` defaults (part of the header type in
    /// Lean). An `autoParam` default is a TACTIC — syntax, not a term, so its
    /// identifiers are not free variables of the header (Lean stores it as the
    /// quoted syntax of `autoParam T stx`) and it is not scanned.
    fn binders(&mut self, binders: &[SurfaceBinder]) {
        for b in binders {
            if let Some(ty) = &b.ty {
                self.expr(ty);
            }
            if let Some(default) = &b.default {
                if !matches!(**default, SurfaceExpr::ByTactic(..)) {
                    self.expr(default);
                }
            }
        }
    }
}

/// Scan what `decl`'s rule reads. `None` for declaration kinds that never
/// receive section binders here (mirroring which kinds `preprocess` prepends
/// variables to).
pub(super) fn scan_decl(
    decl: &SurfaceDecl,
) -> Option<(SectionVarRule, ScanAcc, HashSet<SurfaceName>)> {
    let mut acc = ScanAcc::new();
    let (rule, binders) = match decl {
        SurfaceDecl::Def {
            binders,
            ty,
            val,
            where_decls,
            ..
        } => {
            acc.decl_binders(binders);
            if let Some(ty) = ty {
                acc.expr(ty);
            }
            acc.expr(val);
            for w in where_decls {
                acc.where_decl(w);
            }
            let mut own: HashSet<SurfaceName> = binders.iter().map(|b| b.name.clone()).collect();
            // A `where` helper's name is a local of the body, not a section
            // variable of the same name.
            own.extend(where_decls.iter().map(|w| w.name.clone()));
            return Some((SectionVarRule::Used, acc, own));
        }
        // The HEADER only: binders and statement. The proof, and the `where`
        // helpers that live inside it, are elaborated in the context the
        // header selects and never add a variable (`withHeaderSecVars`).
        SurfaceDecl::Theorem { binders, ty, .. } => {
            acc.decl_binders(binders);
            acc.expr(ty);
            (SectionVarRule::Header, binders)
        }
        // An axiom closes the used section locals over its elaborated type
        // (`elabAxiom`, `mkForallFVars vars ... (usedOnly := true)`).
        // `include` does not force an otherwise unused axiom parameter.
        SurfaceDecl::Axiom { binders, ty, .. } => {
            acc.decl_binders(binders);
            acc.expr(ty);
            (SectionVarRule::Used, binders)
        }
        // `opaque` is elaborated as a definition whose value is Lean's
        // `default_or_ofNonempty%` (or the written one): the variables its
        // header and value use, plus the instances over them (an `[Inhabited
        // α]` section variable is what serves `opaque o : α`).
        SurfaceDecl::Opaque {
            binders, ty, val, ..
        } => {
            acc.decl_binders(binders);
            acc.expr(ty);
            if let Some(val) = val {
                acc.expr(val);
            }
            (SectionVarRule::Used, binders)
        }
        SurfaceDecl::Example {
            binders, ty, val, ..
        } => {
            acc.decl_binders(binders);
            if let Some(ty) = ty {
                acc.expr(ty);
            }
            acc.expr(val);
            (SectionVarRule::Used, binders)
        }
        SurfaceDecl::Instance {
            binders,
            class_type,
            fields,
            ..
        } => {
            acc.decl_binders(binders);
            acc.expr(class_type);
            for f in fields {
                acc.expr(&f.val);
            }
            (SectionVarRule::Used, binders)
        }
        _ => return None,
    };
    let own = binders.iter().map(|b| b.name.clone()).collect();
    Some((rule, acc, own))
}
