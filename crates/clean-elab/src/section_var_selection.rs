// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Which section `variable`s a declaration receives.
//!
//! Lean decides this in `Lean/Elab/MutualDef.lean` by two different rules,
//! chosen by declaration kind:
//!
//! * A `theorem` keeps the section variables its HEADER mentions, the ones an
//!   `include` names, whatever those depend on, and every instance-implicit
//!   variable whose type mentions only kept variables (`withHeaderSecVars`,
//!   `MutualDef.lean:443-490`, selected for theorems at :533 and :1393). The
//!   proof is never consulted — it is elaborated in the restricted context, so
//!   a proof that names an omitted variable is `Unknown identifier`.
//! * Every other value declaration (`def`, `abbrev`, `instance`) is elaborated
//!   with ALL section variables in scope and keeps exactly those whose free
//!   variables occur in its elaborated header and value, closed under the
//!   types of the kept ones (`withUsed` / `removeUnusedVars`, :593-609, over
//!   `Meta.removeUnused`, `Lean/Meta/CollectFVars.lean:53`). `include` plays no
//!   part there.
//!
//! Clean selects before elaboration, from a surface free-identifier scan
//! ([`crate::where_desugar_ext::collect_free_idents_checked`]). A theorem's
//! header is what Lean reads too, so for theorems the scan IS the rule. For
//! the others it approximates the elaborated occurrence test. Where the scan
//! cannot see every identifier, the selection is every section variable plus a
//! request to apply Lean's rule to the ELABORATED declaration instead
//! ([`select_section_binders`], `crate::infer::section_prune`). The same
//! request is armed, over the selection, when a definition's scan activated an
//! instance variable the definition does not name ([`used_selection`]):
//! whether the value reached it is only visible in the elaborated term.
//!
//! Measured on the pinned v4.30.0-rc2 `lean` (2026-09-12), in a section with
//! `variable {α : Type} (h : α)` and `include h`: `def dinc : Nat := 0` gives
//! `dinc : Nat`, and `theorem tshadow (h : True) : True := h` gives
//! `∀ {α : Type} (h : α), True → True` — the included `h` is bound although
//! the theorem's own `h` shadows it. With `variable {α β : Type} [C2 α β]
//! [Inhabited Nat] {γ : Type} [Inhabited γ]`, `theorem tonly (a : α) : a = a`
//! gives `∀ {α : Type} [Inhabited Nat] (a : α), a = a`: `[C2 α β]` is left out
//! because `β` is not kept, `[Inhabited Nat]` is kept because its type
//! mentions no variable at all.
//!
//! The theorem rule reads the ELABORATED header, and the elaborated header can
//! name a variable its surface does not: instance resolution fills an
//! `outParam` from a section instance. With `class Get (F : Type) (β :
//! outParam Type)` and `variable {F β : Type} [Get F β]`, `theorem t (f g : F)
//! (h : f = g) : Get.get f = Get.get g` names only `F`, yet Lean gives `@t :
//! ∀ {F β : Type} [inst : Get F β] (f g : F), …` — `Get.get f` elaborated to
//! `@Get.get F β inst f`. So whenever an instance-implicit variable's type
//! mentions a kept variable AND one the surface did not keep, the surface
//! cannot decide the instance rule, and the selection defers it to the
//! elaborated header (see [`header_selection`]).

use std::collections::HashSet;

use clean_parser::{SurfaceBinder, SurfaceBinderInfo, SurfaceDecl, SurfaceName};

use crate::infer::section_prune::{PruneRule, SectionPruneRequest};
use crate::macro_integration::MacroCtx;
use crate::where_desugar_ext::collect_free_idents;

#[path = "section_var_scan.rs"]
mod scan;
use scan::scan_decl;

/// The Lean rule a declaration kind follows (see the module doc).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum SectionVarRule {
    /// `theorem`: Lean's `withHeaderSecVars` — header, `include`, dependency
    /// closure, then instance-implicits over kept variables.
    Header,
    /// `def` / `abbrev` / `instance`: Lean's `removeUnusedVars` — the
    /// variables the declaration uses, closed under their types.
    Used,
}

/// The section variables selected for one declaration.
#[derive(Debug, Clone, Default)]
pub(crate) struct SectionVarSelection {
    /// The section binders to prepend, in declaration order.
    pub(crate) binders: Vec<SurfaceBinder>,
    /// `Some` when the surface scan could not see the whole declaration:
    /// `binders` is then every section variable, and the elaborator is to
    /// drop the unused ones from the elaborated term.
    pub(crate) prune: Option<SectionPruneRequest>,
}

/// The section binders `decl` receives, in declaration order.
///
/// `forced` names the section variables an `include` command put in scope.
/// Under the theorem rule they are kept whether the theorem mentions them or
/// not — even when a binder of the theorem's own shadows the name, because
/// Lean includes by variable identity, not by name. The other declaration
/// kinds ignore `include`, as Lean's `removeUnusedVars` does.
///
/// FAIL CLOSED when the scan cannot see everything: a missed identifier would
/// drop a section variable and register the declaration with the WRONG ARITY
/// (measured: `variable {α : Type} (p : α × α)` with `def f : α × α := (p.2,
/// p.1)` once dropped `p`, and every later application failed with
/// `TooManyArguments` — `lean4_corpus_tests::test_r90_discovery_lock`, snippet
/// `sectvar_transitive_incl`). The selection is then every section binder —
/// the context Lean elaborates a definition in — together with a
/// [`SectionPruneRequest`] under which the elaborator drops the ones the
/// elaborated declaration does not use (`crate::infer::section_prune`).
pub(crate) fn select_section_binders(
    section_binders: &[SurfaceBinder],
    decl: &SurfaceDecl,
    macro_ctx: Option<&MacroCtx>,
    forced: &[SurfaceName],
) -> SectionVarSelection {
    if section_binders.is_empty() {
        return SectionVarSelection::default();
    }
    let Some((rule, scan, own_binders)) = scan_decl(decl) else {
        return SectionVarSelection::default();
    };
    if !scan.complete {
        let every = vec![true; section_binders.len()];
        return SectionVarSelection {
            binders: section_binders.to_vec(),
            prune: Some(prune_request(section_binders, &every, rule, forced)),
        };
    }
    let mut used = scan.free;
    if let Some(macro_ctx) = macro_ctx {
        macro_ctx.close_over_simple_notation_dependencies(&mut used);
    }
    // A declaration binder with the same name shadows the section variable —
    // from that binder on. A mention that PRECEDES it in the telescope is the
    // section variable itself (`ScanAcc::before_own_binder`).
    for name in &own_binders {
        if !scan.before_own_binder.contains(name) {
            used.remove(name);
        }
    }
    // A template's reference to a section variable is not shadowed by any
    // binder of the declaration.
    used.extend(scan.template_section);
    let (include, prune) = match rule {
        SectionVarRule::Header => header_selection(section_binders, used, forced),
        SectionVarRule::Used => used_selection(section_binders, used),
    };
    SectionVarSelection {
        binders: section_binders
            .iter()
            .zip(include)
            .filter(|&(_, inc)| inc)
            .map(|(binder, _)| binder.clone())
            .collect(),
        prune,
    }
}

/// The pruning request for the section binders `include` selects, under
/// `rule`'s Lean counterpart.
fn prune_request(
    section_binders: &[SurfaceBinder],
    include: &[bool],
    rule: SectionVarRule,
    forced: &[SurfaceName],
) -> SectionPruneRequest {
    let selected: Vec<&SurfaceBinder> = section_binders
        .iter()
        .zip(include)
        .filter(|&(_, &inc)| inc)
        .map(|(binder, _)| binder)
        .collect();
    let rule = match rule {
        SectionVarRule::Header => PruneRule::Header {
            forced: selected.iter().map(|b| forced.contains(&b.name)).collect(),
        },
        SectionVarRule::Used => PruneRule::Used,
    };
    SectionPruneRequest {
        section_names: selected.iter().map(|b| b.name.clone()).collect(),
        rule,
    }
}

/// The definition rule over a scannable declaration: [`used_rule`]'s choice,
/// together with a request to apply Lean's `removeUnusedVars` to the
/// elaborated declaration whenever that choice holds a variable the
/// declaration does not NAME.
///
/// [`used_rule`] activates an instance-implicit variable whose type mentions a
/// kept variable, because instance resolution in the elaborated value is what
/// brings such a variable in — and the surface cannot see whether resolution
/// did. Lean decides on the elaborated term (`Lean/Elab/MutualDef.lean:593-609`
/// over `Meta.removeUnused`), so an activated instance the value never uses is
/// NOT a parameter there. Measured on the pinned v4.30.0-rc2 (2026-09-20), with
/// `variable {α : Type} [DecidableEq α] {β : Type} [Inhabited β]`:
///
/// * `def konst (a : α) : α := a` is `@konst : {α : Type} → α → α`;
/// * `def both (x : α) (y : β) : α × β := (x, default)` is `{α β : Type} →
///   [Inhabited β] → α → β → α × β`;
/// * `instance : Nonempty (Option α) := ⟨none⟩` is `∀ {α : Type}, Nonempty
///   (Option α)`.
///
/// Kept unconditionally, `[DecidableEq α]` was a parameter of `konst`: `konst
/// x` at a type with no `DecidableEq` instance failed `failed to synthesize
/// instance`, and `@konst Nat 0` was read with `0` in the instance slot. The
/// activated instances (and what only they mention) are still PREPENDED — the
/// value may need them — and `crate::infer::section_prune` then keeps exactly
/// those the elaborated header or value uses. When nothing was activated the
/// named closure is already Lean's answer and nothing is armed.
fn used_selection(
    section_binders: &[SurfaceBinder],
    used: HashSet<SurfaceName>,
) -> (Vec<bool>, Option<SectionPruneRequest>) {
    let mut named_used = used.clone();
    let mut named = vec![false; section_binders.len()];
    close_over_dependencies(section_binders, &mut named_used, &mut named);
    let wide = used_rule(section_binders, used);
    if wide == named {
        return (wide, None);
    }
    let prune = prune_request(section_binders, &wide, SectionVarRule::Used, &[]);
    (wide, Some(prune))
}

/// The theorem rule over a scannable header: Lean's `withHeaderSecVars`
/// ([`header_rule`]) when the surface decides it, else a superset of it
/// together with a request to apply the rule to the elaborated header.
///
/// The surface cannot decide an instance-implicit variable whose type
/// mentions a kept variable and one that is not kept: the elaborated header
/// may name the second through the instance itself (an `outParam` filled by
/// resolution — see the module doc). Measured before this deferral: with
/// `variable {F β : Type} [Get F β]` (`β` an `outParam`), `theorem get_congr
/// (f g : F) (h : f = g) : Get.get f = Get.get g := by rw [h]` was
/// prepended `F` alone and failed `failed to synthesize instance Get fvar#0
/// ?1`, where Lean keeps `{F β} [Get F β]` — and the pre-2026-09-12 rule,
/// which kept every instance mentioning a kept variable, had accepted it.
///
/// The superset is that earlier rule — each instance mentioning a kept
/// variable, and what it mentions, to a fixpoint ([`used_rule`]) — joined with
/// [`header_rule`]'s own choice (an instance mentioning no variable). Lean
/// elaborates the header in the full section context and then applies
/// `withHeaderSecVars` to it (`Lean/Elab/MutualDef.lean:454-490`);
/// `crate::infer::section_prune` applies that same rule to the elaborated
/// statement, so the declaration ends with Lean's telescope unless its proof
/// uses a variable outside it.
fn header_selection(
    section_binders: &[SurfaceBinder],
    used: HashSet<SurfaceName>,
    forced: &[SurfaceName],
) -> (Vec<bool>, Option<SectionPruneRequest>) {
    let exact = header_rule(section_binders, used.clone(), forced);
    let mut seeded = used;
    seeded.extend(forced.iter().cloned());
    let wide: Vec<bool> = used_rule(section_binders, seeded)
        .into_iter()
        .zip(&exact)
        .map(|(w, &e)| w || e)
        .collect();
    if wide == exact {
        return (exact, None);
    }
    let prune = prune_request(section_binders, &wide, SectionVarRule::Header, forced);
    (wide, Some(prune))
}

/// The name the parser gives an anonymous binder (`[Inhabited α]`, `(_ : T)`).
/// No expression can refer to such a binder by it — a `_` in a term is a
/// hole — so it is never evidence that the binder is used.
const ANONYMOUS_BINDER: &str = "_";

/// Whether `binder` is anonymous (see [`ANONYMOUS_BINDER`]).
fn is_anonymous_binder(binder: &SurfaceBinder) -> bool {
    binder.name.is_unescaped_component(ANONYMOUS_BINDER)
}

/// Whether a use of the name `name` reaches `binder`.
fn is_named_use(binder: &SurfaceBinder, used: &HashSet<SurfaceName>) -> bool {
    !is_anonymous_binder(binder) && used.contains(&binder.name)
}

/// Mark every not-yet-included binder whose name is in `used`, adding the
/// free identifiers of its type, until nothing changes — the dependency
/// closure (`CollectFVars.State.addDependencies`): `a : α` pulls in `α`.
///
/// An anonymous binder is never reached by name (see [`is_named_use`]).
/// Every anonymous instance binder is named `_`, so keying the closure on
/// that name made one activated `[C α]` drag in every other anonymous
/// instance of the section and the variables their types mention. Measured:
/// `variable {α : Type} [Inhabited α] {β : Type} [Inhabited β]` with `def
/// dflt (x : α) : α := default` registered the phantom `{β} [Inhabited β]`,
/// and `dflt (3 : Nat)` failed `failed to synthesize instance Inhabited ?3`,
/// where Lean gives `@dflt : {α : Type} → [Inhabited α] → α → α`.
fn close_over_dependencies(
    section_binders: &[SurfaceBinder],
    used: &mut HashSet<SurfaceName>,
    include: &mut [bool],
) {
    loop {
        let mut changed = false;
        for (i, binder) in section_binders.iter().enumerate() {
            if !include[i] && is_named_use(binder, used) {
                include[i] = true;
                changed = true;
                if let Some(ty) = &binder.ty {
                    used.extend(collect_free_idents(ty));
                }
            }
        }
        if !changed {
            break;
        }
    }
}

/// The section variables a binder's type mentions.
fn section_refs<'a>(
    binder: &SurfaceBinder,
    section_names: &HashSet<&'a SurfaceName>,
) -> Vec<&'a SurfaceName> {
    let Some(ty) = &binder.ty else {
        return Vec::new();
    };
    let free = collect_free_idents(ty);
    section_names
        .iter()
        .copied()
        .filter(|n| free.contains(*n))
        .collect()
}

/// Lean's `withHeaderSecVars` (`Lean/Elab/MutualDef.lean:454-490`), over the
/// header's surface identifiers `used`.
fn header_rule(
    section_binders: &[SurfaceBinder],
    mut used: HashSet<SurfaceName>,
    forced: &[SurfaceName],
) -> Vec<bool> {
    // `include`d variables, by identity: added AFTER own-binder shadowing.
    used.extend(forced.iter().cloned());
    let mut include = vec![false; section_binders.len()];
    close_over_dependencies(section_binders, &mut used, &mut include);
    // Instance-implicits whose type mentions only kept variables — one pass in
    // declaration order, with no further dependency step ("by definition they
    // may only reference variables already included", :477-478). `.all` over
    // an empty set holds, so an instance mentioning no variable is kept.
    let section_names: HashSet<&SurfaceName> = section_binders.iter().map(|b| &b.name).collect();
    let mut kept_names: HashSet<&SurfaceName> = section_binders
        .iter()
        .zip(include.iter())
        .filter(|&(_, &inc)| inc)
        .map(|(b, _)| &b.name)
        .collect();
    for (i, binder) in section_binders.iter().enumerate() {
        if include[i] || binder.info != SurfaceBinderInfo::Instance {
            continue;
        }
        if section_refs(binder, &section_names)
            .iter()
            .all(|n| kept_names.contains(n))
        {
            include[i] = true;
            kept_names.insert(&binder.name);
        }
    }
    include
}

/// The surface approximation of Lean's `removeUnusedVars` for definitions:
/// the variables the declaration mentions, closed under dependencies, plus an
/// instance-implicit variable whose type mentions a kept variable (instance
/// resolution in the elaborated value is what brings it in there).
fn used_rule(section_binders: &[SurfaceBinder], mut used: HashSet<SurfaceName>) -> Vec<bool> {
    // The names a section `variable` line BINDS. Instance activation is keyed on
    // these, never on every free identifier.
    //
    // Without this guard, `variable {α : Type} [Tagd α]` followed by
    // `instance : Tagd Nat := ⟨fun n => n + 5⟩` activated `[Tagd α]` —
    // because `Tagd` appears in the instance's own class type and so was
    // "used" — which then pulled in `α` through the dependency step. The
    // instance registered as `∀ {α} [Tagd α], Tagd Nat`, which cannot inhabit
    // `Tagd Nat` without first inhabiting `Tagd α`: the only candidate for the
    // goal was unusable, and every `Tagd Nat` synthesis in the file failed.
    // Upstream Lean binds neither variable here, because the instance mentions
    // neither.
    let section_names: HashSet<&SurfaceName> = section_binders.iter().map(|b| &b.name).collect();
    let mut include = vec![false; section_binders.len()];
    loop {
        close_over_dependencies(section_binders, &mut used, &mut include);
        let mut changed = false;
        for (i, binder) in section_binders.iter().enumerate() {
            if include[i] || binder.info != SurfaceBinderInfo::Instance {
                continue;
            }
            if section_refs(binder, &section_names)
                .iter()
                .any(|n| used.contains(*n))
            {
                include[i] = true;
                changed = true;
                used.insert(binder.name.clone());
                if let Some(ty) = &binder.ty {
                    used.extend(collect_free_idents(ty));
                }
            }
        }
        if !changed {
            break;
        }
    }
    include
}

#[cfg(test)]
#[path = "section_var_selection_tests.rs"]
mod tests;
