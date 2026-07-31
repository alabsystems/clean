// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Type mapping: Isabelle [`IsaType`] → Lean type surface text, plus the
//! schematic-type-variable → greek-letter map and a bottom-up
//! [`term_type`] used by the fragment guards (e.g. `size` renders to `.length`
//! only when its argument is a `List`, `sup`/`inf` render to `∪`/`∩` only over
//! `Set`).

use std::collections::BTreeMap;

use super::super::isabelle_pure::{IsaTerm, IsaType};
use super::types::Unsupported;

/// The ten greek letters standard Isabelle schematic type variables (`'a`…`'j`)
/// map to. Beyond this range the type is declined ([`Unsupported::
/// UnrenderableType`]) rather than guessed.
const GREEK: [&str; 10] = ["α", "β", "γ", "δ", "ε", "ζ", "η", "θ", "ι", "κ"];

/// The schematic/free type-variable → greek-letter binding for one theorem,
/// keyed by the Isabelle type-var base name (`'a`, `'b`, …). Assignment is by
/// the letter itself (`'a`→α, `'b`→β), so the map is order-independent and
/// reproduces the batch's `{α β γ : Type*}` binder exactly.
#[derive(Debug, Clone, Default)]
pub struct TyCtx {
    map: BTreeMap<String, &'static str>,
}

impl TyCtx {
    /// Record a type-var name, assigning it a greek letter. Idempotent.
    ///
    /// # Errors
    /// [`Unsupported::UnrenderableType`] if the name is outside `'a…'j`.
    pub fn intern(&mut self, tvar: &str) -> Result<&'static str, Unsupported> {
        if let Some(g) = self.map.get(tvar) {
            return Ok(g);
        }
        let g = greek_for(tvar).ok_or_else(|| Unsupported::UnrenderableType(tvar.to_string()))?;
        self.map.insert(tvar.to_string(), g);
        Ok(g)
    }

    /// The greek letters in use, in greek order (α, β, γ, …) — the type-binder
    /// group order the batch emits.
    #[must_use]
    pub fn greeks_in_order(&self) -> Vec<&'static str> {
        let mut v: Vec<&'static str> = self.map.values().copied().collect();
        v.sort_unstable_by_key(|g| GREEK.iter().position(|x| x == g).unwrap_or(usize::MAX));
        v.dedup();
        v
    }

    /// Whether any type variable is in play (drives whether a `{… : Type*}`
    /// binder is emitted at all).
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.map.is_empty()
    }
}

/// The greek letter for a `'a`-style type-var name, or `None` if out of range.
fn greek_for(tvar: &str) -> Option<&'static str> {
    let bare = tvar.strip_prefix('\'').unwrap_or(tvar);
    let mut chars = bare.chars();
    let (Some(c), None) = (chars.next(), chars.next()) else {
        return None; // multi-char / empty → out of the supported range
    };
    if c.is_ascii_lowercase() {
        GREEK.get((c as u8 - b'a') as usize).copied()
    } else {
        None
    }
}

/// Render an [`IsaType`] to Lean surface text, interning any type variables into
/// `tcx`.
///
/// # Errors
/// [`Unsupported::UnrenderableType`] for an unmapped type former or an
/// out-of-range type variable.
pub fn render_type(ty: &IsaType, tcx: &mut TyCtx) -> Result<String, Unsupported> {
    match ty {
        IsaType::TVar { n, .. } | IsaType::TFree { n } => Ok(tcx.intern(n)?.to_string()),
        IsaType::Type { n, a } => render_type_ctor(n, a, tcx),
    }
}

/// Render a type constructor `n` applied to arguments `a`.
fn render_type_ctor(n: &str, a: &[IsaType], tcx: &mut TyCtx) -> Result<String, Unsupported> {
    match (n, a.len()) {
        ("Nat.nat", 0) => Ok("ℕ".to_string()),
        ("Int.int", 0) => Ok("ℤ".to_string()),
        ("HOL.bool", 0) => Ok("Bool".to_string()),
        ("List.list", 1) => Ok(format!("List {}", paren_type_arg(&a[0], tcx)?)),
        ("Set.set", 1) => Ok(format!("Set {}", paren_type_arg(&a[0], tcx)?)),
        ("Multiset.multiset", 1) => Ok(format!("Multiset {}", paren_type_arg(&a[0], tcx)?)),
        ("fun", 2) => {
            let dom = render_type(&a[0], tcx)?;
            let cod = render_type(&a[1], tcx)?;
            // `→` is right-associative; parenthesize only a function-typed
            // domain so `(α → β) → γ` stays faithful.
            let dom = if matches!(&a[0], IsaType::Type { n, .. } if n == "fun") {
                format!("({dom})")
            } else {
                dom
            };
            Ok(format!("{dom} → {cod}"))
        }
        _ => Err(Unsupported::UnrenderableType(format!("{n}/{}", a.len()))),
    }
}

/// Render a type as the argument of a type constructor, wrapping a compound
/// (applied) type in parentheses so `List (Set α)` etc. stay well-formed.
fn paren_type_arg(ty: &IsaType, tcx: &mut TyCtx) -> Result<String, Unsupported> {
    let s = render_type(ty, tcx)?;
    let compound = matches!(ty, IsaType::Type { a, .. } if !a.is_empty());
    Ok(if compound { format!("({s})") } else { s })
}

/// Bottom-up result type of an Isabelle term: `Const`/`Free`/`Var` carry their
/// type; an application reduces the function type's codomain; an abstraction
/// builds a function type. `Bound` variables have no locally-known type
/// (`None`). Used only by fragment guards — never trusted for correctness, only
/// to *decline* an ambiguous shape.
#[must_use]
pub fn term_type(t: &IsaTerm) -> Option<IsaType> {
    match t {
        IsaTerm::Const { t, .. } | IsaTerm::Free { t, .. } | IsaTerm::Var { t, .. } => {
            Some(t.clone())
        }
        IsaTerm::App { f, .. } => match term_type(f)? {
            IsaType::Type { n, a } if n == "fun" && a.len() == 2 => Some(a[1].clone()),
            _ => None,
        },
        IsaTerm::Abs { t, b, .. } => Some(IsaType::Type {
            n: "fun".to_string(),
            a: vec![t.clone(), term_type(b)?],
        }),
        IsaTerm::Bound { .. } => None,
    }
}

/// Whether a term's result type is the list type `List.list _`.
#[must_use]
pub fn is_list_typed(t: &IsaTerm) -> bool {
    matches!(term_type(t), Some(IsaType::Type { n, .. }) if n == "List.list")
}

/// Whether a term's result type is the set type `Set.set _`.
#[must_use]
pub fn is_set_typed(t: &IsaTerm) -> bool {
    matches!(term_type(t), Some(IsaType::Type { n, .. }) if n == "Set.set")
}

/// Whether a **type** (not a term) is the set type `Set.set _`. Used to guard the
/// nullary lattice constants (`bot`/`top`) — which carry no argument to inspect —
/// on their *own* (already-instantiated) head-constant type.
#[must_use]
pub fn is_set_type(ty: &IsaType) -> bool {
    matches!(ty, IsaType::Type { n, .. } if n == "Set.set")
}

/// Whether a term's result type is a set **of sets** (`Set.set [Set.set _]`) —
/// the `Set`-instance carrier of the complete-lattice `Sup`/`Inf` (where
/// `Sup :: 'a set ⇒ 'a` specializes to `(β set) set ⇒ β set` = `⋃`/`sSup`).
#[must_use]
pub fn is_set_of_sets(t: &IsaTerm) -> bool {
    matches!(term_type(t), Some(IsaType::Type { n, a }) if n == "Set.set" && a.len() == 1
        && matches!(&a[0], IsaType::Type { n: inner, .. } if inner == "Set.set"))
}

/// Whether a term's result type is exactly `ℕ` (`Nat.nat`). Guards `gcd`/`lcm`,
/// which render to `Nat.gcd`/`Nat.lcm` only on the `ℕ` instance (Lean's
/// `Int.gcd : ℤ → ℤ → ℕ` changes the result type off `ℕ`).
#[must_use]
pub fn is_nat_typed(t: &IsaTerm) -> bool {
    matches!(term_type(t), Some(IsaType::Type { n, a }) if a.is_empty() && n == "Nat.nat")
}

/// Whether a term's result type is a *concrete* (variable-free head) numeric
/// type Lean orders unambiguously (`ℕ`, `ℤ`, `ℚ`, `ℝ`). Bare type variables and
/// unknown formers are excluded so [`crate::hol::isabelle_lean_goal`] declines
/// order comparisons whose Lean order class is not statement-determined.
#[must_use]
pub fn is_concrete_ordered(t: &IsaTerm) -> bool {
    matches!(
        term_type(t),
        Some(IsaType::Type { n, a }) if a.is_empty()
            && matches!(n.as_str(), "Nat.nat" | "Int.int" | "Rat.rat" | "Real.real")
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    fn ty(n: &str, a: Vec<IsaType>) -> IsaType {
        IsaType::Type {
            n: n.to_string(),
            a,
        }
    }

    #[test]
    fn greek_map_covers_abc_and_declines_beyond() {
        let mut tcx = TyCtx::default();
        assert_eq!(tcx.intern("'a").unwrap(), "α");
        assert_eq!(tcx.intern("'b").unwrap(), "β");
        assert_eq!(tcx.intern("'a").unwrap(), "α", "idempotent");
        assert!(matches!(
            tcx.intern("'aa"),
            Err(Unsupported::UnrenderableType(_))
        ));
    }

    #[test]
    fn renders_list_and_fun_and_nat() {
        let mut tcx = TyCtx::default();
        assert_eq!(render_type(&ty("Nat.nat", vec![]), &mut tcx).unwrap(), "ℕ");
        let la = ty(
            "List.list",
            vec![IsaType::TVar {
                n: "'a".into(),
                i: 0,
            }],
        );
        assert_eq!(render_type(&la, &mut tcx).unwrap(), "List α");
        let f = ty(
            "fun",
            vec![
                IsaType::TVar {
                    n: "'a".into(),
                    i: 0,
                },
                ty("HOL.bool", vec![]),
            ],
        );
        assert_eq!(render_type(&f, &mut tcx).unwrap(), "α → Bool");
    }

    #[test]
    fn term_type_reduces_application() {
        // (append : list → list → list) xs  ⇒  list → list
        let list = ty(
            "List.list",
            vec![IsaType::TVar {
                n: "'a".into(),
                i: 0,
            }],
        );
        let app_ty = ty(
            "fun",
            vec![list.clone(), ty("fun", vec![list.clone(), list.clone()])],
        );
        let xs = IsaTerm::Var {
            n: "xs".into(),
            i: 0,
            t: list.clone(),
        };
        let app = IsaTerm::App {
            f: Box::new(IsaTerm::Const {
                n: "List.append".into(),
                t: app_ty,
            }),
            a: Box::new(xs),
        };
        assert!(matches!(term_type(&app), Some(IsaType::Type { n, .. }) if n == "fun"));
    }
}
