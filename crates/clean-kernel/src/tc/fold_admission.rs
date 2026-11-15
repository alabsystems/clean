// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The type checker's side of native-fold authority
//! (`env/native_fold_authority.rs`): every name-keyed reduction asks here
//! before it fires, and the answer is memoized for the checker's lifetime —
//! sound because the checker borrows the environment immutably, so nothing a
//! verdict read can change while the memo lives.

use crate::name::Name;
use crate::tc::TypeChecker;

/// Per-checker memo of the two admission questions a head can be asked.
#[derive(Debug, Default, Clone, Copy)]
pub(crate) struct FoldAdmission {
    /// The environment's FOLD verdict for this name (a `fold` row).
    authority: Option<bool>,
    /// The environment's DEFINITION verdict (a row of any role).
    definition: Option<bool>,
    /// The native-reducer admission: authority, the kernel theory's own rules,
    /// and the authority of every constant the reducer recognizes by name.
    registry: Option<bool>,
    /// Exact list-backed String constructor shape in this immutable environment.
    list_string: Option<bool>,
}

impl FoldAdmission {
    /// Drop the theory-dependent verdict (the checker's theory changed).
    pub(crate) fn forget_registry(&mut self) {
        self.registry = None;
    }
}

/// Memo key for the `Nat` literal-extension check (never a fold key: `Nat`
/// is an inductive type, which [`TypeChecker::fold_admitted`] refuses).
static NAT_LITERAL_KEY: std::sync::LazyLock<Name> =
    std::sync::LazyLock::new(|| Name::from_string("Nat"));

/// Memo key for the cubical layer's admission (never asked as a fold key).
static CUBICAL_LAYER_KEY: std::sync::LazyLock<Name> =
    std::sync::LazyLock::new(|| Name::from_string("<cubical-layer>"));

static STRING_LITERAL_KEY: std::sync::LazyLock<Name> =
    std::sync::LazyLock::new(|| Name::from_string("String"));

#[path = "cubical_authority.rs"]
mod cubical_authority;

impl<'env> TypeChecker<'env> {
    /// Whether a name-keyed fold on `name` may fire here: the environment holds
    /// a definition for it that a `fold` row pins, i.e. one the fold was
    /// reviewed against (`Environment::native_fold_verdict`).
    pub(in crate::tc) fn fold_admitted(&self, name: &Name) -> bool {
        if let Some(known) = self
            .lean_reducer_admission
            .borrow()
            .get(name)
            .and_then(|a| a.authority)
        {
            return known;
        }
        let verdict = self.env.native_fold_authorized(name);
        self.lean_reducer_admission
            .borrow_mut()
            .entry(name.clone())
            .or_default()
            .authority = Some(verdict);
        verdict
    }

    /// Whether `name` is a KNOWN definition here (a row of any role pins its
    /// closure): what a reviewed reducer needs of a constant it recognizes in
    /// its arguments, whose own rules need not fire
    /// (`Environment::native_fold_definition_verdict`).
    pub(in crate::tc) fn definition_admitted(&self, name: &Name) -> bool {
        if let Some(known) = self
            .lean_reducer_admission
            .borrow()
            .get(name)
            .and_then(|a| a.definition)
        {
            return known;
        }
        let verdict = self.env.native_fold_definition_admitted(name);
        self.lean_reducer_admission
            .borrow_mut()
            .entry(name.clone())
            .or_default()
            .definition = Some(verdict);
        verdict
    }

    /// Whether `Nat` is the canonical inductive every `Nat` literal extension
    /// (successor folding, literal ↔ constructor, offset peeling) assumes.
    pub(in crate::tc) fn nat_literal_admitted(&self) -> bool {
        if let Some(known) = self
            .lean_reducer_admission
            .borrow()
            .get(&*NAT_LITERAL_KEY)
            .and_then(|a| a.authority)
        {
            return known;
        }
        let verdict = self.env.nat_literal_extension_canonical();
        self.lean_reducer_admission
            .borrow_mut()
            .entry(NAT_LITERAL_KEY.clone())
            .or_default()
            .authority = Some(verdict);
        verdict
    }

    /// Whether the cubical and directed layers' name-keyed rules may fire:
    /// every reserved head the environment declares is the kernel's own
    /// declaration of it (`tc/cubical_authority.rs`).
    pub(in crate::tc) fn cubical_layer_admitted(&self) -> bool {
        if let Some(known) = self
            .lean_reducer_admission
            .borrow()
            .get(&*CUBICAL_LAYER_KEY)
            .and_then(|a| a.authority)
        {
            return known;
        }
        let verdict = cubical_authority::cubical_primitives_canonical(self.env);
        self.lean_reducer_admission
            .borrow_mut()
            .entry(CUBICAL_LAYER_KEY.clone())
            .or_default()
            .authority = Some(verdict);
        verdict
    }

    /// Whether a literal may expand through the canonical conversion function
    /// or the exact list-backed constructor, with canonical characters.
    pub(in crate::tc) fn string_literal_admitted(&self) -> bool {
        use crate::tc::reduction::names;
        self.nat_literal_admitted()
            && self.fold_admitted(&names::CHAR_OF_NAT)
            && ((self.env.get_const(&names::STRING_OF_LIST).is_some()
                && self.fold_admitted(&names::STRING_OF_LIST))
                || (self.env.get_const(&names::STRING_OF_LIST).is_none()
                    && self.list_backed_string_constructor()))
    }

    /// The legacy representation is an inductive constructor, never a
    /// similarly typed conversion function over a different representation.
    fn list_backed_string_constructor(&self) -> bool {
        if let Some(known) = self
            .lean_reducer_admission
            .borrow()
            .get(&*STRING_LITERAL_KEY)
            .and_then(|admission| admission.list_string)
        {
            return known;
        }
        let admitted = self.list_backed_string_constructor_uncached();
        self.lean_reducer_admission
            .borrow_mut()
            .entry(STRING_LITERAL_KEY.clone())
            .or_default()
            .list_string = Some(admitted);
        admitted
    }

    fn list_backed_string_constructor_uncached(&self) -> bool {
        use crate::expr::{BinderInfo, Expr};
        use crate::level::Level;
        let n = Name::from_string;
        let c = |name| Expr::const_(n(name), vec![]);
        let string = n("String");
        let mk = n("String.mk");
        let list = n("List");
        let nil = n("List.nil");
        let cons = n("List.cons");
        let (Some(s), Some(m), Some(l), Some(z), Some(k)) = (
            self.env.get_inductive(&string),
            self.env.get_constructor(&mk),
            self.env.get_inductive(&list),
            self.env.get_constructor(&nil),
            self.env.get_constructor(&cons),
        ) else {
            return false;
        };
        if !s.level_params.is_empty()
            || s.num_params != 0
            || s.num_indices != 0
            || s.all_names != [string.clone()]
            || s.constructor_names != [mk.clone()]
            || s.type_ != Expr::sort(Level::succ(Level::zero()))
            || m.inductive_name != string
            || !m.level_params.is_empty()
            || m.num_params != 0
            || m.num_fields != 1
            || m.constructor_idx != 0
            || l.level_params.len() != 1
            || l.num_params != 1
            || l.num_indices != 0
            || l.all_names != [list.clone()]
            || l.constructor_names != [nil.clone(), cons.clone()]
            || z.inductive_name != list
            || z.num_params != 1
            || z.num_fields != 0
            || z.constructor_idx != 0
            || k.inductive_name != list
            || k.num_params != 1
            || k.num_fields != 2
            || k.constructor_idx != 1
            || z.level_params != l.level_params
            || k.level_params != l.level_params
        {
            return false;
        }
        let u = Level::param(l.level_params[0].clone());
        let ty = Expr::sort(Level::succ(u.clone()));
        let list_at = |index| {
            Expr::app(
                Expr::const_(list.clone(), vec![u.clone()]),
                Expr::bvar(index),
            )
        };
        let nil_ty = Expr::pi(BinderInfo::Implicit, ty.clone(), list_at(0));
        let cons_ty = Expr::pi(
            BinderInfo::Implicit,
            ty.clone(),
            Expr::pi(
                BinderInfo::Default,
                Expr::bvar(0),
                Expr::pi(BinderInfo::Default, list_at(1), list_at(2)),
            ),
        );
        let mk_ty = Expr::pi(
            BinderInfo::Default,
            Expr::app(Expr::const_(list.clone(), vec![Level::zero()]), c("Char")),
            c("String"),
        );
        l.type_ == Expr::pi(BinderInfo::Default, ty.clone(), ty)
            && z.type_ == nil_ty
            && k.type_ == cons_ty
            && m.type_ == mk_ty
            && [
                (&string, &s.type_),
                (&mk, &m.type_),
                (&list, &l.type_),
                (&nil, &z.type_),
                (&cons, &k.type_),
            ]
            .into_iter()
            .all(|(name, ty)| {
                self.env
                    .get_const(name)
                    .is_some_and(|info| info.type_ == *ty && info.value.is_none())
            })
    }

    pub(in crate::tc) fn expand_admitted_string_literal(&self, text: &str) -> crate::expr::Expr {
        use crate::tc::reduction::{names, string_lit_to_constructor_with_head};
        let head = if self.env.get_const(&names::STRING_OF_LIST).is_some()
            && self.fold_admitted(&names::STRING_OF_LIST)
        {
            names::STRING_OF_LIST.clone()
        } else {
            Name::from_string("String.mk")
        };
        string_lit_to_constructor_with_head(text, head)
    }

    /// Whether one of the kernel's own folds that Lean's kernel does NOT have
    /// may fire on `name`: `reduce_int` (`Int.add`/`Int.sub`/`Int.mul` over a
    /// literal above `u64`), the `Nat.pred` arm of `reduce_nat`, and the
    /// evaluation of `Lean.reduceBool`/`Lean.reduceNat` by whnf.
    ///
    /// THEORY. These folds are compiled into the checker, not registered, so
    /// until 2026-11-12 they asked [`Self::fold_admitted`] alone and fired in
    /// every theory, the reference entry's included, although its `TheoryId`
    /// digests only the fourteen `Nat` heads and the string-literal expansion
    /// (self-proof unit F1, `docs/DECISIONS.md`). Measured on pinned Lean
    /// (`reports/fence-folds-2026-11-12/`): its kernel folds `Nat.add` by name
    /// and only δ-unfolds `Nat.pred` and the three `Int` heads; it evaluates
    /// `Lean.reduceBool c` by running `c`'s compiled code, under the axiom
    /// `Lean.trustCompiler`, which no reference closure may reach. They now
    /// take the registry's rule ([`Self::registry_reducer_admitted`]), one
    /// rule for both kinds of name-keyed computation (a first form of this
    /// gate, landed the same day, special-cased `LeanReference` and left the
    /// `Lean` profile on authority alone; `docs/DECISIONS.md` records why the
    /// two were made one):
    /// `Extended` admits each one native-fold authority admits (a `fold` row
    /// for the arithmetic heads; structurally, for an opaque identity
    /// `Lean.reduce*`, so that evaluation IS reachable in production wherever
    /// the opaque is declared); `LeanReference`
    /// admits none, so the head δ-unfolds like any definition and an opaque
    /// stays stuck; `Lean` applies its differential rule
    /// (`Environment::lean_theory_exclusion`), which lists `Nat.pred` and the
    /// three `Int` heads and neither `Lean.reduce*`.
    pub(in crate::tc) fn hardwired_fold_admitted(&self, name: &Name) -> bool {
        self.registry_reducer_admitted(name)
    }

    /// Whether the registered native reducer for `name` may fire: the kernel
    /// theory admits it, a `fold` row pins `name`'s closure (the reducer was
    /// reviewed against it), and every constant the reducer recognizes by name
    /// in its arguments is a known definition.
    pub(crate) fn registry_reducer_admitted(&self, name: &Name) -> bool {
        if let Some(known) = self
            .lean_reducer_admission
            .borrow()
            .get(name)
            .and_then(|a| a.registry)
        {
            return known;
        }
        let theory_ok = match self.kernel_theory() {
            crate::env::KernelTheory::Extended => true,
            crate::env::KernelTheory::LeanReference => {
                crate::env::Environment::is_lean_kernel_nat_extension(name)
            }
            _ => self.env.lean_theory_exclusion(name).is_none(),
        };
        let admitted = theory_ok
            && self.fold_admitted(name)
            && crate::env::recognized_argument_names(name)
                .iter()
                .all(|r| self.env.get_const(r).is_none() || self.definition_admitted(r));
        self.lean_reducer_admission
            .borrow_mut()
            .entry(name.clone())
            .or_default()
            .registry = Some(admitted);
        admitted
    }
}

#[cfg(test)]
#[path = "fold_admission_tests.rs"]
mod tests;
