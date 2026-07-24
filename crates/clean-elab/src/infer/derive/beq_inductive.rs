// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Field-binding `BEq` body for monomorphic, multi-constructor inductives whose
//! constructors carry fields that do NOT recursively mention the type being
//! defined (e.g. `Shape | circle : Nat -> Shape | rect : Nat -> Nat -> Shape`).
//!
//! The previous `derive_beq_inductive` body compared only the *constructor tag*
//! — its `casesOn` minors were bare `Bool.true`/`Bool.false` with no field
//! binders, which (a) does not even kernel-type-check for fielded ctors (the
//! minor for `circle : Nat -> Shape` must be `(n : Nat) -> motive (circle n)`,
//! not `Bool`) and (b) silently reported `circle 1 == circle 2` as `true`. This
//! module builds minors that BIND each constructor's fields and compare them
//! pairwise via `@BEq.beq fieldTy fieldInst`, so genuinely-different values
//! compare `false`.
//!
//! Recursive fields (a field whose type mentions the inductive itself, directly
//! or through a nested container like `List Ty`) are NOT handled here: a
//! self-referential `@BEq.beq Ty self …` needs structural recursion (brecOn),
//! which a `casesOn`-only construction cannot express. The caller rejects
//! unsupported shapes rather than manufacturing a comparator.

use crate::infer::ElabCtx;
use crate::ElabError;
use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Expr, ExprKind, FVarId, Level};
use clean_parser::SurfaceCtor;

/// The elaborated field types of one constructor, plus whether any field is
/// recursive (mentions the inductive being defined).
pub(super) struct CtorFields {
    pub field_types: Vec<Expr>,
    pub has_recursive_field: bool,
}

impl<'a> ElabCtx<'a> {
    /// Whether EVERY field type across all constructors has a `BEq fieldTy`
    /// instance resolvable to a CLOSED term (no metavariables / free variables).
    ///
    /// The field-binding body emits `@BEq.beq fieldTy fieldInst …`; if any
    /// `fieldInst` can only be a fresh metavariable, the committed instance
    /// would "contain free variables" and the kernel rejects it. The caller
    /// uses this to gate the field-binding path and otherwise fall back —
    /// keeping the produced instance always closed and sound.
    pub(super) fn all_field_beq_instances_closed(&mut self, ctor_fields: &[CtorFields]) -> bool {
        let beq_class = Name::from_string("BEq");
        for cf in ctor_fields {
            for fty in &cf.field_types {
                let goal = Expr::app(self.mk_const(&beq_class), fty.clone());
                match self.resolve_instance(&goal) {
                    Some(inst) if !inst.has_fvar_quick() && !self.has_metavars(&inst) => {}
                    _ => return false,
                }
            }
        }
        true
    }

    /// Elaborate each constructor's surface type under a temporary local for the
    /// inductive name, peel its Pi/arrow telescope, and record the per-field
    /// elaborated types together with a recursive-field flag.
    ///
    /// Returns `None` if any constructor type fails to elaborate (the caller
    /// then conservatively falls back), keeping this path total.
    pub(super) fn collect_ctor_fields(
        &mut self,
        ind_name: &Name,
        ctors: &[SurfaceCtor],
    ) -> Option<Vec<CtorFields>> {
        // Push a temporary local so the inductive name resolves while
        // elaborating constructor field types. `Type 0` is the right kind for
        // the monomorphic inductives this path targets.
        let local_name = ind_name
            .to_string()
            .rsplit('.')
            .next()
            .unwrap_or("")
            .to_string();
        let ind_sort = Expr::sort(Level::succ(Level::zero()));
        let ind_fvar = self.push_local(local_name, ind_sort);

        let mut out = Vec::with_capacity(ctors.len());
        let mut ok = true;
        for ctor in ctors {
            let Ok(ctor_ty) = self.elaborate(&ctor.ty) else {
                ok = false;
                break;
            };
            let mut field_types = Vec::new();
            let mut has_recursive_field = false;
            let mut curr = ctor_ty;
            // Peel the field telescope; each Pi domain is a field type.
            while let ExprKind::Pi(_, domain, body) = curr.kind() {
                let dom = domain.as_ref().clone();
                if expr_mentions_fvar(&dom, ind_fvar) {
                    has_recursive_field = true;
                }
                field_types.push(dom);
                // Field telescopes for non-dependent ctors don't bind the domain
                // in the body in a way we use; instantiate with the fvar to keep
                // the body closed for the next peel.
                curr = body.as_ref().instantiate(&Expr::fvar(ind_fvar));
            }
            out.push(CtorFields {
                field_types,
                has_recursive_field,
            });
        }

        self.pop_local(); // ind_fvar
        if ok {
            Some(out)
        } else {
            None
        }
    }

    /// Build the field-binding `BEq` comparison body for a monomorphic,
    /// multi-constructor inductive with NO recursive fields.
    ///
    /// Produced term (inside the outer `λ (a b : Ind)`):
    /// ```text
    /// Ind.casesOn.{1} (λ _ : Ind => Bool) a
    ///   (λ a_f… => Ind.casesOn.{1} (λ _ : Ind => Bool) b
    ///                 (λ b_f… => <compare a_f vs b_f | false>) …)
    ///   …
    /// ```
    /// All field binders are introduced as fresh fvars and abstracted back into
    /// the minor lambdas, so de Bruijn indices need no manual bookkeeping.
    pub(super) fn build_beq_inductive_body(
        &mut self,
        ind_name: &Name,
        ind_type: &Expr,
        ctor_names: &[Name],
        ctor_fields: &[CtorFields],
        a_ref: &Expr,
        b_ref: &Expr,
    ) -> Result<Expr, ElabError> {
        let motive_u = Level::succ(Level::zero());
        let cases_on_name = Name::from_string(&format!("{ind_name}.casesOn"));
        let bool_type = Expr::const_(Name::from_string("Bool"), vec![]);
        let bool_false = Expr::const_(Name::from_string("Bool.false"), vec![]);
        // Motive `λ _ : Ind => Bool` (shared by outer and inner casesOn).
        let motive = Expr::lam(BinderInfo::Default, ind_type.clone(), bool_type);

        let mut outer_minors = Vec::with_capacity(ctor_names.len());
        for (i, fields_i) in ctor_fields.iter().enumerate() {
            // Fresh fvars for a's fields under ctor i.
            let a_fvars: Vec<FVarId> = fields_i
                .field_types
                .iter()
                .map(|_| self.fresh_fvar())
                .collect();

            // Inner casesOn over b.
            let mut inner_minors = Vec::with_capacity(ctor_names.len());
            for (j, fields_j) in ctor_fields.iter().enumerate() {
                let b_fvars: Vec<FVarId> = fields_j
                    .field_types
                    .iter()
                    .map(|_| self.fresh_fvar())
                    .collect();

                // Minor body: compare fields when i == j, else `false`.
                let mut minor_body = if i == j {
                    self.build_field_eq_chain(&fields_i.field_types, &a_fvars, &b_fvars)?
                } else {
                    bool_false.clone()
                };

                // λ (b_f : T) … => minor_body  (abstract innermost-first).
                for k in (0..b_fvars.len()).rev() {
                    minor_body = minor_body.abstract_fvar(b_fvars[k]);
                    minor_body = Expr::lam(
                        BinderInfo::Default,
                        fields_j.field_types[k].clone(),
                        minor_body,
                    );
                }
                inner_minors.push(minor_body);
            }

            // Ind.casesOn.{1} motive b inner_minor…
            // Lean-faithful casesOn order: motive, (indices,) major, then minors.
            let mut inner = Expr::app(
                Expr::const_(cases_on_name.clone(), vec![motive_u.clone()]),
                motive.clone(),
            );
            inner = Expr::app(inner, b_ref.clone());
            for m in inner_minors {
                inner = Expr::app(inner, m);
            }

            // λ (a_f : T) … => inner  (abstract innermost-first).
            let mut outer_minor = inner;
            for k in (0..a_fvars.len()).rev() {
                outer_minor = outer_minor.abstract_fvar(a_fvars[k]);
                outer_minor = Expr::lam(
                    BinderInfo::Default,
                    fields_i.field_types[k].clone(),
                    outer_minor,
                );
            }
            outer_minors.push(outer_minor);
        }

        // Ind.casesOn.{1} motive a outer_minor…
        // Lean-faithful casesOn order: motive, (indices,) major, then minors.
        let mut outer = Expr::app(Expr::const_(cases_on_name, vec![motive_u]), motive);
        outer = Expr::app(outer, a_ref.clone());
        for m in outer_minors {
            outer = Expr::app(outer, m);
        }
        Ok(outer)
    }

    /// `(@BEq.beq T₀ i₀ a₀ b₀) && … && (@BEq.beq T_{k-1} i_{k-1} a_{k-1} b_{k-1})`
    /// over the field fvars, or `Bool.true` when there are no fields.
    fn build_field_eq_chain(
        &mut self,
        field_types: &[Expr],
        a_fvars: &[FVarId],
        b_fvars: &[FVarId],
    ) -> Result<Expr, ElabError> {
        if field_types.is_empty() {
            return Ok(Expr::const_(Name::from_string("Bool.true"), vec![]));
        }
        let bool_and = Name::from_string("Bool.and");
        let mut acc: Option<Expr> = None;
        for (k, fty) in field_types.iter().enumerate() {
            let cmp =
                self.build_field_beq_eq(fty, Expr::fvar(a_fvars[k]), Expr::fvar(b_fvars[k]))?;
            acc = Some(match acc {
                None => cmp,
                Some(prev) => {
                    Expr::app(Expr::app(Expr::const_(bool_and.clone(), vec![]), prev), cmp)
                }
            });
        }
        Ok(acc.expect("nonempty field list produced a comparison"))
    }

    /// `@BEq.beq fieldTy fieldInst a b` with the field's `[BEq fieldTy]`
    /// instance resolved to a closed term. Missing instances are typed derive
    /// errors; automatic deriving never substitutes an unresolved metavariable.
    fn build_field_beq_eq(&mut self, field_ty: &Expr, a: Expr, b: Expr) -> Result<Expr, ElabError> {
        let beq_class = Name::from_string("BEq");
        let beq_field_ty = Expr::app(self.mk_const(&beq_class), field_ty.clone());
        let field_inst =
            self.resolve_instance(&beq_field_ty)
                .ok_or_else(|| ElabError::Unsupported {
                    feature: format!(
                        "deriving BEq cannot synthesize a closed field instance for `{field_ty:?}`"
                    ),
                })?;
        let beq_beq = self.mk_const_str("BEq.beq");
        Ok(Expr::app(
            Expr::app(
                Expr::app(Expr::app(beq_beq, field_ty.clone()), field_inst),
                a,
            ),
            b,
        ))
    }
}

/// Whether `expr` references the free variable `id` anywhere.
fn expr_mentions_fvar(expr: &Expr, id: FVarId) -> bool {
    // `abstract_fvar` rewrites iff the fvar occurs; structural (interned)
    // equality is then false. Cheap and dependency-free.
    expr.abstract_fvar(id) != *expr
}
