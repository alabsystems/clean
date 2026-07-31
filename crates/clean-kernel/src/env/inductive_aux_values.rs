// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Definitional VALUES for the generated auxiliary eliminators
//! (`casesOn` / `recOn`) — the Lean-parity reordering wrappers over `.rec`.
//!
//! In Lean 4, `T.casesOn` and `T.recOn` are ordinary value-bearing
//! DEFINITIONS whose bodies delegate to the primitive recursor `T.rec`; the
//! kernel closes `casesOn … stuck-major ≡ rec … stuck-major` by plain delta
//! unfolding. Clean historically registered its generated aux eliminators as
//! value-less recursor-table entries: iota fired on constructor-headed
//! majors, but a VARIABLE-scrutinee `casesOn` application was permanently
//! stuck — so every Lean-elaborated equation lemma comparing a matcher
//! spelling (`casesOn`) against a `rec` spelling failed its re-check (the
//! `List.tail.eq_1` / `*.match_1.eq_N` / `filter_singleton` type_mismatch
//! class, residual-to-zero campaign 2026-07-02).
//!
//! This module builds the missing values. The aux eliminator type layout is
//!
//! ```text
//! aux : params → motives → indices → major → minors → motive indices major
//! rec : params → motives → minors' → indices → major → motive indices major
//! ```
//!
//! so the value is the telescope-reordering wrapper
//!
//! ```text
//! aux := λ params motives indices major minors ⇒
//!            rec params motives minors' indices major
//! ```
//!
//! where for `recOn` the minors pass through verbatim (identical premise
//! types), and for `casesOn` each minor is eta-adapted to the rec premise by
//! absorbing-and-dropping the induction hypotheses:
//! `minor'_i = λ fields ihs ⇒ minor_i fields`.
//!
//! ## Soundness
//!
//! Attaching these values is a COMPLETENESS improvement, never a relaxation:
//! delta-unfolding a definition is the kernel's own standard reduction, and
//! the values are exactly the wrappers whose iota behaviour the existing
//! rule-table entries already implement (`casesOn (ctor …)` reduces to the
//! same branch through either path — pinned in tests). In debug builds every
//! generated value is additionally `check_type`-verified against the
//! generated eliminator type at `add_inductive` time.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{ConstantKind, EnvError, Environment};
use crate::expr::{BinderInfo, Expr, ExprKind};
use crate::inductive::{InductiveError, RecursorArgOrder};
use crate::level::Level;
use crate::name::Name;
use crate::tc::TypeChecker;

/// A binder captured while walking a Pi telescope with fresh locals.
struct WalkedBinder {
    id: crate::expr::FVarId,
    fvar: Expr,
    info: BinderInfo,
    /// Domain type as instantiated over the previously-created fvars.
    domain: Expr,
}

/// Strip one Pi from `cur`, materializing its binder as a fresh local.
fn walk_one(b: &mut EnvDeclBuilder, cur: &mut Expr, who: &Name) -> Result<WalkedBinder, EnvError> {
    let ExprKind::Pi(data, domain, body) = &cur.kind else {
        return Err(EnvError::Inductive(InductiveError::InvalidType(format!(
            "aux-eliminator value builder for {who}: telescope shorter than \
             the recursor arity counts (expected another Pi binder)"
        ))));
    };
    let domain = domain.as_ref().clone();
    let info = data.info;
    let (id, fvar) = b.fresh_local(domain.clone());
    *cur = body.instantiate(&fvar);
    Ok(WalkedBinder {
        id,
        fvar,
        info,
        domain,
    })
}

impl Environment {
    /// Build the definitional value for a generated aux eliminator.
    ///
    /// `minor_arities` selects the flavour:
    /// - `Some(arities)` — `casesOn`: per-minor `(num_fields, num_ihs)` of the
    ///   UNDERLYING `rec` premise; each aux minor (no IH binders) is
    ///   eta-adapted by absorbing the rec premise's fields+IHs and applying
    ///   the aux minor to the fields only.
    /// - `None` — `recOn`: aux minors have the rec premise types verbatim and
    ///   pass straight through.
    ///
    /// REQUIRES: `aux_ty` has layout params→motives→indices→major→minors and
    /// `rec_ty` has layout params→motives→minors→indices→major, over the SAME
    /// `level_params` (both derive `[motive_univ?] ++ decl.level_params`
    /// identically in the callers).
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn build_aux_eliminator_value(
        &self,
        aux_name: &Name,
        rec_name: &Name,
        level_params: &[Name],
        aux_ty: &Expr,
        rec_ty: &Expr,
        num_params: u32,
        num_motives: u32,
        num_indices: u32,
        num_minors: usize,
        minor_arities: Option<&[(u32, u32)]>,
    ) -> Result<Expr, EnvError> {
        let mut b = EnvDeclBuilder::new();

        // ── Walk the aux telescope: params, motives, indices, major, minors ──
        let mut cur = aux_ty.clone();
        let walk_n = |b: &mut EnvDeclBuilder,
                      cur: &mut Expr,
                      n: usize|
         -> Result<Vec<WalkedBinder>, EnvError> {
            (0..n).map(|_| walk_one(b, cur, aux_name)).collect()
        };
        let params = walk_n(&mut b, &mut cur, num_params as usize)?;
        let motives = walk_n(&mut b, &mut cur, num_motives as usize)?;
        let indices = walk_n(&mut b, &mut cur, num_indices as usize)?;
        let major = walk_one(&mut b, &mut cur, aux_name)?;
        let minors = walk_n(&mut b, &mut cur, num_minors)?;

        // ── Walk the rec telescope with the SAME param/motive fvars, reading
        // off the rec minor premise types (needed to type the casesOn
        // adapters; instantiating with the shared fvars makes them concrete
        // expressions over this builder's locals). ──
        let mut rcur = rec_ty.clone();
        for w in params.iter().chain(motives.iter()) {
            let ExprKind::Pi(_, _, body) = &rcur.kind else {
                return Err(EnvError::Inductive(InductiveError::InvalidType(format!(
                    "aux-eliminator value builder for {aux_name}: recursor \
                         telescope shorter than params+motives"
                ))));
            };
            rcur = body.instantiate(&w.fvar);
        }
        let mut rec_minor_types = Vec::with_capacity(num_minors);
        for _ in 0..num_minors {
            let ExprKind::Pi(_, domain, body) = &rcur.kind else {
                return Err(EnvError::Inductive(InductiveError::InvalidType(format!(
                    "aux-eliminator value builder for {aux_name}: recursor \
                         telescope shorter than its minor count"
                ))));
            };
            rec_minor_types.push(domain.as_ref().clone());
            // Minor premises are non-dependent on one another, but keep the
            // telescope walk uniform: no later domain references this binder,
            // so instantiating with the (unused) aux minor fvar is exact.
            let placeholder = minors
                .get(rec_minor_types.len() - 1)
                .map(|w| w.fvar.clone())
                .unwrap_or_else(|| Expr::bvar(0));
            rcur = body.instantiate(&placeholder);
        }

        // ── Build the rec-side minors ──
        let rec_minors: Vec<Expr> = match minor_arities {
            // recOn: identical premise types — pass the bound minors through.
            None => minors.iter().map(|w| w.fvar.clone()).collect(),
            // casesOn: eta-adapt each minor to the rec premise, dropping IHs.
            Some(arities) => {
                if arities.len() != num_minors {
                    return Err(EnvError::Inductive(InductiveError::InvalidType(format!(
                        "aux-eliminator value builder for {aux_name}: \
                             {} minor arities for {num_minors} minors",
                        arities.len()
                    ))));
                }
                let mut adapted = Vec::with_capacity(num_minors);
                for (i, ((num_fields, num_ihs), minor)) in
                    arities.iter().zip(minors.iter()).enumerate()
                {
                    let total = (*num_fields + *num_ihs) as usize;
                    let mut cb = EnvDeclBuilder::child_of(&b);
                    let mut mcur = rec_minor_types[i].clone();
                    let bound: Vec<WalkedBinder> = (0..total)
                        .map(|_| walk_one(&mut cb, &mut mcur, aux_name))
                        .collect::<Result<_, _>>()?;
                    // Apply the aux minor to the FIELDS only (IHs dropped).
                    let mut body = minor.fvar.clone();
                    for w in bound.iter().take(*num_fields as usize) {
                        body = Expr::app(body, w.fvar.clone());
                    }
                    for w in bound.iter().rev() {
                        body = cb.mk_lam(w.id, w.info, w.domain.clone(), body);
                    }
                    adapted.push(cb.finish_child(body));
                }
                adapted
            }
        };

        // ── rec params motives minors' indices major ──
        let rec_levels: Vec<Level> = level_params.iter().cloned().map(Level::param).collect();
        let rec_const = Expr::const_(rec_name.clone(), rec_levels);
        let mut app = rec_const;
        for w in params.iter().chain(motives.iter()) {
            app = Expr::app(app, w.fvar.clone());
        }
        for m in rec_minors {
            app = Expr::app(app, m);
        }
        for w in indices.iter() {
            app = Expr::app(app, w.fvar.clone());
        }
        app = Expr::app(app, major.fvar.clone());

        // ── Close the aux telescope (innermost minors first). ──
        let mut value = app;
        for w in minors.iter().rev() {
            value = b.mk_lam(w.id, w.info, w.domain.clone(), value);
        }
        value = b.mk_lam(major.id, major.info, major.domain.clone(), value);
        for w in indices.iter().rev() {
            value = b.mk_lam(w.id, w.info, w.domain.clone(), value);
        }
        for w in motives.iter().rev() {
            value = b.mk_lam(w.id, w.info, w.domain.clone(), value);
        }
        for w in params.iter().rev() {
            value = b.mk_lam(w.id, w.info, w.domain.clone(), value);
        }
        Ok(b.finish(value))
    }

    /// Authenticate an imported `casesOn` definition against the canonical
    /// checked wrapper over its primitive `.rec` packet.
    ///
    /// A value-bearing constant with the right eliminator type is not enough:
    /// the match compiler relies on the name computing by the canonical
    /// constructor rules. This routine rebuilds exactly the wrapper used for
    /// native inductives, checks both bodies against the imported declaration,
    /// and requires definitional equality with the imported value. The
    /// underlying recursor is independently authenticated, including every
    /// rule's subject-reduction obligation.
    ///
    /// `minor_arities` must be the complete global minor order obtained from
    /// authenticated member/companion recursor packets. Each pair is
    /// `(num_fields, num_recursive_fields)` for one primitive-rec minor.
    pub fn authenticate_cases_on_wrapper_readonly(
        &self,
        cases_name: &Name,
        rec_name: &Name,
        minor_arities: &[(u32, u32)],
    ) -> Result<(), String> {
        self.authenticate_recursor_readonly(rec_name)?;
        let rec = self
            .get_recursor(rec_name)
            .ok_or_else(|| format!("missing primitive recursor `{rec_name}`"))?;
        if rec.arg_order != RecursorArgOrder::MajorAfterMinors {
            return Err(format!(
                "primitive recursor `{rec_name}` has {:?} layout, but canonical `casesOn` wrapping requires MajorAfterMinors",
                rec.arg_order
            ));
        }
        if minor_arities.len() != rec.num_minors as usize {
            return Err(format!(
                "canonical `casesOn` wrapper for `{cases_name}` received {} minor arities, but `{rec_name}` declares {}",
                minor_arities.len(),
                rec.num_minors
            ));
        }

        let cases = self
            .get_const(cases_name)
            .ok_or_else(|| format!("missing imported cases eliminator `{cases_name}`"))?;
        if cases.name != *cases_name {
            return Err(format!(
                "cases eliminator registry key `{cases_name}` contains declaration `{}`",
                cases.name
            ));
        }
        if cases.kind != ConstantKind::Definition || cases.value.is_none() {
            return Err(format!(
                "imported cases eliminator `{cases_name}` is not a value-bearing definition"
            ));
        }
        if cases.level_params != rec.level_params {
            return Err(format!(
                "imported cases eliminator `{cases_name}` universe parameters disagree with `{rec_name}`"
            ));
        }

        let canonical = self
            .build_aux_eliminator_value(
                cases_name,
                rec_name,
                &cases.level_params,
                &cases.type_,
                &rec.type_,
                rec.num_params,
                rec.num_motives,
                rec.num_indices,
                rec.num_minors as usize,
                Some(minor_arities),
            )
            .map_err(|error| {
                format!("failed to reconstruct canonical cases eliminator `{cases_name}`: {error}")
            })?;
        let value = cases
            .value
            .as_ref()
            .expect("value-bearing cases eliminator checked above");
        let tc = TypeChecker::new(self);
        tc.check_type(&canonical, &cases.type_).map_err(|error| {
            format!(
                "canonical cases eliminator `{cases_name}` does not inhabit its imported type: {error:?}"
            )
        })?;
        tc.check_type(value, &cases.type_).map_err(|error| {
            format!(
                "imported cases eliminator `{cases_name}` does not inhabit its declaration: {error:?}"
            )
        })?;
        if !tc.is_def_eq(value, &canonical) {
            return Err(format!(
                "imported cases eliminator `{cases_name}` is not definitionally equal to the canonical `{rec_name}` wrapper"
            ));
        }
        Ok(())
    }
}

#[cfg(test)]
mod aux_value_tests {
    use crate::env::Environment;
    use crate::expr::{BinderInfo, Expr};
    use crate::level::Level;
    use crate::name::Name;
    use crate::tc::TypeChecker;

    fn n(s: &str) -> Name {
        Name::from_string(s)
    }

    /// The generated casesOn/recOn VALUES type-check against their eliminator
    /// types in every build profile (the debug-assertions check in
    /// `add_inductive_impl` covers debug builds only). `Eq.casesOn`/`Eq.recOn`
    /// come through the core_eq REPAIR pass (which rebuilds the promoted
    /// singleton types and re-attaches the wrapper values), so they are pinned
    /// here explicitly too.
    #[test]
    fn test_generated_aux_values_type_check() {
        let env = Environment::with_prelude();
        for name in [
            "List.casesOn",
            "List.recOn",
            "Bool.casesOn",
            "Nat.recOn",
            "Eq.casesOn",
            "Eq.recOn",
        ] {
            let ci = env
                .get_const(&n(name))
                .unwrap_or_else(|| panic!("{name} registered"));
            let value = ci
                .value
                .as_ref()
                .unwrap_or_else(|| panic!("{name} must carry its definitional value"));
            let tc = TypeChecker::new(&env);
            tc.check_type(value, &ci.type_)
                .unwrap_or_else(|e| panic!("{name} value must check: {e:?}"));
        }
    }

    /// COMPLETENESS pin (residual-to-zero campaign, 2026-07-02): a
    /// VARIABLE-scrutinee `casesOn` application is definitionally equal to the
    /// corresponding `rec` application — closed by delta-unfolding the
    /// generated value, exactly as Lean's kernel closes it. This is the
    /// equation-lemma/matcher class (`List.tail.eq_1`, `*.match_1.eq_N`,
    /// `filter_singleton`): matcher spellings elaborate to `casesOn`, Clean
    /// prelude stubs spell `rec`, and before this fix the two could never
    /// converge on a stuck major premise.
    #[test]
    fn test_stuck_cases_on_converges_with_rec() {
        let mut env = Environment::with_prelude();
        {
            let nat = Expr::const_(n("Nat"), vec![]);
            let list_nat = Expr::app(Expr::const_(n("List"), vec![Level::zero()]), nat);
            env.add_decl(crate::env::Declaration::Axiom {
                name: n("auxValueTestStuckList"),
                level_params: vec![],
                type_: list_nat,
            })
            .expect("stuck-scrutinee axiom registers");
        }
        let tc = TypeChecker::new(&env);

        let nat = Expr::const_(n("Nat"), vec![]);
        let list_nat = Expr::app(Expr::const_(n("List"), vec![Level::zero()]), nat.clone());
        // Stuck major premise: an opaque axiom of type List Nat (no value,
        // not a constructor — permanently stuck, like a bound variable).
        let x = Expr::const_(n("auxValueTestStuckList"), vec![]);

        // motive := fun (_ : List Nat) => Nat
        let motive = Expr::lam(BinderInfo::Default, list_nat.clone(), nat.clone());
        // nil branch := 0 ; cons branch (casesOn form, no IH) := fun a as => 0
        let zero = Expr::const_(n("Nat.zero"), vec![]);
        let cons_case_cases = Expr::lam(
            BinderInfo::Default,
            nat.clone(),
            Expr::lam(BinderInfo::Default, list_nat.clone(), zero.clone()),
        );
        // cons branch (rec form, with IH) := fun a as ih => 0
        let cons_case_rec = Expr::lam(
            BinderInfo::Default,
            nat.clone(),
            Expr::lam(
                BinderInfo::Default,
                list_nat.clone(),
                Expr::lam(BinderInfo::Default, nat.clone(), zero.clone()),
            ),
        );

        // List.casesOn.{1,0}? — casesOn levels: [motive_univ, u]; Nat lives at
        // Level 1 motive? motive returns Nat : Type 0 → motive univ = 1.
        let cases = Expr::apps(
            Expr::const_(
                n("List.casesOn"),
                vec![Level::succ(Level::zero()), Level::zero()],
            ),
            [
                nat.clone(),
                motive.clone(),
                x.clone(),
                zero.clone(),
                cons_case_cases,
            ],
        );
        let rec_ = Expr::apps(
            Expr::const_(
                n("List.rec"),
                vec![Level::succ(Level::zero()), Level::zero()],
            ),
            [nat.clone(), motive, zero.clone(), cons_case_rec, x.clone()],
        );
        assert!(
            tc.is_def_eq(&cases, &rec_),
            "stuck-scrutinee casesOn must delta-converge with the rec spelling"
        );

        // ADVERSARIAL: swapping the branch payloads must stay rejected.
        let one = Expr::app(Expr::const_(n("Nat.succ"), vec![]), zero.clone());
        let motive2 = Expr::lam(BinderInfo::Default, list_nat.clone(), nat.clone());
        let cases_zero_branch = Expr::apps(
            Expr::const_(
                n("List.casesOn"),
                vec![Level::succ(Level::zero()), Level::zero()],
            ),
            [
                nat.clone(),
                motive2.clone(),
                x.clone(),
                zero.clone(),
                Expr::lam(
                    BinderInfo::Default,
                    nat.clone(),
                    Expr::lam(BinderInfo::Default, list_nat.clone(), zero.clone()),
                ),
            ],
        );
        let cases_one_branch = Expr::apps(
            Expr::const_(
                n("List.casesOn"),
                vec![Level::succ(Level::zero()), Level::zero()],
            ),
            [
                nat.clone(),
                motive2,
                x.clone(),
                one.clone(),
                Expr::lam(
                    BinderInfo::Default,
                    nat.clone(),
                    Expr::lam(BinderInfo::Default, list_nat.clone(), one.clone()),
                ),
            ],
        );
        assert!(
            !tc.is_def_eq(&cases_zero_branch, &cases_one_branch),
            "stuck casesOn with different branches must stay unequal"
        );
    }

    /// Iota regression: the constructor-head fast path (rule-table reduction)
    /// still fires — `Bool.casesOn motive true t f` reduces to `t` without
    /// needing the new value.
    #[test]
    fn test_cases_on_iota_fast_path_still_fires() {
        let env = Environment::with_prelude();
        let tc = TypeChecker::new(&env);
        let nat = Expr::const_(n("Nat"), vec![]);
        let bool_ = Expr::const_(n("Bool"), vec![]);
        let zero = Expr::const_(n("Nat.zero"), vec![]);
        let one = Expr::app(Expr::const_(n("Nat.succ"), vec![]), zero.clone());
        let motive = Expr::lam(BinderInfo::Default, bool_.clone(), nat.clone());
        let app = Expr::apps(
            Expr::const_(n("Bool.casesOn"), vec![Level::succ(Level::zero())]),
            [
                motive,
                Expr::const_(n("Bool.true"), vec![]),
                zero.clone(),
                one.clone(),
            ],
        );
        let reduced = tc.whnf(&app);
        assert!(
            tc.is_def_eq(&reduced, &one),
            "Bool.casesOn true must reduce to the true branch, got {reduced:?}"
        );
    }
}
