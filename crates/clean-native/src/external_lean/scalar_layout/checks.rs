// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use clean_kernel::{BinderInfo, ConstructorVal, Expr, ExprKind, InductiveVal, Level, RecursorVal};

pub(super) fn n(value: &str) -> Name {
    Name::from_string(value)
}
pub(super) fn c(value: &str) -> Expr {
    Expr::const_(n(value), vec![])
}
pub(super) fn pi(domain: Expr, body: Expr) -> Expr {
    Expr::pi(BinderInfo::Default, domain, body)
}
pub(super) fn lam(domain: Expr, body: Expr) -> Expr {
    Expr::lam(BinderInfo::Default, domain, body)
}

pub(super) struct Check<'a, 'program> {
    pub program: &'program ExternalLeanProgram,
    pub context: &'a ReplayedLeanContext<'program>,
    pub replay: &'a ReplayedImportedSource,
    pub limits: ReplayContextLimits,
    pub recursors: &'a [&'program RecursorVal],
    pub budget: &'a RefCell<budget::Budget>,
}
impl<'program> Check<'_, 'program> {
    pub fn expected_type(&self, name: &Name, expected: &Expr) -> Result<(), String> {
        let declaration = self.context.declaration(name).map_err(|e| e.to_string())?;
        self.budget
            .borrow_mut()
            .names(&declaration.constant().level_params)?;
        let levels = vec![Level::zero(); declaration.constant().level_params.len()];
        self.context
            .check_expected_type(&declaration, &levels, expected, self.limits)
            .map_err(|e| format!("{name}: {e}"))
    }
    pub fn equal(&self, left: &Expr, right: &Expr, label: &str) -> Result<(), String> {
        match self.context.definitionally_equal(left, right, self.limits) {
            Ok(true) => Ok(()),
            Ok(false) => Err(format!(
                "{label}: fully checked terms are not definitionally equal"
            )),
            Err(e) => Err(format!("{label}: {e}")),
        }
    }
    pub fn family(
        &self,
        name: &str,
        params: u32,
        indices: u32,
        recursive: bool,
        large: bool,
        constructors: usize,
    ) -> Result<&'program InductiveVal, String> {
        let name = n(name);
        self.context.declaration(&name).map_err(|e| e.to_string())?;
        let ind = self
            .program
            .env
            .get_inductive(&name)
            .ok_or_else(|| format!("{name}: no actual inductive role"))?;
        self.budget.borrow_mut().inductive(ind)?;
        if ind.name != name
            || !ind.level_params.is_empty()
            || ind.num_params != params
            || ind.num_indices != indices
            || ind.all_names != [name.clone()]
            || ind.constructor_names.len() != constructors
            || ind.is_recursive != recursive
            || ind.is_reflexive
            || ind.is_nested
            || ind.is_large_elim != large
        {
            return Err(format!(
                "{name}: unsupported actual inductive metadata: {ind:?}"
            ));
        }
        if self
            .program
            .env
            .get_structure_parents(&name)
            .is_some_and(|p| !p.is_empty())
        {
            return Err(format!("{name}: unexpected structure parents"));
        }
        for (index, ctor_name) in ind.constructor_names.iter().enumerate() {
            let ctor = self.constructor(ctor_name)?;
            if ctor.inductive_name != name
                || ctor.constructor_idx as usize != index
                || ctor.num_params != params
                || !ctor.level_params.is_empty()
            {
                return Err(format!(
                    "{ctor_name}: constructor association/order mismatch"
                ));
            }
        }
        self.recursors(ind)?;
        Ok(ind)
    }
    pub fn constructor(&self, name: &Name) -> Result<&'program ConstructorVal, String> {
        self.context.declaration(name).map_err(|e| e.to_string())?;
        let ctor = self
            .program
            .env
            .get_constructor(name)
            .ok_or_else(|| format!("{name}: no actual constructor role"))?;
        self.budget.borrow_mut().constructor(ctor)?;
        Ok(ctor)
    }
    fn recursors(&self, ind: &InductiveVal) -> Result<(), String> {
        let mut count = 0;
        for rec in self
            .recursors
            .iter()
            .copied()
            .filter(|r| r.inductive_name == ind.name)
        {
            count += 1;
            self.replay
                .require_record(&self.program.env, &rec.name)
                .map_err(|e| e.to_string())?;
            self.replay
                .checked_constant(&rec.name)
                .map_err(|e| e.to_string())?;
            let checked = self
                .replay
                .checked_environment()
                .get_recursor(&rec.name)
                .ok_or_else(|| format!("{}: replay regenerated no recursor", rec.name))?;
            rec.validate_metadata()?;
            if rec.arg_order != checked.arg_order
                || rec.level_params != checked.level_params
                || rec.inductive_name != checked.inductive_name
                || rec.num_params != ind.num_params
                || rec.num_indices != ind.num_indices
                || rec.num_motives != 1
                || rec.num_minors as usize != ind.constructor_names.len()
                || rec.is_k != checked.is_k
                || rec.rules.len() != ind.constructor_names.len()
            {
                return Err(format!(
                    "{}: recursor association/metadata differs from full replay",
                    rec.name
                ));
            }
            for ctor_name in &ind.constructor_names {
                let ctor = self.constructor(ctor_name)?;
                let mut rules = rec
                    .rules
                    .iter()
                    .filter(|r| r.constructor_name == *ctor_name);
                let rule = rules
                    .next()
                    .ok_or_else(|| format!("{}: missing constructor rule", rec.name))?;
                let regenerated = checked
                    .rules
                    .iter()
                    .find(|r| r.constructor_name == *ctor_name)
                    .ok_or_else(|| format!("{}: no regenerated constructor rule", rec.name))?;
                if rules.next().is_some()
                    || rule.num_fields != ctor.num_fields
                    || rule.recursive_fields != regenerated.recursive_fields
                    || rule.recursive_fields.len() != ctor.num_fields as usize
                {
                    return Err(format!(
                        "{}: recursor field/recursion metadata mismatch",
                        rec.name
                    ));
                }
            }
            // ImportedConeGate already compares every actual iota RHS against
            // kernel regeneration, never installing imported rules. Fully
            // validate this actual type again through the closed bounded API.
            {
                let mut work = self.budget.borrow_mut();
                work.names(&rec.level_params)?;
                work.expression(&rec.type_)?;
            }
            let levels = vec![Level::zero(); rec.level_params.len()];
            let closed_type = rec
                .type_
                .instantiate_level_params_direct(&rec.level_params, &levels);
            self.expected_type(&rec.name, &closed_type)?;
        }
        if count == 0 {
            return Err(format!("{}: no actual replay-qualified recursor", ind.name));
        }
        Ok(())
    }
    pub fn projection(
        &self,
        family: &Name,
        field: usize,
        expected_fields: usize,
    ) -> Result<Name, String> {
        let fields = self
            .program
            .env
            .get_structure_field_names(family)
            .ok_or_else(|| format!("{family}: missing original structure field table"))?;
        if fields.len() != expected_fields {
            return Err(format!("{family}: wrong original field count/order"));
        }
        self.budget.borrow_mut().names(fields)?;
        // The actual structure field table is the importer's projection mapping.
        // Constructor identities are always taken from InductiveVal metadata.
        let name = Name::append(family, &fields[field].to_string());
        self.context.declaration(&name).map_err(|e| e.to_string())?;
        self.replay
            .require_record(&self.program.env, &name)
            .map_err(|e| e.to_string())?;
        Ok(name)
    }
    pub fn words(&self) -> Result<[ScalarWordLayoutFacts; 2], (ScalarLayoutStage, String)> {
        Ok([
            self.word(ScalarLayoutWord::U32, 32, "UInt32")?,
            self.word(ScalarLayoutWord::U64, 64, "UInt64")?,
        ])
    }
    fn word(
        &self,
        word: ScalarLayoutWord,
        width: u32,
        family: &str,
    ) -> Result<ScalarWordLayoutFacts, (ScalarLayoutStage, String)> {
        let bound_result = || -> Result<Expr, String> {
            let bv = self
                .program
                .env
                .get_inductive(&n("BitVec"))
                .ok_or("missing BitVec")?;
            let ctor = self.constructor(&bv.constructor_names[0])?;
            let ExprKind::Pi(_, _, body) = ctor.type_.kind() else {
                return Err("BitVec constructor has no width binder".into());
            };
            let closed = body.instantiate(&Expr::nat_lit(u64::from(width)));
            // Full validation precedes observation of this original telescope.
            let closed = self
                .context
                .whnf_closed(&closed, self.limits)
                .map_err(|e| e.to_string())?;
            let ExprKind::Pi(_, payload, _) = closed.kind() else {
                return Err("BitVec constructor has no payload".into());
            };
            let ExprKind::App(head, bound) = payload.kind() else {
                return Err("BitVec payload is not Fin bound".into());
            };
            if head.as_ref() != &c("Fin") {
                return Err("BitVec payload has a different family".into());
            }
            let expected = Expr::nat_lit_u128(1u128 << width);
            self.equal(bound, &expected, "actual closed BitVec bound")?;
            Ok(expected)
        };
        let bound = bound_result().map_err(|e| (ScalarLayoutStage::Bounds, e))?;
        let projection_result = || -> Result<(Name, Name), String> {
            let ind = self
                .program
                .env
                .get_inductive(&n(family))
                .ok_or("missing scalar family")?;
            let projection = self.projection(&ind.name, 0, 1)?;
            self.equal(
                &Expr::const_(projection.clone(), vec![]),
                &lam(c(family), Expr::proj(ind.name.clone(), 0, Expr::bvar(0))),
                "actual word projection",
            )?;
            let bv = n("BitVec");
            let bv_proj = self.projection(&bv, 0, 1)?;
            let bv_ty = Expr::app(c("BitVec"), Expr::nat_lit(u64::from(width)));
            self.equal(
                &Expr::app(
                    Expr::const_(bv_proj, vec![]),
                    Expr::nat_lit(u64::from(width)),
                ),
                &lam(bv_ty, Expr::proj(bv, 0, Expr::bvar(0))),
                "actual BitVec projection",
            )?;
            let fin = n("Fin");
            let val = self.projection(&fin, 0, 2)?;
            let proof = self.projection(&fin, 1, 2)?;
            let fin_ty = Expr::app(c("Fin"), bound.clone());
            self.equal(
                &Expr::app(Expr::const_(val, vec![]), bound.clone()),
                &lam(fin_ty.clone(), Expr::proj(fin.clone(), 0, Expr::bvar(0))),
                "actual Fin value projection",
            )?;
            let proof_type = pi(
                c("Nat"),
                pi(
                    Expr::app(c("Fin"), Expr::bvar(0)),
                    Expr::apps(
                        c("Nat.lt"),
                        [Expr::proj(fin, 0, Expr::bvar(0)), Expr::bvar(1)],
                    ),
                ),
            );
            self.expected_type(&proof, &proof_type)?;
            let info = self
                .program
                .env
                .get_const(&proof)
                .ok_or("missing original proof projection")?;
            if info.kind != clean_kernel::ConstantKind::Theorem
                || info.reducibility != clean_kernel::Reducibility::Opaque
            {
                return Err(
                    "Fin proof projection must retain its original opaque theorem role".into(),
                );
            }
            Ok((ind.constructor_names[0].clone(), projection))
        };
        let (constructor, projection) =
            projection_result().map_err(|e| (ScalarLayoutStage::Projections, e))?;
        Ok(ScalarWordLayoutFacts {
            word,
            family: n(family),
            constructor,
            projection,
            width,
            bound,
        })
    }
}
