// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! AyBackend term construction, assertion, and quantifier helpers.

#[cfg(test)]
use super::triggers::AyTriggerPattern;
use super::{bignat_to_bigint, AyBackend, AyResult, AyTerm};
use ay::{Model, Sort, Term};
use ay_translate::ops;

impl AyBackend {
    fn wrap_term(term: Term) -> AyTerm {
        AyTerm::from_inner(term)
    }

    fn raw_terms(terms: &[AyTerm]) -> Vec<Term> {
        terms.iter().map(|term| term.into_inner()).collect()
    }
    // =========================================================================
    // Variable declaration
    // =========================================================================

    /// Declare a fresh boolean variable
    pub fn fresh_bool(&mut self, name_hint: &str) -> AyTerm {
        Self::wrap_term(self.session().fresh_const(name_hint, Sort::Bool))
    }

    /// Declare a fresh integer variable
    pub fn fresh_int(&mut self, name_hint: &str) -> AyTerm {
        Self::wrap_term(self.session().fresh_const(name_hint, Sort::Int))
    }

    /// Declare a fresh real variable
    pub fn fresh_real(&mut self, name_hint: &str) -> AyTerm {
        Self::wrap_term(self.session().fresh_const(name_hint, Sort::Real))
    }

    /// Declare a fresh bitvector variable
    pub fn fresh_bv(&mut self, name_hint: &str, width: u32) -> AyTerm {
        Self::wrap_term(self.session().fresh_const(name_hint, Sort::bitvec(width)))
    }

    // =========================================================================
    // Constant constructors
    // =========================================================================

    /// Create a boolean constant
    pub fn bool_const(&mut self, value: bool) -> AyTerm {
        Self::wrap_term(self.session().bool_const(value))
    }

    /// Create an integer constant
    pub fn int_const(&mut self, value: i64) -> AyTerm {
        Self::wrap_term(self.session().int_const(value))
    }

    /// Create an integer constant from a Nat literal (arbitrary precision).
    pub fn int_const_nat(&mut self, value: &clean_kernel::expr::BigNat) -> AyTerm {
        let term = match value.to_u64().and_then(|v| i64::try_from(v).ok()) {
            Some(v) => self.session().int_const(v),
            None => {
                let bigint = bignat_to_bigint(value);
                self.solver.int_const_bigint(&bigint)
            }
        };
        Self::wrap_term(term)
    }

    /// Create a real constant
    #[allow(deprecated)] // try_real_const not yet available in ay-dpll
    pub fn real_const(&mut self, value: f64) -> AyTerm {
        Self::wrap_term(self.solver.real_const(value))
    }

    /// Create a bitvector constant
    pub fn bv_const(&mut self, value: i64, width: u32) -> AyTerm {
        Self::wrap_term(self.session().bv_const(value, width))
    }

    // =========================================================================
    // Boolean operations (using ay-translate ops)
    // =========================================================================

    /// Create logical AND
    pub fn and(&mut self, a: AyTerm, b: AyTerm) -> AyTerm {
        Self::wrap_term(ops::bool_nary(
            &mut self.session(),
            ops::NaryBoolOp::And,
            &[a.into_inner(), b.into_inner()],
        ))
    }

    /// Create logical AND of multiple terms
    pub fn and_many(&mut self, terms: &[AyTerm]) -> AyTerm {
        let terms = Self::raw_terms(terms);
        Self::wrap_term(ops::bool_nary(
            &mut self.session(),
            ops::NaryBoolOp::And,
            &terms,
        ))
    }

    /// Create logical OR
    pub fn or(&mut self, a: AyTerm, b: AyTerm) -> AyTerm {
        Self::wrap_term(ops::bool_nary(
            &mut self.session(),
            ops::NaryBoolOp::Or,
            &[a.into_inner(), b.into_inner()],
        ))
    }

    /// Create logical OR of multiple terms
    pub fn or_many(&mut self, terms: &[AyTerm]) -> AyTerm {
        let terms = Self::raw_terms(terms);
        Self::wrap_term(ops::bool_nary(
            &mut self.session(),
            ops::NaryBoolOp::Or,
            &terms,
        ))
    }

    /// Create logical NOT
    pub fn not(&mut self, a: AyTerm) -> AyTerm {
        Self::wrap_term(ops::bool_not(&mut self.session(), a.into_inner()))
    }

    /// Create logical implication (a => b)
    pub fn implies(&mut self, a: AyTerm, b: AyTerm) -> AyTerm {
        Self::wrap_term(ops::implies(
            &mut self.session(),
            a.into_inner(),
            b.into_inner(),
        ))
    }

    /// Create if-then-else
    pub fn ite(&mut self, cond: AyTerm, then_val: AyTerm, else_val: AyTerm) -> AyTerm {
        Self::wrap_term(ops::ite(
            &mut self.session(),
            cond.into_inner(),
            then_val.into_inner(),
            else_val.into_inner(),
        ))
    }

    // =========================================================================
    // Equality and comparison (using ay-translate ops)
    // =========================================================================

    /// Create equality (a = b)
    pub fn eq(&mut self, a: AyTerm, b: AyTerm) -> AyTerm {
        Self::wrap_term(ops::compare(
            &mut self.session(),
            ops::Comparison::Eq,
            a.into_inner(),
            b.into_inner(),
        ))
    }

    /// Create disequality (a != b)
    pub fn neq(&mut self, a: AyTerm, b: AyTerm) -> AyTerm {
        Self::wrap_term(ops::compare(
            &mut self.session(),
            ops::Comparison::Ne,
            a.into_inner(),
            b.into_inner(),
        ))
    }

    /// Create less-than (a < b)
    pub fn lt(&mut self, a: AyTerm, b: AyTerm) -> AyTerm {
        Self::wrap_term(ops::compare(
            &mut self.session(),
            ops::Comparison::Lt,
            a.into_inner(),
            b.into_inner(),
        ))
    }

    /// Create less-than-or-equal (a <= b)
    pub fn le(&mut self, a: AyTerm, b: AyTerm) -> AyTerm {
        Self::wrap_term(ops::compare(
            &mut self.session(),
            ops::Comparison::Le,
            a.into_inner(),
            b.into_inner(),
        ))
    }

    /// Create greater-than (a > b)
    pub fn gt(&mut self, a: AyTerm, b: AyTerm) -> AyTerm {
        Self::wrap_term(ops::compare(
            &mut self.session(),
            ops::Comparison::Gt,
            a.into_inner(),
            b.into_inner(),
        ))
    }

    /// Create greater-than-or-equal (a >= b)
    pub fn ge(&mut self, a: AyTerm, b: AyTerm) -> AyTerm {
        Self::wrap_term(ops::compare(
            &mut self.session(),
            ops::Comparison::Ge,
            a.into_inner(),
            b.into_inner(),
        ))
    }

    // =========================================================================
    // Arithmetic operations (using ay-translate ops::arith)
    // =========================================================================

    /// Create addition (a + b)
    pub fn add(&mut self, a: AyTerm, b: AyTerm) -> AyTerm {
        Self::wrap_term(ops::arith::add(
            &mut self.session(),
            a.into_inner(),
            b.into_inner(),
        ))
    }

    /// Create subtraction (a - b)
    pub fn sub(&mut self, a: AyTerm, b: AyTerm) -> AyTerm {
        Self::wrap_term(ops::arith::sub(
            &mut self.session(),
            a.into_inner(),
            b.into_inner(),
        ))
    }

    /// Create multiplication (a * b)
    pub fn mul(&mut self, a: AyTerm, b: AyTerm) -> AyTerm {
        Self::wrap_term(ops::arith::mul(
            &mut self.session(),
            a.into_inner(),
            b.into_inner(),
        ))
    }

    /// Create negation (-a)
    pub fn neg(&mut self, a: AyTerm) -> AyTerm {
        Self::wrap_term(ops::arith::neg(&mut self.session(), a.into_inner()))
    }

    /// Create integer division (a div b)
    pub fn int_div(&mut self, a: AyTerm, b: AyTerm) -> AyTerm {
        Self::wrap_term(ops::arith::int_div(
            &mut self.session(),
            a.into_inner(),
            b.into_inner(),
        ))
    }

    /// Create modulo (a mod b)
    pub fn modulo(&mut self, a: AyTerm, b: AyTerm) -> AyTerm {
        Self::wrap_term(ops::arith::modulo(
            &mut self.session(),
            a.into_inner(),
            b.into_inner(),
        ))
    }

    // =========================================================================
    // Bitvector operations (using ay-translate ops::bv)
    // =========================================================================

    /// Create bitvector addition
    pub fn bvadd(&mut self, a: AyTerm, b: AyTerm) -> AyTerm {
        Self::wrap_term(ops::bv::add(
            &mut self.session(),
            a.into_inner(),
            b.into_inner(),
        ))
    }

    /// Create bitvector subtraction
    pub fn bvsub(&mut self, a: AyTerm, b: AyTerm) -> AyTerm {
        Self::wrap_term(ops::bv::sub(
            &mut self.session(),
            a.into_inner(),
            b.into_inner(),
        ))
    }

    /// Create bitvector multiplication
    pub fn bvmul(&mut self, a: AyTerm, b: AyTerm) -> AyTerm {
        Self::wrap_term(ops::bv::binop(
            &mut self.session(),
            ops::bv::BinOp::Mul,
            a.into_inner(),
            b.into_inner(),
        ))
    }

    /// Create bitvector unsigned less-than
    pub fn bvult(&mut self, a: AyTerm, b: AyTerm) -> AyTerm {
        Self::wrap_term(ops::bv::cmp(
            &mut self.session(),
            ops::bv::Cmp::ULt,
            a.into_inner(),
            b.into_inner(),
        ))
    }

    /// Create bitvector signed less-than
    pub fn bvslt(&mut self, a: AyTerm, b: AyTerm) -> AyTerm {
        Self::wrap_term(ops::bv::cmp(
            &mut self.session(),
            ops::bv::Cmp::SLt,
            a.into_inner(),
            b.into_inner(),
        ))
    }

    // =========================================================================
    // Array operations (using ay-translate ops::array)
    // =========================================================================

    /// Declare a fresh array variable with the given index and element sorts
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn fresh_array(
        &mut self,
        name_hint: &str,
        index_sort: Sort,
        element_sort: Sort,
    ) -> AyTerm {
        Self::wrap_term(
            self.session()
                .fresh_const(name_hint, Sort::array(index_sort, element_sort)),
        )
    }

    /// Array store: `(store array index value)` — returns a new array with `array[index] = value`
    pub fn store(&mut self, array: AyTerm, index: AyTerm, value: AyTerm) -> AyTerm {
        Self::wrap_term(ops::array::store(
            &mut self.session(),
            array.into_inner(),
            index.into_inner(),
            value.into_inner(),
        ))
    }

    /// Array select: `(select array index)` — reads `array[index]`
    pub fn select(&mut self, array: AyTerm, index: AyTerm) -> AyTerm {
        Self::wrap_term(ops::array::select(
            &mut self.session(),
            array.into_inner(),
            index.into_inner(),
        ))
    }

    /// Constant array: every index maps to `value`, with index sort `index_sort`
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn const_array(&mut self, index_sort: Sort, value: AyTerm) -> AyTerm {
        Self::wrap_term(ops::array::const_array(
            &mut self.session(),
            index_sort,
            value.into_inner(),
        ))
    }

    // =========================================================================
    // Quantifier operations with triggers
    // =========================================================================

    /// Create a universally quantified formula: `(forall ((x S) ...) body)`
    ///
    /// # Arguments
    ///
    /// * `vars` - Bound variables (must be variables created with `fresh_*` methods)
    /// * `body` - The formula body (must have Bool sort)
    ///
    /// # Contract
    ///
    /// REQUIRES: All `vars` are valid ay variable terms from this solver
    /// REQUIRES: `body` has Bool sort
    /// ENSURES: Result has Bool sort
    /// ENSURES: Triggers are auto-selected by the solver
    pub fn forall(&mut self, vars: &[AyTerm], body: AyTerm) -> AyResult<AyTerm> {
        let vars = Self::raw_terms(vars);
        self.solver
            .try_forall(&vars, body.into_inner())
            .map(Self::wrap_term)
            .map_err(Self::map_quantifier_error)
    }

    /// Create a universally quantified formula with explicit trigger patterns
    ///
    /// Triggers control E-matching instantiation: when the E-graph contains
    /// a ground term matching a trigger pattern, the quantifier is instantiated.
    ///
    /// # Arguments
    ///
    /// * `vars` - Bound variables
    /// * `body` - The formula body
    /// * `triggers` - Trigger patterns (outer slice = pattern groups, inner slice = multi-patterns)
    ///
    /// # Contract
    ///
    /// REQUIRES: All `vars` are valid ay variable terms from this solver
    /// REQUIRES: `body` has Bool sort
    /// REQUIRES: Each trigger pattern contains at least one bound variable
    /// ENSURES: Result has Bool sort
    /// ENSURES: Exactly the provided triggers are used (no auto-selection)
    #[cfg(test)]
    pub(crate) fn forall_with_triggers(
        &mut self,
        vars: &[AyTerm],
        body: AyTerm,
        triggers: &[AyTriggerPattern],
    ) -> AyResult<AyTerm> {
        let vars = Self::raw_terms(vars);
        let trigger_refs = Self::convert_triggers(triggers);
        let trigger_slices: Vec<&[Term]> = trigger_refs.iter().map(|v| v.as_slice()).collect();
        self.solver
            .try_forall_with_triggers(&vars, body.into_inner(), &trigger_slices)
            .map(Self::wrap_term)
            .map_err(Self::map_quantifier_error)
    }

    /// Create an existentially quantified formula: `(exists ((x S) ...) body)`
    ///
    /// # Arguments
    ///
    /// * `vars` - Bound variables (must be variables created with `fresh_*` methods)
    /// * `body` - The formula body (must have Bool sort)
    ///
    /// # Contract
    ///
    /// REQUIRES: All `vars` are valid ay variable terms from this solver
    /// REQUIRES: `body` has Bool sort
    /// ENSURES: Result has Bool sort
    /// ENSURES: Triggers are auto-selected by the solver
    pub fn exists(&mut self, vars: &[AyTerm], body: AyTerm) -> AyResult<AyTerm> {
        let vars = Self::raw_terms(vars);
        self.solver
            .try_exists(&vars, body.into_inner())
            .map(Self::wrap_term)
            .map_err(Self::map_quantifier_error)
    }

    /// Create an existentially quantified formula with explicit trigger patterns
    ///
    /// See [`Self::forall_with_triggers`] for trigger pattern semantics.
    ///
    /// # Contract
    ///
    /// REQUIRES: All `vars` are valid ay variable terms from this solver
    /// REQUIRES: `body` has Bool sort
    /// REQUIRES: Each trigger pattern contains at least one bound variable
    /// ENSURES: Result has Bool sort
    /// ENSURES: Exactly the provided triggers are used (no auto-selection)
    #[cfg(test)]
    pub(crate) fn exists_with_triggers(
        &mut self,
        vars: &[AyTerm],
        body: AyTerm,
        triggers: &[AyTriggerPattern],
    ) -> AyResult<AyTerm> {
        let vars = Self::raw_terms(vars);
        let trigger_refs = Self::convert_triggers(triggers);
        let trigger_slices: Vec<&[Term]> = trigger_refs.iter().map(|v| v.as_slice()).collect();
        self.solver
            .try_exists_with_triggers(&vars, body.into_inner(), &trigger_slices)
            .map(Self::wrap_term)
            .map_err(Self::map_quantifier_error)
    }

    /// Convert AyTriggerPatterns to the format expected by ay-dpll
    ///
    /// # Contract
    ///
    /// ENSURES: Each inner Vec contains the terms from the corresponding AyTriggerPattern
    /// ENSURES: Empty patterns are included (ay handles them as no-op)
    #[cfg(test)]
    pub(crate) fn convert_triggers(triggers: &[AyTriggerPattern]) -> Vec<Vec<Term>> {
        triggers
            .iter()
            .map(|pattern| Self::raw_terms(&pattern.terms))
            .collect()
    }

    // =========================================================================
    // Assertion and solving (using TranslationSession)
    // =========================================================================

    /// Assert a constraint
    pub fn assert_term(&mut self, term: AyTerm) {
        self.clear_last_consumer_sat();
        self.session().assert_term(term.into_inner());
    }

    /// Push a new scope for incremental solving
    pub fn push(&mut self) {
        self.clear_last_consumer_sat();
        self.session().push();
    }

    /// Pop the most recent scope
    pub fn pop(&mut self) {
        self.clear_last_consumer_sat();
        self.session().pop();
    }

    /// Get the model from the last consumer-accepted SAT result.
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn get_model(&mut self) -> Option<Model> {
        if !self.last_consumer_sat {
            return None;
        }
        self.solver.model().map(|vm| vm.into_inner())
    }
}
