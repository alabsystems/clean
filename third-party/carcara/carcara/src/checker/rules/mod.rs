use super::{
    error::{CheckerError, EqualityError},
    ContextStack,
};
use crate::{
    ast::{
        alpha_equiv, polyeq, pool::TermPool, rare_rules::Rules, Operator, ProofCommand, Rc, Term,
    },
    utils::{Range, TypeName},
};
use std::time::Duration;

pub type RuleResult = Result<(), CheckerError>;

pub type Rule = fn(RuleArgs) -> RuleResult;

pub struct RuleArgs<'a> {
    pub(super) conclusion: &'a [Rc<Term>],
    pub(super) premises: &'a [Premise<'a>],
    pub(super) args: &'a [Rc<Term>],
    pub(super) pool: &'a mut dyn TermPool,
    pub(super) context: &'a mut ContextStack,
    pub(super) rare_rules: &'a Rules,

    // For rules that end a subproof, we need to pass the previous command in the subproof that it
    // is closing, because it may be implicitly referenced, and it is not given as premises. If a
    // rule is not ending a subproof, this should be `None`.
    pub(super) previous_command: Option<Premise<'a>>,
    pub(super) discharge: &'a [&'a ProofCommand],

    pub(super) polyeq_time: &'a mut Duration,
}

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub struct Premise<'a> {
    pub id: &'a str,
    pub clause: &'a [Rc<Term>],
    pub index: (usize, usize),
}

impl<'a> Premise<'a> {
    pub fn new(index: (usize, usize), command: &'a ProofCommand) -> Self {
        Self {
            id: command.id(),
            clause: command.clause(),
            index,
        }
    }
}

/// Helper function to get a single term from a premise, or return a
/// `CheckerError::WrongLengthOfPremiseClause` error if it doesn't succeed.
fn get_premise_term<'a>(premise: &Premise<'a>) -> Result<&'a Rc<Term>, CheckerError> {
    match premise.clause {
        [t] => Ok(t),
        cl => Err(CheckerError::WrongLengthOfPremiseClause(
            premise.id.to_owned(),
            1.into(),
            cl.len(),
        )),
    }
}

/// Asserts that the first argument is true, and returns the error specified by the second argument
/// otherwise.
macro_rules! rassert {
    ($arg:expr, $err:expr $(,)?) => {
        match $arg {
            true => Ok(()),
            false => Err($err),
        }?
    };
}

fn assert_num_premises<T: Into<Range>>(premises: &[Premise], range: T) -> RuleResult {
    let range = range.into();
    if !range.contains(premises.len()) {
        return Err(CheckerError::WrongNumberOfPremises(range, premises.len()));
    }
    Ok(())
}

fn assert_clause_len<T: Into<Range>>(clause: &[Rc<Term>], range: T) -> RuleResult {
    let range = range.into();
    if !range.contains(clause.len()) {
        return Err(CheckerError::WrongLengthOfClause(range, clause.len()));
    }
    Ok(())
}

// Modified in Clean: the first literal of a step's conclusion, or an error for the empty clause.
// Rules that read `conclusion[0]` without first checking the clause length panicked (index out of
// bounds) on a step concluding `(cl)`; this keeps their verdict on every non-empty conclusion (see
// third-party/carcara/DOWNSTREAM.md, "Malformed steps are refused, not a panic").
fn first_conclusion_literal(conclusion: &[Rc<Term>]) -> Result<&Rc<Term>, CheckerError> {
    conclusion
        .first()
        .ok_or(CheckerError::WrongLengthOfClause((1..).into(), 0))
}

fn assert_num_args<T: Into<Range>>(args: &[Rc<Term>], range: T) -> RuleResult {
    let range = range.into();
    if !range.contains(args.len()) {
        return Err(CheckerError::WrongNumberOfArgs(range, args.len()));
    }
    Ok(())
}

fn assert_operation_len<T: Into<Range>>(op: Operator, args: &[Rc<Term>], range: T) -> RuleResult {
    let range = range.into();
    if !range.contains(args.len()) {
        return Err(CheckerError::WrongNumberOfTermsInOp(op, range, args.len()));
    }
    Ok(())
}

fn assert_eq<T>(a: &T, b: &T) -> RuleResult
where
    T: Eq + Clone + TypeName,
    EqualityError<T>: Into<CheckerError>,
{
    if a != b {
        return Err(EqualityError::ExpectedEqual(a.clone(), b.clone()).into());
    }
    Ok(())
}

fn assert_is_expected<T>(got: &T, expected: T) -> RuleResult
where
    T: Eq + Clone + TypeName,
    EqualityError<T>: Into<CheckerError>,
{
    if *got != expected {
        return Err(EqualityError::ExpectedToBe { expected, got: got.clone() }.into());
    }
    Ok(())
}

fn assert_polyeq(a: &Rc<Term>, b: &Rc<Term>, time: &mut Duration) -> Result<(), CheckerError> {
    if !polyeq(a, b, time) {
        return Err(EqualityError::ExpectedEqual(a.clone(), b.clone()).into());
    }
    Ok(())
}

fn assert_polyeq_expected(got: &Rc<Term>, expected: Rc<Term>, time: &mut Duration) -> RuleResult {
    if !polyeq(got, &expected, time) {
        return Err(EqualityError::ExpectedToBe { expected, got: got.clone() }.into());
    }
    Ok(())
}

// Modified in Clean: added for `arrays_ext`, which now compares modulo renaming of the witness
// variable (see third-party/carcara/DOWNSTREAM.md).
fn assert_alpha_equiv(a: &Rc<Term>, b: &Rc<Term>, time: &mut Duration) -> RuleResult {
    if !alpha_equiv(a, b, time) {
        return Err(EqualityError::ExpectedEqual(a.clone(), b.clone()).into());
    }
    Ok(())
}

fn assert_alpha_equiv_expected(
    got: &Rc<Term>,
    expected: Rc<Term>,
    time: &mut Duration,
) -> RuleResult {
    if !alpha_equiv(got, &expected, time) {
        return Err(EqualityError::ExpectedToBe { expected, got: got.clone() }.into());
    }
    Ok(())
}

fn assert_is_bool_constant(got: &Rc<Term>, expected: bool) -> RuleResult {
    if !got.is_bool_constant(expected) {
        return Err(CheckerError::ExpectedBoolConstant(expected, got.clone()));
    }
    Ok(())
}

// Since the rule submodules use the `rassert!` macro, we have to declare them here, after the
// macro is declared
pub(super) mod arrays;
pub(super) mod bitvectors;
// Added in Clean: separately versioned, bounded scalar offset-spine checking.
pub(super) mod bv_offset_spines;
// Added in Clean: exact version-one constant-array reads.
pub(super) mod array_const_select;
// Added in Clean: explicit version-one full-width reconstruction.
pub(super) mod bv_reconstruct;
pub(super) mod clausification;
pub(super) mod congruence;
pub(super) mod cutting_planes;
// Modified in Clean: the Clean-authored datatype rules (see third-party/carcara/DOWNSTREAM.md, C2).
pub(super) mod datatypes;
pub(super) mod drup;
pub(super) mod extras;
pub(super) mod linear_arithmetic;
pub(super) mod pb_blasting;
pub(super) mod polynomial;
pub(super) mod quantifier;
pub(super) mod rare;
pub(super) mod reflexivity;
pub(super) mod resolution;
pub(super) mod simplification;
pub(super) mod strings;
pub(super) mod subproof;
pub(super) mod tautology;
pub(super) mod transitivity;
