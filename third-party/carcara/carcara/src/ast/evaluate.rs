use super::{
    pool::{StepTerms, TermPool},
    Constant, Operator, ParamOperator, Rc, Term,
};
use crate::checker::{
    budget::{integer_words, rational_words, ExpansionBudget},
    error::CheckerError,
};
use rug::{Integer, Rational};
use std::collections::{HashMap, HashSet};

/// A representation of the value of an SMT-LIB/Alethe term.
///
/// This is constructed by evaluating a term (see [`Rc::<Term>::evaluate`]).
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Value {
    /// A boolean value.
    Bool(bool),

    /// An integer value.
    Integer(Integer),

    /// A real value.
    Real(Rational),

    /// A string value.
    String(String),

    /// A bitvector value, represented by its integer value and width.
    BitVec(Integer, usize),
}

impl Value {
    /// Constructs a value from a [`Constant`].
    pub fn from_constant(c: Constant) -> Option<Self> {
        match c {
            Constant::Integer(i) => Some(Value::Integer(i)),
            Constant::Real(r) => Some(Value::Real(r)),
            Constant::String(s) => Some(Value::String(s)),
            Constant::RegLan(_, _) => None,
            // Modified in Clean: SMT-LIB `(_ bv<n> <w>)` denotes `n mod 2^w`, so a literal whose
            // value does not fit in `w` bits is *not* that value. Taking `val` as written made
            // `evaluate` report `(= (_ bv5 2) #b01)` as `false` and `(bvult #b10 (_ bv5 2))` as
            // `true` (see third-party/carcara/DOWNSTREAM.md).
            Constant::BitVec(val, width) => Value::new_bitvec(val, width),
        }
    }

    /// Tries to construct a value from a term, return `None` if it is not possible.
    pub fn from_term(t: &Rc<Term>) -> Option<Self> {
        match t.as_ref() {
            Term::Const(c) => Value::from_constant(c.clone()),
            Term::Op(Operator::True, _) => Some(Value::Bool(true)),
            Term::Op(Operator::False, _) => Some(Value::Bool(false)),
            _ => None,
        }
    }

    /// Constructs a new bitvector value, truncating the integer `value` to `width` bits, and
    /// ensuring it is non-negative.
    ///
    /// Modified in Clean: returns `None` for a width above [`MAX_EVALUATED_BV_WIDTH`]. The width
    /// was cast to `u32` (`keep_bits(width as u32)`), so a width of `2^32 + k` reduced the value
    /// modulo `2^k`: `evaluate` proved `(= (= ((_ sign_extend 4294967295) #b1) ((_ sign_extend
    /// 4294967295) #b0)) true)`, both sides reading as the width-0 value `0`. Every bit-vector
    /// value the evaluator builds goes through here, so every width it later computes with is at
    /// most the bound, and the index casts below it are exact (fix 35, see
    /// third-party/carcara/DOWNSTREAM.md).
    pub fn new_bitvec(value: Integer, width: usize) -> Option<Self> {
        if width > MAX_EVALUATED_BV_WIDTH {
            return None;
        }
        Some(Self::BitVec(value.keep_bits(width as u32), width))
    }

    /// Tries to extract a `bool` from the value.
    pub fn as_bool(&self) -> Option<bool> {
        match self {
            Value::Bool(b) => Some(*b),
            _ => None,
        }
    }

    /// Tries to extract an [`Integer`] from the value.
    pub fn as_int(&self) -> Option<Integer> {
        match self {
            Value::Integer(i) => Some(i.clone()),
            _ => None,
        }
    }

    /// Tries to extract a [`Rational`] from the value.
    pub fn as_real(&self) -> Option<Rational> {
        match self {
            Value::Real(r) => Some(r.clone()),
            _ => None,
        }
    }

    /// Tries to extract a bitvector from the value, interpreting the bits as an unsigned integer.
    pub fn as_bitvec(&self) -> Option<(&Integer, usize)> {
        match self {
            Value::BitVec(val, width) => Some((val, *width)),
            _ => None,
        }
    }

    /// Tries to extract a bitvector from the value, interpreting the bits as a signed integer.
    // Modified in Clean: a set sign bit denotes `val - 2^w` (two's complement). This used to
    // return the magnitude `2^w - val`, a positive number, so every signed operation computed
    // with the wrong sign (see third-party/carcara/DOWNSTREAM.md).
    pub fn as_signed_bitvec(&self) -> Option<(Integer, usize)> {
        let (val, w) = self.as_bitvec()?;
        if w == 0 {
            return None;
        }
        let val = if val.get_bit((w - 1) as u32) {
            let m = Integer::from(1) << w;
            val.clone() - m
        } else {
            val.clone()
        };
        Some((val, w))
    }

    /// Constructs a constant term that corresponds to this value.
    pub fn into_term(self) -> Term {
        match self {
            Value::Bool(true) => Term::Op(Operator::True, Vec::new()),
            Value::Bool(false) => Term::Op(Operator::False, Vec::new()),
            Value::Integer(i) => Term::Const(Constant::Integer(i)),
            Value::Real(r) => Term::Const(Constant::Real(r)),
            Value::String(s) => Term::Const(Constant::String(s)),
            Value::BitVec(val, width) => Term::Const(Constant::BitVec(val, width)),
        }
    }
}

impl Rc<Term> {
    /// Tries to obtain a [`Value`] from a term by evaluating it. This will return `Some` if the
    /// term is "evaluatable".
    ///
    /// We say that a term is evaluatable if it is either:
    /// - a constant term
    /// - an application of an operator over evaluatable terms
    ///
    /// Modified in Clean: what the evaluation reads and computes is charged to a step's
    /// `ExpansionBudget`, in words, and a step past the budget is refused (`Err`) before the
    /// number that would pass it is computed: each value read, the bits a sum, difference, product
    /// or quotient can reach (its arguments' bits together, a bit more for each), and each value
    /// computed. A product squares what it reads, so a chain of shared products, `d_i = (* d_(i-1)
    /// d_(i-1))`, reached any size from a few hundred bytes of text, past GMP's integer type (an
    /// abort) from about 1.3 KB. The terms it builds are hash-consed in a `StepTerms`, not added to
    /// the pool, where every number computed stayed for the rest of the proof; a `match` is left
    /// unevaluated, as a `let` is, where it reached a `todo!()` (a panic, so an abort under Clean's
    /// release profile). See third-party/carcara/DOWNSTREAM.md, "Bit-vector expansion has a
    /// resource budget", `evaluate`.
    pub fn evaluate(&self, pool: &mut dyn TermPool) -> Result<Rc<Term>, CheckerError> {
        let mut budget = ExpansionBudget::new();
        let mut terms = StepTerms::new(&*pool);
        self.evaluate_impl(&mut HashMap::new(), &mut terms, &mut budget)
    }

    fn evaluate_impl<'t>(
        &'t self,
        cache: &mut HashMap<&'t Rc<Term>, Rc<Term>>,
        terms: &mut StepTerms,
        budget: &mut ExpansionBudget,
    ) -> Result<Rc<Term>, CheckerError> {
        if let Some(result) = cache.get(self) {
            return Ok(result.clone());
        }

        let result = match self.as_ref() {
            Term::Const(c) => {
                let value = Value::from_constant(c.clone());
                if let Some(value) = &value {
                    budget.spend_words(READING, value_words(value))?;
                }
                value.map_or_else(|| Term::Const(c.clone()), Value::into_term)
            }
            Term::Op(op, args) => {
                let args: Vec<_> = args
                    .iter()
                    .map(|a| a.evaluate_impl(cache, terms, budget))
                    .collect::<Result<_, _>>()?;
                eval_op(*op, &args, budget)?.map_or_else(|| Term::Op(*op, args), Value::into_term)
            }
            Term::ParamOp { op, op_args, args } => {
                let op_args: Vec<_> = op_args
                    .iter()
                    .map(|a| a.evaluate_impl(cache, terms, budget))
                    .collect::<Result<_, _>>()?;
                let args: Vec<_> = args
                    .iter()
                    .map(|a| a.evaluate_impl(cache, terms, budget))
                    .collect::<Result<_, _>>()?;

                eval_param_op(*op, &op_args, &args, budget)?.map_or_else(
                    || Term::ParamOp { op: *op, op_args, args },
                    Value::into_term,
                )
            }
            // TODO: qualified operators
            Term::AsOp(_, _, _) => self.as_ref().clone(),

            // Modified in Clean: a `match` is left unevaluated; it reached a `todo!()`.
            Term::Var(_, _)
            | Term::App(_, _)
            | Term::Binder(_, _, _)
            | Term::Let(_, _)
            | Term::Match(_, _) => {
                cache.insert(self, self.clone());
                return Ok(self.clone());
            }
        };
        let result = terms.add(result);
        cache.insert(self, result.clone());
        Ok(result)
    }
}

/// Added in Clean: what the evaluator's charges are for.
const READING: &str = "evaluating a term";

/// Added in Clean: the words a value takes, one for the value itself and one for each 64 bits of
/// its numbers or eight bytes of its string.
fn value_words(value: &Value) -> u128 {
    1 + match value {
        Value::Bool(_) => 0,
        Value::Integer(i) => integer_words(i),
        Value::Real(r) => rational_words(r),
        Value::String(s) => s.len() as u128 / 8,
        Value::BitVec(_, w) => *w as u128 / 64,
    }
}

/// Added in Clean: the bits of a number, its numerator's and denominator's together.
fn number_bits(value: &Value) -> u128 {
    match value {
        Value::Integer(i) => u128::from(i.significant_bits()),
        Value::Real(r) => {
            u128::from(r.numer().significant_bits()) + u128::from(r.denom().significant_bits())
        }
        _ => 0,
    }
}

/// Added in Clean: reads `args` as values, charging what each copy takes. `None` if one of them is
/// not a value.
fn read_values(
    args: &[Rc<Term>],
    budget: &mut ExpansionBudget,
) -> Result<Option<Vec<Value>>, CheckerError> {
    let Some(values) = args
        .iter()
        .map(Value::from_term)
        .collect::<Option<Vec<_>>>()
    else {
        return Ok(None);
    };
    budget.spend_words(READING, values.iter().map(value_words).sum())?;
    Ok(Some(values))
}

/// Added in Clean: evaluates `op` over `args`, charging to `budget` what it reads and computes. An
/// arithmetic fold is charged before it runs: each partial result of a sum, difference, product
/// or quotient of rationals has at most as many bits as its arguments together, plus one for each
/// of them, and the charge is twice that (the result, and what GMP works in to compute it).
fn eval_op(
    op: Operator,
    args: &[Rc<Term>],
    budget: &mut ExpansionBudget,
) -> Result<Option<Value>, CheckerError> {
    let Some(args) = read_values(args, budget)? else {
        return Ok(None);
    };
    if matches!(
        op,
        Operator::Add | Operator::Sub | Operator::Mult | Operator::RealDiv
    ) {
        let bits: u128 = args.iter().map(|a| number_bits(a) + 1).sum();
        budget.spend_words("evaluating arithmetic", 2 * (bits / 64 + 1))?;
    }
    let value = compute_op(op, args);
    if let Some(value) = &value {
        budget.spend_words(READING, value_words(value))?;
    }
    Ok(value)
}

macro_rules! mixed_type_arith {
    ($op:tt, $a:expr, $b:expr, $is_real:expr) => {
        match ($a, $b) {
            (Value::Integer(l), Value::Integer(r)) if $is_real => {
                let (l, r) = (Rational::from(l), Rational::from(r));
                Some(Value::Real(l $op r))
            }
            (Value::Integer(l), Value::Integer(r)) => Some(Value::Integer(l $op r)),
            (Value::Integer(l), Value::Real(r)) => Some(Value::Real(Rational::from(l) $op r)),
            (Value::Real(l), Value::Integer(r)) => Some(Value::Real(l $op Rational::from(r))),
            (Value::Real(l), Value::Real(r)) => Some(Value::Real(l $op r)),
            _ => None,
        }
    };
}

macro_rules! arith_op {
    ($op:tt, $args:expr $(, $flag:literal)?) => {{
        let args = $args;
        let first = args[0].clone();
        if !matches!(first, Value::Integer(_) | Value::Real(_)) {
            return None;
        }
        // Hacky way to set `real` to `true` if the "real" flag is passed
        let real = $($flag == "real" ||)? false;
        args[1..]
            .iter()
            .try_fold(first, |acc, arg| mixed_type_arith!($op, acc, arg, real))?
    }};
}

macro_rules! bitvec_op {
    ($op:tt, $args:expr) => {{
        let args = $args;
        let Value::BitVec(first, w) = args[0].clone() else {
            return None;
        };
        // Modified in Clean: `w` is at most `MAX_EVALUATED_BV_WIDTH` (see `Value::new_bitvec`), so
        // the cast is exact.
        let res = args[1..].iter().try_fold(first, |acc, arg| {
            let (arg, _) = arg.as_bitvec()?;
            Some((acc $op arg).keep_bits(w as u32))
        })?;
        Value::new_bitvec(res, w)?
    }};
}

macro_rules! comparison_op {
    ($op:tt, $args:expr) => {{
        fn compare(window: &[Value]) -> Option<bool> {
            match window {
                [Value::Integer(l), Value::Integer(r)] => Some(l $op r),
                [Value::Integer(l), Value::Real(r)] => Some(l $op r),
                [Value::Real(l), Value::Integer(r)] => Some(l $op r),
                [Value::Real(l), Value::Real(r)] => Some(l $op r),
                _ => None,
            }
        }
        Value::Bool(
            $args
                .windows(2)
                .try_fold(true, |acc, w| Some(acc && compare(w)?))?,
        )
    }};
}

macro_rules! bitvec_comparison_op {
    ($op:tt, $args:expr, "signed") => {{
        let args = $args;
        let ((a, _), (b, _)) = (args[0].as_signed_bitvec()?, args[1].as_signed_bitvec()?);
        Value::Bool(a $op b)
    }};
    ($op:tt, $args:expr) => {{
        let args = $args;
        let ((a, _), (b, _)) = (args[0].as_bitvec()?, args[1].as_bitvec()?);
        Value::Bool(a $op b)
    }};
}

fn compute_op(op: Operator, args: Vec<Value>) -> Option<Value> {
    Some(match op {
        Operator::True => Value::Bool(true),
        Operator::False => Value::Bool(false),
        Operator::Not => Value::Bool(!args[0].as_bool()?),
        Operator::Implies => {
            let left = args[0..args.len() - 1]
                .iter()
                .try_fold(false, |acc, arg| Some(acc || !arg.as_bool()?))?;
            let right = args.last().unwrap().as_bool()?;
            Value::Bool(left || right)
        }
        Operator::And => Value::Bool(
            args.iter()
                .try_fold(true, |acc, arg| Some(acc && arg.as_bool()?))?,
        ),
        Operator::Or => Value::Bool(
            args.iter()
                .try_fold(false, |acc, arg| Some(acc || arg.as_bool()?))?,
        ),
        Operator::Xor => Value::Bool(
            args.iter()
                .try_fold(false, |acc, arg| Some(acc != arg.as_bool()?))?,
        ),
        Operator::Equals => Value::Bool(args.windows(2).all(|w| w[0] == w[1])),
        Operator::Distinct => {
            let set: HashSet<&Value> = args.iter().collect();
            Value::Bool(set.len() == args.len())
        }
        Operator::Ite => {
            if args[0].as_bool()? {
                args[1].clone()
            } else {
                args[2].clone()
            }
        }
        Operator::Add => arith_op!(+, args),
        Operator::Sub if args.len() == 1 => match &args[0] {
            Value::Integer(i) => Value::Integer(-i.clone()),
            Value::Real(r) => Value::Real(-r.clone()),
            _ => return None,
        },
        Operator::Sub => arith_op!(-, args),
        Operator::Mult => arith_op!(*, args),
        // Modified in Clean: SMT-LIB `div` and `mod` are Euclidean (the remainder is never
        // negative), while `/` and `%` on `rug::Integer` truncate towards zero. Division by zero is
        // unspecified in SMT-LIB, so no value is produced for it (see
        // third-party/carcara/DOWNSTREAM.md).
        Operator::IntDiv => {
            let mut acc = args[0].as_int()?;
            for arg in &args[1..] {
                let divisor = arg.as_int()?;
                if divisor.is_zero() {
                    return None;
                }
                acc = acc.div_rem_euc(divisor).0;
            }
            Value::Integer(acc)
        }
        Operator::RealDiv => {
            if args[1..].iter().any(|a| {
                matches!(a, Value::Integer(i) if i.is_zero())
                    || matches!(a, Value::Real(r) if r.is_zero())
            }) {
                return None;
            }
            arith_op!(/, args, "real")
        }
        Operator::Mod => {
            let (dividend, divisor) = (args[0].as_int()?, args[1].as_int()?);
            if divisor.is_zero() {
                return None;
            }
            Value::Integer(dividend.div_rem_euc(divisor).1)
        }
        Operator::Abs => match &args[0] {
            Value::Integer(i) => Value::Integer(i.clone().abs()),
            Value::Real(r) => Value::Real(r.clone().abs()),
            _ => return None,
        },
        Operator::Pow2 => {
            let v = args[0].as_int()?;
            if v < 0 {
                return Some(Value::Integer(Integer::from(0)));
            }
            // Modified in Clean: refuse to materialize astronomically large powers.
            let v = v.to_u32().filter(|v| *v <= MAX_MATERIALIZED_BITS)?;
            Value::Integer(Integer::from(1) << v)
        }
        Operator::Log2 => {
            let v = args[0].as_int()?;
            if v <= 0 {
                Value::Integer(Integer::from(0))
            } else {
                Value::Integer(Integer::from(v.significant_bits() - 1))
            }
        }
        Operator::IsPow2 => {
            let v = args[0].as_int()?;
            Value::Bool(v.is_power_of_two())
        }

        // TODO: Transcendentals
        Operator::RealPi
        | Operator::Sqrt
        | Operator::Exp
        | Operator::Sin
        | Operator::Cos
        | Operator::Tan
        | Operator::Csc
        | Operator::Sec
        | Operator::Cot
        | Operator::Arcsin
        | Operator::Arccos
        | Operator::Arctan
        | Operator::Arccsc
        | Operator::Arcsec
        | Operator::Arccot => return None,

        Operator::LessThan => comparison_op!(<, args),
        Operator::GreaterThan => comparison_op!(>, args),
        Operator::LessEq => comparison_op!(<=, args),
        Operator::GreaterEq => comparison_op!(>=, args),

        Operator::ToReal => Value::Real(args[0].as_int()?.into()),
        Operator::ToInt => Value::Integer(args[0].as_real()?.floor().into_numer_denom().0),
        Operator::IsInt => Value::Bool(args[0].as_real()?.is_integer()),

        // TODO: Arrays
        Operator::Select | Operator::Store => return None,

        // TODO: Strings
        Operator::StrConcat
        | Operator::StrLen
        | Operator::StrLessThan
        | Operator::StrLessEq
        | Operator::CharAt
        | Operator::Substring
        | Operator::PrefixOf
        | Operator::SuffixOf
        | Operator::Contains
        | Operator::IndexOf
        | Operator::IndexOfRe
        | Operator::Replace
        | Operator::ReplaceAll
        | Operator::ReplaceRe
        | Operator::ReplaceReAll
        | Operator::StrIsDigit
        | Operator::StrToCode
        | Operator::StrFromCode
        | Operator::StrToInt
        | Operator::StrFromInt
        | Operator::StrToRe
        | Operator::StrInRe
        | Operator::ReNone
        | Operator::ReAll
        | Operator::ReAllChar
        | Operator::ReConcat
        | Operator::ReUnion
        | Operator::ReIntersection
        | Operator::ReKleeneClosure
        | Operator::ReComplement
        | Operator::ReDiff
        | Operator::ReKleeneCross
        | Operator::ReOption
        | Operator::ReRange
        | Operator::ReFromAutomaton => return None,

        // Bitvectors
        Operator::BvNot => {
            let (val, width) = args[0].as_bitvec()?;
            Value::new_bitvec(!val.clone(), width)?
        }
        Operator::BvNeg => {
            let (val, width) = args[0].as_bitvec()?;
            Value::new_bitvec(-val.clone(), width)?
        }
        Operator::BvAnd => bitvec_op!(&, args),
        Operator::BvOr => bitvec_op!(|, args),
        Operator::BvXor => bitvec_op!(^, args),
        Operator::BvAdd => bitvec_op!(+, args),
        Operator::BvMul => bitvec_op!(*, args),
        // Modified in Clean: subtraction is computed modulo 2^w on the unsigned values.
        Operator::BvSub => {
            let ((a, w), (b, _)) = (args[0].as_bitvec()?, args[1].as_bitvec()?);
            Value::new_bitvec(a.clone() - b, w)?
        }
        Operator::BvUDiv => {
            let ((a, w), (b, _)) = (args[0].as_bitvec()?, args[1].as_bitvec()?);
            let value = if b.is_zero() {
                (Integer::from(1) << w) - 1
            } else {
                a.clone() / b
            };
            Value::new_bitvec(value, w)?
        }
        Operator::BvURem => {
            let ((a, w), (b, _)) = (args[0].as_bitvec()?, args[1].as_bitvec()?);
            let value = if b.is_zero() {
                a.clone()
            } else {
                a.clone() % b
            };
            Value::new_bitvec(value, w)?
        }
        // Modified in Clean: with `as_signed_bitvec` fixed, `bvsdiv` (truncating quotient) and
        // `bvsrem` (sign of the dividend) follow SMT-LIB. `bvsmod` takes the sign of the divisor,
        // which is floor division, not `|a| % |b|` with the divisor's sign (see
        // third-party/carcara/DOWNSTREAM.md).
        Operator::BvSDiv => {
            let ((a, w), (b, _)) = (args[0].as_signed_bitvec()?, args[1].as_signed_bitvec()?);
            if b.is_zero() {
                return None;
            }
            Value::new_bitvec(a / b, w)?
        }
        Operator::BvSRem => {
            let ((a, w), (b, _)) = (args[0].as_signed_bitvec()?, args[1].as_signed_bitvec()?);
            if b.is_zero() {
                return None;
            }
            Value::new_bitvec(a % b, w)?
        }
        Operator::BvSMod => {
            let ((a, w), (b, _)) = (args[0].as_signed_bitvec()?, args[1].as_signed_bitvec()?);
            if b.is_zero() {
                return None;
            }
            Value::new_bitvec(a.div_rem_floor(b).1, w)?
        }
        // Modified in Clean: a shift by at least the width produces 0 (or, for a negative
        // `bvashr` operand, all ones) without materializing the shift.
        Operator::BvShl => {
            let ((a, w), (b, _)) = (args[0].as_bitvec()?, args[1].as_bitvec()?);
            match b.to_usize() {
                Some(b) if b < w => Value::new_bitvec(a.clone() << b, w)?,
                _ => Value::new_bitvec(Integer::new(), w)?,
            }
        }
        Operator::BvLShr => {
            let ((a, w), (b, _)) = (args[0].as_bitvec()?, args[1].as_bitvec()?);
            match b.to_usize() {
                Some(b) if b < w => Value::new_bitvec(a.clone() >> b, w)?,
                _ => Value::new_bitvec(Integer::new(), w)?,
            }
        }
        Operator::BvAShr => {
            let (a, w) = args[0].as_signed_bitvec()?;
            let (b, _) = args[1].as_bitvec()?;
            let shift = match b.to_usize() {
                Some(b) if b < w => b,
                _ => w,
            };
            // `>>` on a negative `Integer` rounds towards negative infinity, which is exactly an
            // arithmetic shift.
            Value::new_bitvec(a >> shift, w)?
        }
        Operator::BvULt => bitvec_comparison_op!(<, args),
        Operator::BvULe => bitvec_comparison_op!(<=, args),
        Operator::BvUGt => bitvec_comparison_op!(>, args),
        Operator::BvUGe => bitvec_comparison_op!(>=, args),
        Operator::BvSLt => bitvec_comparison_op!(<, args, "signed"),
        Operator::BvSLe => bitvec_comparison_op!(<=, args, "signed"),
        Operator::BvSGt => bitvec_comparison_op!(>, args, "signed"),
        Operator::BvSGe => bitvec_comparison_op!(>=, args, "signed"),
        Operator::BvConcat => {
            let (value, width) = args.iter().try_fold((Integer::new(), 0), |acc, arg| {
                let (a, i) = acc;
                let (b, j) = arg.as_bitvec()?;
                Some(((a << j) + b, i + j))
            })?;
            Value::new_bitvec(value, width)?
        }
        Operator::BvNAnd => {
            let ((a, w), (b, _)) = (args[0].as_bitvec()?, args[1].as_bitvec()?);
            Value::new_bitvec(!(a.clone() & b), w)?
        }
        Operator::BvNOr => {
            let ((a, w), (b, _)) = (args[0].as_bitvec()?, args[1].as_bitvec()?);
            Value::new_bitvec(!(a.clone() | b), w)?
        }
        Operator::BvXNor => {
            let ((a, w), (b, _)) = (args[0].as_bitvec()?, args[1].as_bitvec()?);
            Value::new_bitvec(!(a.clone() ^ b), w)?
        }
        Operator::BvComp => {
            let ((a, _), (b, _)) = (args[0].as_bitvec()?, args[1].as_bitvec()?);
            Value::new_bitvec(Integer::from(if a == b { 1 } else { 0 }), 1)?
        }
        Operator::UBvToInt => Value::Integer(args[0].as_bitvec()?.0.clone()),
        Operator::SBvToInt => Value::Integer(args[0].as_signed_bitvec()?.0),
        Operator::BvSize => Value::Integer(args[0].as_bitvec()?.1.into()),
        Operator::BvConst => {
            let value = args[0].as_int()?;
            let width = args[1].as_int()?.to_usize().filter(|w| *w > 0)?;
            Value::new_bitvec(value, width)?
        }
        Operator::BvBbTerm => {
            let width = args.len();
            if width > MAX_EVALUATED_BV_WIDTH {
                return None;
            }
            let mut result = Integer::with_capacity(width);
            for (i, b) in args.into_iter().enumerate() {
                result.set_bit(i as u32, b.as_bool()?);
            }
            Value::BitVec(result, width)
        }
        Operator::BvPBbTerm => {
            let width = args.len();
            if width > MAX_EVALUATED_BV_WIDTH {
                return None;
            }
            let mut result = Integer::with_capacity(width);
            for (i, b) in args.into_iter().enumerate() {
                result.set_bit(i as u32, b.as_int()? == 1);
            }
            Value::BitVec(result, width)
        }

        // TODO: Rare
        Operator::RareList | Operator::Cl | Operator::Delete => return None,

        // TODO: Sets and relations
        Operator::SetUnion
        | Operator::SetInter
        | Operator::SetMinus
        | Operator::SetMember
        | Operator::SetSubset
        | Operator::SetSingleton
        | Operator::SetIsEmpty
        | Operator::SetIsSingleton
        | Operator::SetCard
        | Operator::SetInsert
        | Operator::SetComplement
        | Operator::Tuple
        | Operator::TupleUnit
        | Operator::RelTranspose
        | Operator::RelTclosure
        | Operator::RelJoin
        | Operator::RelProduct => return None,
    })
}

/// Added in Clean: evaluates `op` over `op_args` and `args`, charging to `budget` what it reads and
/// computes. Every value these operators compute is a bit-vector of at most
/// `MAX_EVALUATED_BV_WIDTH` bits, a Boolean or a bit.
fn eval_param_op(
    op: ParamOperator,
    op_args: &[Rc<Term>],
    args: &[Rc<Term>],
    budget: &mut ExpansionBudget,
) -> Result<Option<Value>, CheckerError> {
    let (Some(op_args), Some(args)) = (read_values(op_args, budget)?, read_values(args, budget)?)
    else {
        return Ok(None);
    };
    let value = compute_param_op(op, op_args, args);
    if let Some(value) = &value {
        budget.spend_words(READING, value_words(value))?;
    }
    Ok(value)
}

fn compute_param_op(op: ParamOperator, op_args: Vec<Value>, args: Vec<Value>) -> Option<Value> {
    // Modified in Clean: indices that do not fit, and widths of zero, produce no value instead of
    // panicking or wrapping around (see third-party/carcara/DOWNSTREAM.md).
    Some(match op {
        ParamOperator::BvExtract => {
            let i = op_args[0].as_int()?.to_usize()?;
            let j = op_args[1].as_int()?.to_usize()?;
            let (bits, w) = args[0].as_bitvec()?;
            if j > i || i >= w {
                return None;
            }
            // Modified in Clean: `extract i j` keeps bits `i` down to `j`, i.e. the `i + 1` low
            // bits before shifting. Keeping only `i` bits dropped the top extracted bit.
            let bits = bits.clone().keep_bits(i as u32 + 1) >> j;
            Value::new_bitvec(bits, i - j + 1)?
        }
        ParamOperator::ZeroExtend => {
            let i = op_args[0].as_int()?.to_usize()?;
            let (value, w) = args[0].as_bitvec()?;
            Value::new_bitvec(value.clone(), w.checked_add(i)?)?
        }
        ParamOperator::SignExtend => {
            let i = op_args[0].as_int()?.to_usize()?;
            let (value, w) = args[0].as_signed_bitvec()?;
            Value::new_bitvec(value, w.checked_add(i)?)?
        }
        ParamOperator::RotateLeft => {
            let i = op_args[0].as_int()?.to_usize()?;
            let (value, w) = args[0].as_bitvec()?;
            if w == 0 {
                return None;
            }
            // A left rotation by i bits is a right rotation by (w - i mod w) bits. Modified in
            // Clean: `w - i` underflowed for `i > w`.
            Value::new_bitvec(rotate_right(value, w, (w - i % w) % w), w)?
        }
        ParamOperator::RotateRight => {
            let i = op_args[0].as_int()?.to_usize()?;
            let (value, w) = args[0].as_bitvec()?;
            if w == 0 {
                return None;
            }
            Value::new_bitvec(rotate_right(value, w, i), w)?
        }
        ParamOperator::Repeat => {
            let i = op_args[0].as_int()?.to_usize().filter(|i| *i > 0)?;
            let (value, w) = args[0].as_bitvec()?;
            // Modified in Clean: the result width is checked before the loop runs `i` times.
            if w.checked_mul(i)? > MAX_EVALUATED_BV_WIDTH {
                return None;
            }
            let mut result = Integer::ZERO;
            for _ in 0..i {
                result <<= w;
                result += value;
            }
            Value::new_bitvec(result, w * i)?
        }
        ParamOperator::IntToBv => {
            let w = op_args[0].as_int()?.to_usize().filter(|w| *w > 0)?;
            let value = args[0].as_int()?;
            Value::new_bitvec(value, w)?
        }
        ParamOperator::BvConst => {
            let value = op_args[0].as_int()?;
            let w = op_args[1].as_int()?.to_usize().filter(|w| *w > 0)?;
            Value::new_bitvec(value, w)?
        }
        ParamOperator::BvBitOf => {
            let i = op_args[0].as_int()?.to_usize()?;
            let (value, w) = args[0].as_bitvec()?;
            if i >= w {
                return None;
            }
            Value::Bool(value.get_bit(i as u32))
        }
        ParamOperator::BvIntOf => {
            let i = op_args[0].as_int()?.to_usize()?;
            let (value, w) = args[0].as_bitvec()?;
            if i >= w {
                return None;
            }
            let bit = Integer::from(value.get_bit(i as u32) as usize);
            Value::Integer(bit)
        }

        // TODO: Strings, datatypes, sets and relations
        ParamOperator::RePower
        | ParamOperator::ReLoop
        | ParamOperator::Tester
        | ParamOperator::TupleSelect => return None,
    })
}

/// The largest power of two `int.pow2` materializes.
const MAX_MATERIALIZED_BITS: u32 = 1 << 16;

/// Added in Clean: the widest bit-vector `evaluate` computes with. Wider terms are left
/// unevaluated, so a rule that needs their value fails instead of reading a truncated width.
pub const MAX_EVALUATED_BV_WIDTH: usize = MAX_MATERIALIZED_BITS as usize;

/// Rotates a `w`-sized bitvector `r` bits to the right
fn rotate_right(value: &Integer, w: usize, r: usize) -> Integer {
    let r = r % w;
    // The least significant bits, that got rotated around
    let rotated = value.clone().keep_bits(r as u32) << (w - r);
    // The most significant bits, that only got shifted right
    let shifted = value.clone() >> r;
    rotated + shifted
}
