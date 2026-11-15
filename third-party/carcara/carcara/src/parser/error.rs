//! The types for parser errors.

use crate::{
    ast::{Constant, Rc, Sort, Term},
    parser::Token,
    utils::Range,
};
use rug::Integer;
use std::fmt;
use thiserror::Error;

/// The error type for the parser.
#[derive(Debug, Error)]
pub enum ParserError {
    /// The lexer encountered an unexpected character.
    #[error("unexpected character: '{0}'")]
    UnexpectedChar(char),

    /// The lexer encountered a numeral with a leading zero, e.g. `0123`.
    #[error("leading zero in numeral '{0}'")]
    LeadingZero(String),

    /// The lexer encountered a numerical literal that contained a division by zero, e.g. '1/0'.
    #[error("division by zero in numerical literal: '{0}'")]
    DivisionByZeroInLiteral(String),

    /// Modified in Clean: the problem has a number where SMT-LIB reads a symbol that is declared or
    /// bound, such as `-5` with `|-5|` declared (see third-party/carcara/DOWNSTREAM.md, fix 40).
    #[error("'{0}' is a declared or bound symbol, which this checker would read here as a number")]
    SymbolReadAsNumber(String),

    /// The lexer encountered a `\` character while reading a quoted symbol.
    #[error("quoted symbol contains backslash")]
    BackslashInQuotedSymbol,

    /// The lexer encountered the end of the input while reading a quoted symbol.
    #[error("unexpected EOF in quoted symbol")]
    EofInQuotedSymbol,

    /// The lexer encountered the end of the input while reading a string literal.
    #[error("unexpected EOF in string literal")]
    EofInString,

    /// The lexer encountered an invalid Unicode value in an escape sequence.
    #[error("invalid Unicode value: 0x'{0}'")]
    InvalidUnicode(String),

    /// The lexer encountered a bitvector literal with no actual digits. This happens when the
    /// bitvector literal is just `#`, `#b` or `#x`.
    #[error("empty bitvector literal")]
    EmptyBitvector,

    /// A bitvector literal was too large.
    #[error("bitvector literal is too large")]
    TooLargeBitvector,

    /// The parser encountered an unexpected token.
    #[error("unexpected token: '{0}'")]
    UnexpectedToken(Token),

    /// The parser encountered an empty sequence where only non-empty sequences are allowed.
    #[error("expected non-empty sequence")]
    EmptySequence,

    /// An error in sort checking.
    #[error("sort error: {0}")]
    SortError(#[from] SortError),

    /// Expected any bitvector sort.
    #[error("expected bitvector sort, got '{0}'")]
    ExpectedBvSort(Rc<Sort>),

    /// Expected any datatype sort.
    #[error("expected datatype sort, got '{0}'")]
    ExpectedDatatypeSort(Rc<Sort>),

    /// Expected any set sort.
    #[error("expected set sort, got '{0}'")]
    ExpectedSetSort(Rc<Sort>),

    /// Expected any tuple sort.
    #[error("expected tuple sort, got '{0}'")]
    ExpectedTupleSort(Rc<Sort>),

    /// Expected an integer constant term.
    #[error("expected integer constant, got '{0}'")]
    ExpectedIntegerConstant(Rc<Term>),

    /// Pattern in `match` term is not valid.
    #[error("invalid pattern '{0}'")]
    InvalidPattern(Rc<Term>),

    /// Results in `match` term do not have the same type.
    #[error("invalid match results (different types) '{0} and {1}'")]
    InvalidMatchResults(Rc<Term>, Rc<Term>),

    /// Patterns in `match` term do not cover all constructors.
    #[error("Patterns in match statement do not cover all constructors")]
    NonExhaustivePatterns,

    /// A term that is not a function was used as a function.
    #[error("'{0}' is not a function sort")]
    NotAFunction(Rc<Sort>), // TODO: This should also carry the actual function term

    /// Tried to match two incompatible sorts.
    #[error("'{0}' cannot be matched to '{1}'")]
    IncompatibleSorts(Rc<Sort>, Rc<Sort>),

    /// The parser encountered an identifier that was not defined.
    #[error("identifier '{0}' is not defined")]
    UndefinedIden(String),

    /// The parser encountered a sort that was not defined.
    #[error("sort '{0}' is not defined")]
    UndefinedSort(String),

    /// The parser encountered a step id that was not defined.
    #[error("step id '{0}' is not defined")]
    UndefinedStepId(String),

    /// The wrong number of arguments was given to a function, operator or sort.
    #[error("expected {0} arguments, got {1}")]
    WrongNumberOfArgs(Range, usize),

    /// The argument values are not in the expected range.
    #[error("expected argument value to be greater than {0}, got {1}")]
    WrongValueOfArgs(Range, Integer),

    /// Constant arguments given to `extract` do not follow required restrictions.
    #[error("extract arguments do not follow restrictions. Expected: {2} > {0} and {0} >= {1} and {1} >= 0")]
    InvalidExtractArgs(usize, usize, usize),

    /// Modified in Clean: a bit-vector operator whose result width does not fit a `usize` (or,
    /// for `extract`, whose range is empty), which `TermPool::compute_sort` cannot refuse.
    #[error("the result width of '{0}' is not a bit-vector width")]
    BitVecWidthOverflow(String),

    /// A step id was used in more than one step.
    #[error("step id '{0}' was repeated")]
    RepeatedStepId(String),

    /// The number given as the arity in a `declare-sort` command is too large. This only happens
    /// if the number is too big to fit in a `usize`, so it almost never happens.
    #[error("{0} is not a valid sort arity")]
    InvalidSortArity(Integer),

    /// The number of datatype declarations given in a `declare-datatypes` command didn't match the
    /// number of sorts declared beforehand.
    #[error("expected {0} datatype declarations, got {1}")]
    WrongNumberOfDatatypeDeclarations(usize, usize),

    /// The number of parameters of a datatype in a `declare-datatypes` command didn't match the
    /// arity declared beforehand.
    #[error("expected {0} parameters for datatype based on declared arity, got {1}")]
    WrongNumberOfDatatypeParams(usize, usize),

    /// A `match` pattern contained an unknown constructor
    #[error("unknown datatype constructor: {0}")]
    UnknownConstructor(String),

    // Modified in Clean: the four errors below refuse declarations that would give a datatype
    // symbol or a datatype sort a second meaning, which the `dt_project` rule relies on not
    // happening (see third-party/carcara/DOWNSTREAM.md, C2). Each is ill-formed SMT-LIB.
    /// A datatype constructor, selector or tester shares its name and argument sorts with another
    /// global declaration (in either order), so an application of it is ambiguous.
    #[error(
        "'{0}' is declared both as a datatype constructor, selector or tester and as another \
         symbol with the same argument sorts"
    )]
    AmbiguousDatatypeSymbol(String),

    /// A datatype was declared more than once.
    #[error("datatype '{0}' is declared more than once")]
    DatatypeRedeclared(String),

    /// A datatype has the name of a sort from `declare-sort` or `define-sort` (in either order).
    #[error("'{0}' is declared both as a datatype and as another sort")]
    DatatypeSortRedeclared(String),

    /// A name is used for more than one constructor or selector of the same datatype.
    #[error("'{0}' names more than one constructor or selector of the same datatype")]
    DuplicateDatatypeSymbol(String),

    // Modified in Clean: refuses `(as f S)` whose sort `S` is not an instance of the `par` sort of
    // `f`; upstream built `f` at any sort `S` (see third-party/carcara/DOWNSTREAM.md, C2).
    /// A parametric datatype symbol was qualified with `as` at a sort that is not an instance of
    /// its parametric sort.
    #[error(
        "parametric datatype symbol '{0}' qualified with sort '{1}', which is not an instance of \
         its sort '{2}'"
    )]
    NotAnInstanceOfParSort(String, Rc<Sort>, Rc<Sort>),

    // Modified in Clean: the four errors below refuse problems that would otherwise be read with
    // premises other than the script's (see third-party/carcara/DOWNSTREAM.md, fixes 36 and 37).
    /// A function definition (`define-fun` expanded as a macro, or a `:named` term) is used in the
    /// problem where a binder rebinds a name its definition mentions, so the binder would capture
    /// it.
    #[error("'{0}' is used where a binder rebinds '{1}', which its definition mentions")]
    MacroCapture(String, String),

    /// A `:named` term in the problem mentions a locally bound variable. SMT-LIB requires a named
    /// term to be closed.
    #[error("the term named '{0}' mentions the bound variable '{1}'")]
    NamedTermNotClosed(String, String),

    /// The problem uses `push`, `pop`, `reset` or `reset-assertions`. A problem must be a single
    /// query.
    #[error(
        "'{0}' is not supported: a problem must be a single query, without push, pop, reset or \
         reset-assertions"
    )]
    UnsupportedScriptCommand(String),

    /// A command that changes the problem follows the end of its query (the first `check-sat`,
    /// `check-sat-assuming` or `exit`).
    #[error(
        "'{0}' after '{1}': the query a proof refutes ends at its first check-sat, \
             check-sat-assuming or exit"
    )]
    CommandAfterQueryEnd(String, String),

    /// Modified in Clean: the problem uses a command the parser does not read (an extension such
    /// as `check-sat-using`, or a quoted command name). It may end the query or change the
    /// assertions in a way the parser cannot see (see third-party/carcara/DOWNSTREAM.md, fix 37).
    #[error("'{0}' is not a command this checker reads, so the problem's query is unknown")]
    UnknownScriptCommand(String),

    /// Modified in Clean: the problem uses `define-fun-rec` or `define-funs-rec`. Its SMT-LIB
    /// reading is an axiom that need not be consistent, and solvers read it differently (see
    /// third-party/carcara/DOWNSTREAM.md, fix 39).
    #[error(
        "'{0}' is not supported: a recursive definition is an axiom that need not be consistent, \
         and solvers do not agree on its reading"
    )]
    RecursiveDefinitionRefused(String),

    // Modified in Clean: the errors below refuse problems whose names the parser would not keep
    // apart (see third-party/carcara/DOWNSTREAM.md, fix 38).
    /// The problem declares or defines a symbol named like a built-in operator, which the parser
    /// keeps reading as the built-in.
    #[error("'{0}' is a built-in operator and cannot be declared or defined")]
    BuiltinNameDeclared(String),

    /// The problem declares or defines a symbol whose name is already declared or defined.
    #[error("'{0}' is already declared or defined and cannot be declared or defined again")]
    NameAlreadyInUse(String),

    /// The problem declares or defines a sort named like a built-in sort, which the parser keeps
    /// reading as the built-in.
    #[error("'{0}' is a built-in sort and cannot be declared or defined")]
    BuiltinSortDeclared(String),

    /// The problem declares or defines a sort whose name is already declared or defined.
    #[error("sort '{0}' is already declared or defined")]
    SortRedeclared(String),

    /// The parser encountered an empty subproof
    #[error("subproof '{0}' is empty")]
    EmptySubproof(String),

    // Modified in Clean: the two errors below bound how deep the parser and the checker recurse
    // (see `MAX_WRITTEN_NESTING` and `MAX_TERM_DEPTH` in `parser/mod.rs`, and
    // third-party/carcara/DOWNSTREAM.md, "Terms nest at most 2^18 deep").
    /// Terms or sorts are written nested more than the limit deep.
    #[error("terms and sorts written more than {0} deep inside each other are not read")]
    WrittenTooDeep(usize),

    /// A term or a sort is more than the limit deep, as written or as built from definitions.
    #[error("a term or sort more than {0} deep is not read")]
    TooDeep(usize),

    // Added in Clean: the parse stops at the deadline its caller sets (`parse_instance_until`; see
    // third-party/carcara/DOWNSTREAM.md, "The checker stops at a deadline").
    /// The parse ran past its deadline.
    #[error("the parse ran past its deadline")]
    DeadlineExceeded,

    /// The last command in a subproof is not a `step` command.
    #[error("last command in subproof '{0}' is not a step")]
    LastSubproofStepIsNotStep(String),

    /// The parser encountered the end of the input while it was still inside a subproof.
    #[error("subproof '{0}' was not closed")]
    UnclosedSubproof(String),

    /// The parser encountered an `assume` after a `step` inside of a subproof.
    #[error("`assume` command '{0}' appears after step inside subproof")]
    AssumeAfterStepInSubproof(String),

    /// Modified in Clean: a tester `(_ is C)` whose `C` is not a constructor of its argument's
    /// datatype, or is a local binding of that name (see third-party/carcara/DOWNSTREAM.md, "Also
    /// hardened").
    #[error("'(_ is {0})' does not name a constructor of its argument's datatype")]
    InvalidTester(String),

    /// The parser encountered an unknown indexed operator.
    #[error("not a valid indexed operator: '{0}'")]
    InvalidIndexedOp(String),

    /// The parser encountered an unknown qualified operator.
    #[error("not a valid qualified operator: '{0}'")]
    InvalidQualifiedOp(String),

    // RCP errors
    #[error("not a valid automaton declaration: '{0}'")]
    InvalidAutomatonDeclaration(String),

    #[error("expected an automaton declaration, got: '{0}'")]
    ExpectedAnAutomatonDeclaration(Rc<Term>),

    /// The parser encountered an invalid argument.
    #[error("not a valid format for the argument: '{0}'")]
    InvalidRareArgFormat(String),

    /// The parser encountered an invalid Rare argument attribute.
    #[error("not a valid argument attribute: '{0}'")]
    InvalidRareArgAttribute(String),

    /// The parser encountered an invalid Rare rule attribute.
    #[error("not a valid rule attribute: '{0}'")]
    InvalidRareRuleAttribute(String),

    /// The parser encountered a Rare ruel with no conclusion.
    #[error("the rule '{0}' has no conclusion")]
    UndefinedRareConclusion(String),
}

/// Returns an error if the length of `sequence` is not in the `expected` range.
pub fn assert_num_args<T, R>(sequence: &[T], range: R) -> Result<(), ParserError>
where
    R: Into<Range>,
{
    let range = range.into();
    if range.contains(sequence.len()) {
        Ok(())
    } else {
        Err(ParserError::WrongNumberOfArgs(range, sequence.len()))
    }
}

/// Returns an error if the value of `sequence` is not in the `expected` range.
pub fn assert_indexed_op_args_value<R>(sequence: &[Rc<Term>], range: R) -> Result<(), ParserError>
where
    R: Into<Range>,
{
    let range = range.into();
    for x in sequence {
        if let Term::Const(Constant::Integer(i)) = x.as_ref() {
            let contained = i.to_usize().is_some_and(|i| range.contains(i));
            if !contained {
                return Err(ParserError::WrongValueOfArgs(range, i.clone()));
            }
        }
    }
    Ok(())
}

/// Makes sure `got` is a valid `Set` sort.
pub fn check_set_sort(got: &Rc<Sort>) -> Result<(), ParserError> {
    if !matches!(got.as_ref(), Sort::Set(_)) {
        return Err(ParserError::ExpectedSetSort(got.clone()));
    }
    Ok(())
}

/// Makes sure `got` is a valid `Tuple` sort.
pub fn check_tuple_sort(got: &Rc<Sort>) -> Result<(), ParserError> {
    if !matches!(got.as_ref(), Sort::Tuple(_)) {
        return Err(ParserError::ExpectedTupleSort(got.clone()));
    }
    Ok(())
}

/// Makes sure `got` is a valid `(Set (Tuple ...))` sort.
pub fn check_relation_sort(got: &Rc<Sort>) -> Result<(), ParserError> {
    let Sort::Set(tuple) = got.as_ref() else {
        return Err(ParserError::ExpectedSetSort(got.clone()));
    };
    check_tuple_sort(tuple)
}

/// An error in sort checking.
#[derive(Debug, Error)]
pub struct SortError {
    /// The possible sorts that were expected.
    pub expected: Box<[Rc<Sort>]>,

    /// The sort we got.
    pub got: Rc<Sort>,
}

impl fmt::Display for SortError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match &*self.expected {
            [] => unreachable!(),
            [p] => write!(f, "expected '{}', got '{}'", p, self.got),
            [first, middle @ .., last] => {
                write!(f, "expected '{}'", first)?;
                for p in middle {
                    write!(f, ", '{}'", p)?;
                }
                write!(f, " or '{}', got '{}'", last, self.got)
            }
        }
    }
}
