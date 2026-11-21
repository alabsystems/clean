// Modified in Clean: typed array-lambda dialect and explicit lambda export refusal.
//! A parser for the Alethe proof format.
//! Clean downstream changes: optional, declaration-aware `bv2nat` compatibility; the optional
//! `zero_extend` reading of Clean's Alethe dialect (`expand_zero_extend`); checked bit-vector
//! result widths. See third-party/carcara/DOWNSTREAM.md.

mod array_lambda;
mod datatypes;
mod error;
mod lexer;
mod rare;
pub(crate) mod tests;

use crate::{
    ast::{
        build_term,
        pool::{first_free_var, FreeVars, PrimitivePool, TermPool},
        rare_rules::{RareStatements, Rules},
        AnchorArg, Binder, BindingList, Constant, Operator, ParamOperator, Problem, ProblemPrelude,
        Proof, ProofCommand, ProofStep, QualifiedOperator, Rc, Sort, SortSubstitution, SortedVar,
        Subproof, Substitution, Term,
    },
    automata::parser::parse_automaton,
    utils::{HashCache, HashMapStack},
    CarcaraResult, Error,
};
use carcara_macros::GenerateSetters;
use error::{assert_indexed_op_args_value, assert_num_args, check_relation_sort, check_set_sort};
use indexmap::{IndexMap, IndexSet};
use rug::{Integer, Rational};
use std::{collections::HashMap, iter::Iterator, str::FromStr, sync::Arc};

pub use error::{ParserError, SortError};
pub use lexer::{Position, Reserved, Token};

/// Grammar selection belongs to the existing checker dialect, not a user
/// workaround or a global Function/Array compatibility relation.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
enum ArrayLambdaDialect {
    #[default]
    FunctionsOnly,
    TypedArrayContexts,
}

/// Configuration for [`Parser`].
#[derive(Debug, Clone, Copy, Default, GenerateSetters)]
#[const_setters]
pub struct Config {
    /// If `true`, the parser will automatically expand function definitions introduced by
    /// `define-fun` commands in the SMT problem. If `false`, those `define-fun`s are instead
    /// interpreted as a function declaration and an `assert` command that defines the function
    /// as equal to its body (or to a lambda term, if it contains arguments). Note that function
    /// definitions in the proof are always expanded.
    apply_function_defs: bool,

    /// If `true`, the parser will eliminate `let` bindings from terms during parsing. This is done
    /// by replacing any occurrence of a variable bound in the `let` binding with its corresponding
    /// value.
    expand_lets: bool,

    /// If `true`, this relaxes the type checking rules in Carcara to allow `Int`-`Real` subtyping.
    /// That is, terms of sort `Int` will be allowed in arithmetic operations where a `Real` term
    /// was expected. Note that this only applies to predefined operators --- passing an `Int` term
    /// to a function that expects a `Real` will still be an error.
    allow_int_real_subtyping: bool,

    /// Enables "strict" parsing. If `true`:
    /// - Unary `and`, `or` and `xor` terms are not allowed
    /// - Anchor arguments using the old syntax (i.e., `(:= <symbol> <term>)`) are not allowed
    strict: bool,

    /// If `true`, the parser will parse arguments to the `hole` rule, expecting them to be valid
    /// terms.
    parse_hole_args: bool,

    /// If `true`, allow indexed operators (usually used like so: `((_ <op> <op_args>...)
    /// <args>...)`) to be used in "higher-order" fashion, that is, by omitting the `_` construction
    /// and passing the operator arguments and regular arguments together: `(<op> <op_args>...
    /// <args>...)`.
    allow_higher_order_indexed_ops: bool,

    /// If `true`, allow local sort parameters declared with a leading `@` character (e.g. `@T`) to
    /// also be referenced with the `@` omitted (i.e., both `T` or `@T` are accepted).
    ///
    /// This behaviour is seen in some legacy rare files.
    implicit_at_sort_alias: bool,

    /// If `true`, relaxes sort checking rules such that sorts that are compatible but not identical
    /// (e.g. `(Array Int T)` and `(Array Int Real)`, where `T` is a sort variable) are considered
    /// equal for sort checking purposes.
    relaxed_sort_checking: bool,

    /// If `true`, allow old (SMT-LIB versions < 2.6) syntax for datatype testers, namely `is-cons`
    /// instead of `(_ is cons)`.
    allow_legacy_tester_syntax: bool,

    /// Interpret an undeclared `bv2nat` application as the typed `ubv_to_int` operator.
    /// Declared, defined, and locally bound names retain their ordinary interpretation.
    allow_legacy_bv2nat: bool,

    /// Modified in Clean: the rule is stated in third-party/carcara/DOWNSTREAM.md § Dialect.
    expand_zero_extend: bool,
    #[skip_setter]
    array_lambda_dialect: ArrayLambdaDialect,
}

impl Config {
    /// Concstructs a new `Config`, with default settings.
    pub const fn new() -> Self {
        // I can't just call `default()` because it is not const :/
        Self {
            apply_function_defs: false,
            expand_lets: false,
            allow_int_real_subtyping: false,
            strict: false,
            parse_hole_args: false,
            allow_higher_order_indexed_ops: false,
            implicit_at_sort_alias: false,
            relaxed_sort_checking: false,
            allow_legacy_tester_syntax: false,
            allow_legacy_bv2nat: false,
            expand_zero_extend: false,
            array_lambda_dialect: ArrayLambdaDialect::FunctionsOnly,
        }
    }

    /// Modified in Clean: the configuration of Clean's Alethe dialect, every option a
    /// `### Dialect:` entry of third-party/carcara/DOWNSTREAM.md states, and no other.
    pub const fn clean_dialect() -> Self {
        Self {
            array_lambda_dialect: ArrayLambdaDialect::TypedArrayContexts,
            ..Self::new()
                .allow_legacy_bv2nat(true)
                .expand_zero_extend(true)
        }
    }
}

/// Parses an SMT problem instance (in the SMT-LIB format) and its associated proof (in the Alethe
/// format). If the optional argument `rules` is provided, also parses a set of Rare rewrite rules.
///
/// This returns the parsed problem, proof, and rules, as well as the `TermPool` used in parsing.
pub fn parse_instance<'s>(
    problem: &'s str,
    proof: &'s str,
    rules: Option<&'s str>,
    config: Config,
) -> CarcaraResult<(Problem, Proof, Rules, PrimitivePool)> {
    let mut pool = PrimitivePool::new();
    parse_instance_with_pool(problem, proof, rules, config, &mut pool)
        .map(|(prelude, proof, rules)| (prelude, proof, rules, pool))
}

/// Added in Clean: [`parse_instance`], refused with `ParserError::DeadlineExceeded` once `deadline`
/// passes. The deadline is set on this thread for the parse (`checker/deadline.rs`), and the
/// parser and its capture checks poll it as they go; nothing a refused parse read is returned.
/// See third-party/carcara/DOWNSTREAM.md, "The checker stops at a deadline".
pub fn parse_instance_until<'s>(
    problem: &'s str,
    proof: &'s str,
    rules: Option<&'s str>,
    config: Config,
    deadline: Option<std::time::Instant>,
) -> CarcaraResult<(Problem, Proof, Rules, PrimitivePool)> {
    let _deadline = crate::checker::deadline::arm(deadline);
    parse_instance(problem, proof, rules, config)
}

/// Given an existing [`PrimitivePool`], parses an SMT problem instance (in the SMT-LIB format) and
/// its associated proof (in the Alethe format). If the optional argument `rules` is provided, also
/// parses a set of Rare rewrite rules.
///
/// This returns the parsed problem, proof, and rules.
pub fn parse_instance_with_pool<'s>(
    problem: &'s str,
    proof: &'s str,
    rules: Option<&'s str>,
    config: Config,
    pool: &mut PrimitivePool,
) -> CarcaraResult<(Problem, Proof, Rules)> {
    // Modified in Clean: the parse runs under the deadline set on this thread, if any (see
    // `parse_instance_until`). The parser polls it as it reads, and a parse that ends past it is
    // refused whatever it read, so no parse cut short is returned even where a poll's refusal was
    // caught on the way.
    let mut parser = Parser::new(pool, config, problem)?;
    let parsed = parse_all(&mut parser, proof, rules);
    if crate::checker::deadline::expired_now() {
        let position = parser.current_position;
        return Err(Error::Parser(ParserError::DeadlineExceeded, position));
    }
    parsed
}

/// The problem `parser` reads, then `proof` and `rules`.
fn parse_all<'s>(
    parser: &mut Parser<'_, 's>,
    proof: &'s str,
    rules: Option<&'s str>,
) -> CarcaraResult<(Problem, Proof, Rules)> {
    let problem = parser.parse_problem()?;
    parser.reset(proof)?;
    let proof = parser.parse_proof()?;
    if let Some(rules) = rules {
        parser.reset(rules)?;
        parser.config.allow_higher_order_indexed_ops = true;
        parser.config.relaxed_sort_checking = true;
        let rules = parser.parse_rare();
        let rules = match rules {
            Ok(t) => Ok(t),
            Err(v) => Err(v),
        }?;
        return Ok((problem, proof, rules));
    }
    Ok((problem, proof, RareStatements { rules: IndexMap::new() }))
}

/// A function definition, from a `define-fun` command.
struct FunctionDef {
    params: Vec<SortedVar>,
    body: Rc<Term>,
}

impl FunctionDef {
    fn apply(&self, p: &mut PrimitivePool, args: Vec<Rc<Term>>) -> Result<Rc<Term>, ParserError> {
        assert_num_args(&args, self.params.len())?;
        if args.is_empty() {
            return Ok(self.body.clone());
        }

        for (arg, (_, expected)) in args.iter().zip(self.params.iter()) {
            let got = p.sort(arg);

            // TODO: maybe use `is_compatible_with` instead of `param_eq` when
            // `relaxed_sort_checking` is enabled, similarly to how `Parser::compare_sort` works.
            if !expected.param_eq(got.as_ref()) {
                return Err(SortError {
                    expected: vec![expected.clone()].into_boxed_slice(),
                    got,
                }
                .into());
            }
        }

        // Build a hash map of all the parameter names and the values they will
        // take
        let substitution = self
            .params
            .iter()
            .zip(args)
            .map(|((n, s), arg)| (p.add(Term::new_var(n, s.clone())), arg))
            .collect();

        // Since we already checked the sorts of the arguments, creating this substitution
        // can never fail
        let result = Substitution::new(p, substitution)
            .unwrap()
            .apply(p, &self.body);
        Ok(result)
    }
}

/// A sort definition, from a `define-sort` command.
#[derive(Debug)]
struct SortDef {
    params: Vec<String>,
    body: Rc<Sort>,
}

// Added in Clean: how deep the parser reads terms and sorts. The parser recurses once per term or
// sort written inside another, and the checker's rules, the substitutions and free-variable sets
// recurse once per level of the terms they walk, so a term nested a few thousand deep, written out
// or built through a chain of definitions, `:named` terms or `define-sort`s, overflowed the stack
// of the thread that checked it, which ends the process (Clean's adapter ran on its caller's
// thread: 8 MiB on the main thread, 2 MiB on a worker). The parser now refuses deeper input, and
// Clean's adapter checks on a thread whose stack covers these limits (see
// third-party/carcara/DOWNSTREAM.md, "Terms nest at most 2^18 deep").

/// Added in Clean: the most terms and sorts the parser reads written inside each other. The parser
/// takes about 2.3 KiB of stack per level in a release build. Every trust-cg certificate is
/// written less than 80 deep.
pub const MAX_WRITTEN_NESTING: usize = 1 << 14;

/// Added in Clean: the deepest term or sort the parser reads, as written or as built from
/// definitions, `:named` terms and `define-sort`s. A rule recurses over terms at up to about
/// 1.4 KiB of stack per level in a release build. The deepest trust-cg certificate is 8,585 deep (a
/// 64-bit division's circuit); a division of the widest operands the expansion budget admits
/// (255 bits) is about 136,000 deep.
pub const MAX_TERM_DEPTH: usize = 1 << 18;

/// The state of the parser.
///
/// This holds all the function, constant or sort declarations and definitions, as well as the term
/// pool used by the parser.
#[derive(Default)]
struct ParserState {
    symbol_table: HashMapStack<HashCache<String>, Rc<Sort>>,
    function_defs: IndexMap<String, FunctionDef>,
    sort_declarations: IndexMap<String, usize>,
    datatype_declarations: HashMapStack<String, usize>,
    sort_defs: IndexMap<String, SortDef>,
    step_ids: HashMapStack<HashCache<String>, usize>,

    // Modified in Clean: every global symbol declared so far, by name: each sort it was declared
    // with, and whether that declaration is a datatype constructor, selector or tester (see
    // `Parser::record_global_symbol`).
    global_symbols: IndexMap<String, Vec<(Rc<Sort>, bool)>>,

    // Modified in Clean: the `define-fun` whose body is being parsed, if any (see
    // `Parser::expand_macro`).
    define_fun_scope: Option<DefineFunScope>,

    // Added in Clean: how many terms and sorts the parser is inside, and the depth of each term and
    // sort it has read (see `MAX_WRITTEN_NESTING` and `MAX_TERM_DEPTH`).
    nesting: usize,
    term_depths: HashMap<Rc<Term>, u32>,
    sort_depths: HashMap<Rc<Sort>, u32>,

    // Added in Clean: the answers of `Parser::locally_bound_free_vars`, each with the state of the
    // scopes it was computed in, and the state of each local scope of the symbol table as of its
    // last call, innermost last (see there).
    locally_bound: HashMap<Rc<Term>, (FreeVars, Arc<ScopeState>)>,
    scope_states: Vec<Arc<ScopeState>>,
    // Added in Clean: the answers at which `locally_bound` is next swept, if more than
    // `ANSWERS_SWEEP_MIN` (see `Parser::locally_bound_free_vars`).
    locally_bound_sweep_at: usize,

    // Added in Clean: how many terms `Parser::locally_bound_free_vars` answered from their free
    // variables, for the tests that bound it.
    #[cfg(test)]
    answered_from_free_vars: usize,
}

/// Added in Clean: the symbol table's scopes up to a depth (1 for the outermost local scope), as
/// `Parser::locally_bound_free_vars` found them: the table's generation for that depth
/// (`HashMapStack::generation_at`), and the state of the depth below, if it is a local scope.
struct ScopeState {
    depth: usize,
    generation: (u64, u64),
    outer: Option<Arc<ScopeState>>,
}

/// Added in Clean: how many depths `Parser::carried_answer` looks through for scopes an answer
/// holds for. A scope entered for each of a chain's links costs one depth a link (two for a link
/// in two binders of its own); an answer found deeper is computed again.
const MAX_CARRY_STEPS: usize = 64;

/// Added in Clean: the fewest answers at which `Parser::locally_bound_free_vars` drops those that no
/// longer answer anywhere.
const ANSWERS_SWEEP_MIN: usize = 1 << 12;

/// Added in Clean: the depth up to which an answer kept with the scope state `kept` answers, where
/// the table's local scopes are in the states `states` (innermost last, `innermost` of them), or
/// `None` where it does not answer (see `Parser::carried_answer`). `empty` is whether the answer
/// holds no variable.
fn answering_depth(
    states: &[Arc<ScopeState>],
    innermost: usize,
    empty: bool,
    kept: &Arc<ScopeState>,
) -> Option<usize> {
    let (mut state, mut steps) = (kept, 0);
    loop {
        if state.depth <= innermost && states[state.depth - 1].generation == state.generation {
            return Some(state.depth);
        }
        // An answer that holds a variable answers only in the scopes it was computed in: which
        // of its variables the scopes up to a depth below bind is not kept.
        if !empty || steps == MAX_CARRY_STEPS {
            return None;
        }
        state = state.outer.as_ref()?;
        steps += 1;
    }
}

/// Modified in Clean: the parameter scope of the `define-fun` whose body is being parsed.
///
/// A macro (a `define-fun` expanded as a macro, or a `:named` term) used in that body may mention
/// a global symbol that one of the parameters shadows. The expansion then holds the global under
/// an unforgeable placeholder name, and `Parser::close_define_fun` renames the parameter and puts
/// the global back. See third-party/carcara/DOWNSTREAM.md, fix 36.
struct DefineFunScope {
    /// The symbol table depth of the parameter scope.
    depth: usize,

    /// Each placeholder introduced in the body, and the variable it stands for.
    placeholders: IndexMap<Rc<Term>, Rc<Term>>,
}

/// Modified in Clean: appended to a name to build a placeholder for a global symbol (see
/// `DefineFunScope`). No symbol the lexer produces contains a backslash (it is not a symbol
/// character, and the lexer refuses it in a quoted symbol), so no script can name it; unlike `|`,
/// the printer can still write it (quoted) in a message.
const GLOBAL_PLACEHOLDER_SUFFIX: &str = "\\global";

/// Modified in Clean: appended to a `define-fun` parameter renamed so that it no longer shadows a
/// global symbol its body mentions (see `DefineFunScope`). Unforgeable for the same reason.
const RENAMED_PARAMETER_SUFFIX: &str = "\\param";

/// Modified in Clean: the SMT-LIB commands that do not change the problem, which may appear
/// anywhere in it (see `Parser::check_script_command`).
const READ_ONLY_COMMANDS: &[&str] = &[
    "set-info",
    "set-option",
    "get-info",
    "get-option",
    "get-value",
    "get-model",
    "get-assignment",
    "get-assertions",
    "get-proof",
    "get-unsat-core",
    "get-unsat-assumptions",
    "echo",
];

/// Modified in Clean: the sort names `Parser::make_sort` reads as built-in sorts (keep the two in
/// step). A script may not declare or define a sort of one of these names (see
/// `Parser::check_sort_name_is_free`).
const BUILTIN_SORT_NAMES: &[&str] = &[
    "->",
    "Bool",
    "Int",
    "Real",
    "String",
    "RegLan",
    "Type",
    "Array",
    "rare-list",
    "RareList",
    "Set",
    "Tuple",
    "UnitTuple",
    "Relation",
];

/// Modified in Clean: the argument sorts of a symbol of sort `sort` (none for a constant), and
/// whether they may mention sort parameters (`sort` is a `par` sort).
fn symbol_domain(sort: &Sort) -> (&[Rc<Sort>], bool) {
    match sort {
        Sort::Par(_, inner) => (symbol_domain(inner).0, true),
        Sort::Function(sorts) => (sorts.split_last().map_or(&[], |(_, args)| args), false),
        _ => (&[], false),
    }
}

/// Modified in Clean: whether an application of a symbol of sort `a` could also be read as an
/// application of a same-named symbol of sort `b`. Carcara resolves an application by the name
/// alone (the later declaration wins), and SMT-LIB tells same-named symbols apart by their
/// argument sorts, so two declarations overlap when their argument sorts are equal, whatever their
/// result sorts. A `par` sort overlaps any declaration of the same arity: its parameters can be
/// instantiated.
fn symbol_domains_overlap(a: &Sort, b: &Sort) -> bool {
    let ((a_args, a_par), (b_args, b_par)) = (symbol_domain(a), symbol_domain(b));
    if a_par || b_par {
        a_args.len() == b_args.len()
    } else {
        a_args == b_args
    }
}

/// A parser for the Alethe proof format.
pub struct Parser<'p, 's> {
    pool: &'p mut PrimitivePool,
    config: Config,
    lexer: lexer::Lexer<'s>,
    current_token: Token,
    current_position: Position,
    // Modified in Clean: the symbol SMT-LIB reads in place of the current number token, and of the
    // token `next_token` last returned (see `Lexer::take_number_symbol_reading`).
    current_number_symbol: Option<String>,
    consumed_number_symbol: Option<String>,
    state: ParserState,
    is_real_only_logic: bool,
    problem: Option<Problem>,
    // One original-deadline role plan per outer term; nested parses only read it.
    lambda_term_depth: usize,
    lambda_array_positions: std::collections::HashSet<Position>,
    lambda_expected: Option<Rc<Sort>>,
}

/// Added in Clean: records in `depths` the depth of `root` (one more than its deepest child, as
/// `children` lists them) and of each node under it not yet recorded, without recursion; refuses a
/// node more than `MAX_TERM_DEPTH` deep. The parser reads a term's subterms before the term, so
/// this usually only looks up its children; a definition's expansion is walked once.
fn record_depth<T: Eq>(
    depths: &mut HashMap<Rc<T>, u32>,
    root: &Rc<T>,
    children: impl Fn(&T, &mut dyn FnMut(&Rc<T>)),
) -> Result<(), ParserError> {
    if depths.contains_key(root) {
        return Ok(());
    }
    let mut stack = vec![root.clone()];
    while let Some(node) = stack.last().cloned() {
        if depths.contains_key(&node) {
            stack.pop();
            continue;
        }
        let (mut deepest, mut unrecorded) = (0, false);
        children(&node, &mut |child| match depths.get(child) {
            Some(&depth) => deepest = deepest.max(depth),
            None => {
                unrecorded = true;
                stack.push(child.clone());
            }
        });
        if unrecorded {
            continue;
        }
        stack.pop();
        if deepest as usize >= MAX_TERM_DEPTH {
            return Err(ParserError::TooDeep(MAX_TERM_DEPTH));
        }
        // Modified in Clean: a term built from definitions can hold many new subterms per token
        // read, so the walk polls the parse's deadline too (see `parse_instance_until`).
        if crate::checker::deadline::expired() {
            return Err(ParserError::DeadlineExceeded);
        }
        depths.insert(node, deepest + 1);
    }
    Ok(())
}

impl<'p, 's> Parser<'p, 's> {
    /// Constructs a new `Parser` from a type that implements `BufRead`.
    ///
    /// This operation can fail if there is an IO or lexer error on the first token.
    pub fn new(pool: &'p mut PrimitivePool, config: Config, input: &'s str) -> CarcaraResult<Self> {
        let mut lexer = lexer::Lexer::new(input);
        let (current_token, current_position) = lexer.next_token()?;
        // Modified in Clean: see `check_number_is_not_a_bound_symbol`.
        let current_number_symbol = lexer.take_number_symbol_reading();
        Ok(Parser {
            pool,
            config,
            lexer,
            current_token,
            current_position,
            current_number_symbol,
            consumed_number_symbol: None,
            state: ParserState::default(),
            is_real_only_logic: false,
            problem: None,
            lambda_term_depth: 0,
            lambda_array_positions: std::collections::HashSet::new(),
            lambda_expected: None,
        })
    }

    /// Resets the parser position and sets its input to `input`. This keeps the parser state,
    /// including all function, constant and sort declarations.
    pub fn reset(&mut self, input: &'s str) -> CarcaraResult<()> {
        let mut lexer = lexer::Lexer::new(input);
        let (current_token, current_position) = lexer.next_token()?;
        // Modified in Clean: see `check_number_is_not_a_bound_symbol`.
        self.current_number_symbol = lexer.take_number_symbol_reading();
        self.consumed_number_symbol = None;
        self.lexer = lexer;
        self.current_token = current_token;
        self.current_position = current_position;
        Ok(())
    }

    /// Advances the parser one token, and returns the previous `current_token`.
    ///
    /// Modified in Clean: refused once the parse's deadline has passed (see `parse_instance_until`).
    fn next_token(&mut self) -> CarcaraResult<(Token, Position)> {
        use std::mem::replace;

        self.poll_deadline()?;
        let (new_token, new_position) = self.lexer.next_token()?;
        // Modified in Clean: see `check_number_is_not_a_bound_symbol`.
        let new_number_symbol = self.lexer.take_number_symbol_reading();
        self.consumed_number_symbol = replace(&mut self.current_number_symbol, new_number_symbol);
        let old_token = replace(&mut self.current_token, new_token);
        let old_position = replace(&mut self.current_position, new_position);
        Ok((old_token, old_position))
    }

    /// Added in Clean: refuses once the deadline of this parse has passed (`parse_instance_until`).
    /// Cheap enough to poll once per token or term: it reads the clock once every few thousand
    /// polls (`checker/deadline.rs`).
    fn poll_deadline(&self) -> CarcaraResult<()> {
        if crate::checker::deadline::expired() {
            let err = ParserError::DeadlineExceeded;
            return Err(Error::Parser(err, self.current_position));
        }
        Ok(())
    }

    /// Inserts a new symbol into the parser symbol table, with the provided sort.
    fn declare_symbol(&mut self, symbol: String, sort: Rc<Sort>) {
        self.state.symbol_table.insert(HashCache::new(symbol), sort);
    }

    /// Modified in Clean: refuses, while parsing the problem, a number token (the one `next_token`
    /// last returned) where SMT-LIB reads a symbol that is declared, defined or bound here. The
    /// lexer reads `-5`, `-5x` and `-1/2` as numbers and `1/2x` as a rational, where SMT-LIB reads
    /// the symbols `-5`, `-5x` and `-1/2`, and `1` followed by the symbol `/2x`; so with `|-5|`
    /// declared, `(assert (= -5 3))` was refuted, and so was `(assert (= x 1/2))` with `/2`
    /// declared. A number whose SMT-LIB symbol is not in scope keeps its reading: SMT-LIB would
    /// refuse the script, and AY reads an undeclared `-5` as the numeral too. A proof keeps
    /// Carcara's numbers (`:args (-1)`), since its terms are judged as written (see
    /// third-party/carcara/DOWNSTREAM.md, fix 40).
    fn check_number_is_not_a_bound_symbol(&self, position: Position) -> CarcaraResult<()> {
        let Some(symbol) = &self.consumed_number_symbol else {
            return Ok(());
        };
        let bound = self
            .state
            .symbol_table
            .get(&HashCache::new(symbol.clone()))
            .is_some()
            || self.state.function_defs.contains_key(symbol);
        if self.problem.is_some() && bound {
            let err = ParserError::SymbolReadAsNumber(symbol.clone());
            return Err(Error::Parser(err, position));
        }
        Ok(())
    }

    /// Modified in Clean: the symbol table depth of the innermost *local* binding of `symbol` (a
    /// binder, `let`, `match` case, `define-fun` parameter or anchor argument), or `None` when
    /// `symbol` is global or unbound. Depth 0 is the global scope.
    fn local_binding_depth(&self, symbol: &str) -> Option<usize> {
        let cached = HashCache::new(symbol.to_owned());
        match self.state.symbol_table.get_with_depth(&cached) {
            Some((depth, _)) if depth > 0 => Some(depth),
            _ => None,
        }
    }

    /// Modified in Clean: the free variables of `term` whose names are bound locally here (see
    /// `local_binding_depth`), what `check_named_term_is_closed` and `expand_macro` ask of every
    /// named term and every use of a definition. Upstream's callers looked up each free variable
    /// of the term in the scopes, out of an `IndexSet` the pool cached for it: a chain of `n`
    /// definitions cost `n^2 / 2` entries, and as many lookups.
    ///
    /// Each answer is kept with the scopes it was computed in (a `ScopeState`: for each depth, the
    /// symbol table's generation there, `HashMapStack::generation_at`). It answers again wherever
    /// the table's scopes up to some depth are those it was computed in: the depth of its own
    /// scopes or, for an answer that holds no variable, one of the depths below (an answer that
    /// holds no variable at a depth holds none at any depth below, where fewer names are bound).
    /// Up to that depth the same names are bound, and each scope pushed inside it since adds only
    /// the names it binds, each looked up in the term's free variables (`carried_answer`). The
    /// answer for an application is the union of its children's whenever each child is a
    /// variable, a constant or a term with an answer here: its free variables are the union of
    /// theirs, and the names bound locally are the same for all of them. Any other term is
    /// answered from its free variables (`locally_bound`). So a chain of definitions used where
    /// many names are bound locally costs a few steps a link, also with a `let` or a binder
    /// entered and left between two links, and with each link read in binders of its own; and the
    /// pool is asked for a term's free variables only where they are looked in. See
    /// third-party/carcara/DOWNSTREAM.md, "Free-variable sets share structure".
    ///
    /// It polls the parse's deadline (see `parse_instance_until`).
    fn locally_bound_free_vars(&mut self, term: &Rc<Term>) -> CarcaraResult<FreeVars> {
        // Where no local scope binds a name (outside every local scope, or in the parameter scope
        // of a `define-fun` without parameters), no name is bound locally.
        if self.state.symbol_table.inner_len() == 0 {
            return Ok(FreeVars::default());
        }
        self.sync_scope_states();
        let set = match self.carried_answer(term)? {
            Some(set) => set,
            None => match self.locally_bound_from_children(term)? {
                Some(set) => set,
                None => {
                    #[cfg(test)]
                    {
                        self.state.answered_from_free_vars += 1;
                    }
                    let free = self.pool.free_vars(term);
                    self.locally_bound(&free)?
                }
            },
        };
        // Tests and unoptimized builds hold every answer to the one computed without the cache.
        #[cfg(any(test, debug_assertions))]
        {
            let free = self.pool.free_vars(term);
            let direct = self.locally_bound(&free)?;
            assert!(
                direct.len() == set.len() && direct.iter().all(|var| set.contains(var)),
                "the cached answer for '{term}' differs from its free variables'"
            );
        }
        let here = self.state.scope_states.last().cloned();
        let here = here.expect("a local scope has a state");
        let state = &mut self.state;
        state
            .locally_bound
            .insert(term.clone(), (set.clone(), here));
        // Once the answers are twice as many as the last sweep left (and at least
        // `ANSWERS_SWEEP_MIN`), those that answer nowhere now are dropped: a depth whose state
        // changed (a name bound there, or its scope left) never has that state again, since the
        // table gives each a generation it never had (`HashMapStack::generation`), so they would
        // never answer again. The answers then grow with the scopes the parser is in, as the
        // caches of each scope did before they were carried.
        let sweep_at = state.locally_bound_sweep_at.max(ANSWERS_SWEEP_MIN);
        if state.locally_bound.len() >= sweep_at {
            let (states, innermost) = (&state.scope_states, state.symbol_table.height() - 1);
            state.locally_bound.retain(|_, (answer, kept)| {
                answering_depth(states, innermost, answer.is_empty(), kept).is_some()
            });
            state.locally_bound_sweep_at = 2 * state.locally_bound.len();
        }
        Ok(set)
    }

    /// Modified in Clean: brings `scope_states` up to date with the symbol table: the state of each
    /// local scope's depth, innermost last. A depth whose generation is unchanged keeps its state,
    /// and so does every depth below it (`HashMapStack::generation_at`), so only the depths changed
    /// since the last call are rebuilt.
    fn sync_scope_states(&mut self) {
        let table = &self.state.symbol_table;
        let innermost = table.height() - 1;
        let states = &mut self.state.scope_states;
        states.truncate(innermost);
        while let Some(last) = states.last() {
            if last.generation == table.generation_at(last.depth) {
                break;
            }
            states.pop();
        }
        while states.len() < innermost {
            let depth = states.len() + 1;
            let outer = states.last().cloned();
            let generation = table.generation_at(depth);
            states.push(Arc::new(ScopeState { depth, generation, outer }));
        }
    }

    /// Modified in Clean: `locally_bound_free_vars` of `term` from the answer kept for it, if it
    /// has one that answers here (see there), or `None`. Of the states of the scopes the answer
    /// was computed in, the deepest that is the state of the table's scopes up to its depth now
    /// (looked for over at most `MAX_CARRY_STEPS` depths) fixes the names bound up to that depth;
    /// the names the scopes inside it bind are looked up in the term's free variables, unless
    /// they are more than answering from the free variables would take.
    fn carried_answer(&mut self, term: &Rc<Term>) -> CarcaraResult<Option<FreeVars>> {
        let Some((answer, kept)) = self.state.locally_bound.get(term) else {
            return Ok(None);
        };
        let innermost = self.state.symbol_table.height() - 1;
        let states = &self.state.scope_states;
        let Some(depth) = answering_depth(states, innermost, answer.is_empty(), kept) else {
            return Ok(None);
        };
        let answer = answer.clone();
        let table = &self.state.symbol_table;
        let added: usize = (depth + 1..=innermost).map(|d| table.scope_len(d)).sum();
        if added == 0 {
            return Ok(Some(answer));
        }
        // Answering from the free variables looks up each of them in the scopes, or each name
        // the scopes inside the outermost bind (at least `added`) in the free variables.
        let free = self.pool.free_vars(term);
        let table = &self.state.symbol_table;
        if added > free.len().saturating_mul(table.height()) {
            return Ok(None);
        }
        let mut set = answer;
        for depth in depth + 1..=innermost {
            for name in table.scope_keys(depth) {
                self.poll_deadline()?;
                for var in free.named(name.as_ref()) {
                    set = set.union(&FreeVars::singleton(var));
                }
            }
        }
        Ok(Some(set))
    }

    /// Modified in Clean: `locally_bound_free_vars` of an application `term` from its children's,
    /// or `None` when `term` binds names, or a child is neither a variable, a constant nor a term
    /// with an answer here (`carried_answer`).
    fn locally_bound_from_children(&mut self, term: &Rc<Term>) -> CarcaraResult<Option<FreeVars>> {
        fn known(p: &mut Parser, child: &Rc<Term>) -> CarcaraResult<Option<FreeVars>> {
            Ok(match child.as_ref() {
                Term::Var(name, _) if p.local_binding_depth(name).is_some() => {
                    Some(FreeVars::singleton(child))
                }
                Term::Var(..) | Term::Const(_) => Some(FreeVars::default()),
                _ => p.carried_answer(child)?,
            })
        }
        let mut set = FreeVars::default();
        match term.as_ref() {
            Term::Var(..) | Term::Const(_) => return known(self, term),
            Term::App(f, args) => {
                for child in std::iter::once(f).chain(args.iter()) {
                    let Some(answer) = known(self, child)? else {
                        return Ok(None);
                    };
                    set = set.union(&answer);
                }
            }
            Term::Op(_, args) | Term::ParamOp { args, .. } | Term::AsOp(_, _, args) => {
                for child in args {
                    let Some(answer) = known(self, child)? else {
                        return Ok(None);
                    };
                    set = set.union(&answer);
                }
            }
            // A binder, `let` or `match` removes the names it binds, which a union of its
            // children's answers would not: it is answered from its free variables.
            Term::Binder(..) | Term::Let(..) | Term::Match(..) => return Ok(None),
        }
        Ok(Some(set))
    }

    /// Modified in Clean: the variables of `free` whose names are bound locally here. A name is
    /// bound locally exactly when some scope but the outermost binds it, so the set is found by
    /// looking each such name up in `free`, or each variable of `free` up in the scopes, whichever
    /// is fewer lookups. It polls the parse's deadline.
    fn locally_bound(&self, free: &FreeVars) -> CarcaraResult<FreeVars> {
        let table = &self.state.symbol_table;
        let mut bound = FreeVars::default();
        if free.len().saturating_mul(table.height()) <= table.inner_len() {
            for var in free.iter() {
                self.poll_deadline()?;
                let name = var.as_var();
                if name.is_some_and(|name| self.local_binding_depth(name).is_some()) {
                    bound = bound.union(&FreeVars::singleton(var));
                }
            }
            return Ok(bound);
        }
        for name in table.inner_keys() {
            self.poll_deadline()?;
            for var in free.named(name.as_ref()) {
                bound = bound.union(&FreeVars::singleton(var));
            }
        }
        Ok(bound)
    }

    /// Modified in Clean: whether `symbol` should be read as the function definition (`define-fun`
    /// expanded as a macro, or `:named` term) of that name. A local binding of the same name
    /// shadows the definition, as it shadows any other global symbol; upstream expanded the
    /// definition anyway, so `(exists ((k Int)) (< k 0))` read the bound `k` as a `define-fun`
    /// constant `k` (see third-party/carcara/DOWNSTREAM.md, fix 36).
    fn is_macro_use(&self, symbol: &str) -> bool {
        self.state.function_defs.contains_key(symbol) && self.local_binding_depth(symbol).is_none()
    }

    /// Modified in Clean: whether the parser reads `symbol`, where no local binding shadows it, as
    /// a built-in operator rather than as a symbol of the script (`Operator`, a `QualifiedOperator`
    /// in `(as <op> <sort>)`, and with `allow_higher_order_indexed_ops` a `ParamOperator`). See
    /// third-party/carcara/DOWNSTREAM.md, fix 38.
    fn is_builtin_operator_name(&self, symbol: &str) -> bool {
        Operator::from_str(symbol).is_ok()
            || QualifiedOperator::from_str(symbol).is_ok()
            || (self.config.allow_higher_order_indexed_ops
                && ParamOperator::from_str(symbol).is_ok())
    }

    /// Modified in Clean: whether the innermost binding of `name` is a local sort parameter (of a
    /// `define-sort`, a `par` datatype, or a binder of sort `Type`). Such a parameter shadows a
    /// built-in sort of the same name; upstream read `Bool` in `(par (Bool) ((mk (val Bool))))` as
    /// the built-in `Bool` (see third-party/carcara/DOWNSTREAM.md, fix 38).
    fn is_local_sort_parameter(&mut self, name: &str) -> bool {
        self.local_binding_depth(name).is_some() && self.has_sort_symbol(name)
    }

    /// Modified in Clean: refuses, while parsing the problem, a global symbol (a declaration, a
    /// definition, a `:named` label, or a datatype constructor, selector or tester) whose name the
    /// parser would not keep apart from another meaning of the same name. A name read as a
    /// built-in operator stays the built-in at every use; a function definition takes precedence
    /// over every declaration of its name, before and after it; and a constant or function declared
    /// twice is one `Term::Var` with two meanings. Each of these let a refutation of a satisfiable
    /// script be certified: `(declare-fun x () Int) (assert (= y (! 5 :named x))) (assert (not (= x
    /// 5)))` was refuted by `(= x 5)` (see third-party/carcara/DOWNSTREAM.md, fix 38). A datatype
    /// symbol sharing a name with another global is judged by `check_global_symbol` (same-named
    /// fields of two datatypes stay legal).
    fn check_global_name_is_free(
        &self,
        symbol: &str,
        is_datatype_symbol: bool,
    ) -> CarcaraResult<()> {
        let declared_as_function = |symbol: &str| {
            self.state
                .global_symbols
                .get(symbol)
                .is_some_and(|earlier| earlier.iter().any(|(_, is_datatype)| !is_datatype))
        };
        let err = if self.is_builtin_operator_name(symbol) {
            ParserError::BuiltinNameDeclared(symbol.to_owned())
        } else if self.state.function_defs.contains_key(symbol)
            || (!is_datatype_symbol && declared_as_function(symbol))
        {
            ParserError::NameAlreadyInUse(symbol.to_owned())
        } else {
            return Ok(());
        };
        Err(Error::Parser(err, self.current_position))
    }

    /// Modified in Clean: refuses, while parsing the problem, a sort (`declare-sort`,
    /// `define-sort` or datatype) named like a built-in sort, which `make_sort` would keep reading
    /// as the built-in, or like a sort already declared or defined, which would make two sorts one
    /// (see third-party/carcara/DOWNSTREAM.md, fix 38). A datatype declared twice, or named like a
    /// declared or defined sort, is refused by `check_not_redeclared` and
    /// `check_sort_is_not_a_datatype`.
    fn check_sort_name_is_free(&self, name: &str) -> CarcaraResult<()> {
        let err = if BUILTIN_SORT_NAMES.contains(&name) {
            ParserError::BuiltinSortDeclared(name.to_owned())
        } else if self.state.sort_declarations.contains_key(name)
            || self.state.sort_defs.contains_key(name)
        {
            ParserError::SortRedeclared(name.to_owned())
        } else {
            return Ok(());
        };
        Err(Error::Parser(err, self.current_position))
    }

    /// Modified in Clean: expands the function definition `name` applied to `args`, hygienically.
    ///
    /// A free variable of the definition's body (other than its parameters) denotes the symbol it
    /// denoted where the definition was made: a global symbol of the problem. Upstream substituted
    /// the body as it stood, so where a binder rebinds that name the binder captured it: with
    /// `(define-fun k () Int x)`, `(define-fun h ((x Int)) Int k)` defined `h` as the identity
    /// instead of the constant `x`, and `(exists ((x Int)) (not (= k x)))` read as `false`. Here,
    /// when the innermost binding of such a name is the parameter scope of the `define-fun` being
    /// parsed, the expansion holds the global under a placeholder that `close_define_fun` resolves
    /// by renaming the parameter. Any other capture is refused while parsing the problem (a
    /// misread premise is what makes a refutation of a satisfiable problem possible). While
    /// parsing a proof it is kept, as upstream does: a proof's terms are judged by the rules as
    /// written, and Alethe producers rely on reusing a named term under a binder.
    fn expand_macro(
        &mut self,
        name: &str,
        args: Vec<Rc<Term>>,
        pos: Position,
    ) -> CarcaraResult<Rc<Term>> {
        let Some(func) = self.state.function_defs.get(name) else {
            let err = ParserError::UndefinedIden(name.to_owned());
            return Err(Error::Parser(err, pos));
        };
        let (params, body) = (func.params.clone(), func.body.clone());

        // Nothing can be captured outside every local scope, and in a proof only a `define-fun`
        // parameter scope changes the expansion.
        let nothing_to_check = self.state.symbol_table.height() == 1
            || (self.problem.is_none() && self.state.define_fun_scope.is_none());
        if nothing_to_check {
            return FunctionDef { params, body }
                .apply(self.pool, args)
                .map_err(|err| Error::Parser(err, pos));
        }

        let param_vars: IndexSet<Rc<Term>> = params
            .iter()
            .map(|param| self.pool.add(param.clone().into()))
            .collect();
        // Modified in Clean: only the free variables whose names are bound locally are read (see
        // `locally_bound_free_vars`, which asks the pool for the body's free variables only where
        // it cannot answer without them), in the order of their names. A capture refuses the
        // expansion whichever variable is found first, and the message names the one
        // `first_free_var` chooses; the order of `placeholders` changes nothing, since a
        // substitution's result does not depend on the order of its map (see
        // third-party/carcara/DOWNSTREAM.md, "Free-variable sets share structure").
        let mut bound: Vec<Rc<Term>> = self
            .locally_bound_free_vars(&body)?
            .iter()
            .filter(|var| !param_vars.contains(*var))
            .cloned()
            .collect();
        bound.sort_by(|a, b| a.as_var().cmp(&b.as_var()));
        let mut placeholders = IndexMap::new();
        let mut captured = FreeVars::default();
        for var in bound {
            let var_name = var.as_var().unwrap();
            let Some(depth) = self.local_binding_depth(var_name) else {
                continue;
            };
            match &self.state.define_fun_scope {
                Some(scope) if scope.depth == depth => {
                    let sort = self.pool.sort(&var);
                    let placeholder_name = format!("{var_name}{GLOBAL_PLACEHOLDER_SUFFIX}");
                    let placeholder = self.pool.add(Term::new_var(placeholder_name, sort));
                    placeholders.insert(var.clone(), placeholder);
                }
                _ if self.problem.is_some() => {
                    captured = captured.union(&FreeVars::singleton(&var));
                }
                _ => {}
            }
        }
        if captured.is_empty() {
            // Nothing is captured (`first_free_var` would compute the body's free variables).
        } else if let Some(var) = first_free_var(self.pool, &body, &captured) {
            let var_name = var.as_var().unwrap().to_owned();
            let err = ParserError::MacroCapture(name.to_owned(), var_name);
            return Err(Error::Parser(err, pos));
        }

        let body = if placeholders.is_empty() {
            body
        } else {
            if let Some(scope) = &mut self.state.define_fun_scope {
                for (var, placeholder) in &placeholders {
                    scope.placeholders.insert(placeholder.clone(), var.clone());
                }
            }
            Substitution::new(self.pool, placeholders)
                .expect("invariant: a placeholder has the sort of the variable it replaces")
                .apply(self.pool, &body)
        };
        FunctionDef { params, body }
            .apply(self.pool, args)
            .map_err(|err| Error::Parser(err, pos))
    }

    /// Modified in Clean: resolves the placeholders `expand_macro` introduced in the body of a
    /// `define-fun` (see `DefineFunScope`): each parameter that shadows a global symbol the body
    /// mentions gets an unforgeable fresh name, and each placeholder becomes that global again.
    /// Without placeholders the definition is returned unchanged.
    fn close_define_fun(
        &mut self,
        scope: DefineFunScope,
        params: Vec<SortedVar>,
        body: Rc<Term>,
    ) -> (Vec<SortedVar>, Rc<Term>) {
        if scope.placeholders.is_empty() {
            return (params, body);
        }
        let shadowed: IndexSet<String> = scope
            .placeholders
            .values()
            .filter_map(|var| var.as_var().map(str::to_owned))
            .collect();
        let mut renaming = IndexMap::new();
        let params: Vec<SortedVar> = params
            .into_iter()
            .map(|(name, sort)| {
                if !shadowed.contains(&name) {
                    return (name, sort);
                }
                let fresh = format!("{name}{RENAMED_PARAMETER_SUFFIX}");
                let old = self.pool.add(Term::new_var(name, sort.clone()));
                let new = self.pool.add(Term::new_var(fresh.clone(), sort.clone()));
                renaming.insert(old, new);
                (fresh, sort)
            })
            .collect();
        let body = Substitution::new(self.pool, renaming)
            .expect("invariant: a renamed parameter keeps its sort")
            .apply(self.pool, &body);
        let body = Substitution::new(self.pool, scope.placeholders)
            .expect("invariant: a placeholder has the sort of the variable it replaces")
            .apply(self.pool, &body);
        (params, body)
    }

    /// Modified in Clean: `term` with every placeholder of the enclosing `define-fun` (see
    /// `DefineFunScope`) replaced by the global it stands for. A `:named` term inside a
    /// `define-fun` body is a global definition, read where no parameter shadows anything, so its
    /// definition must not keep a placeholder that only `close_define_fun` would resolve.
    fn resolve_placeholders(&mut self, term: &Rc<Term>) -> Rc<Term> {
        let placeholders = match &self.state.define_fun_scope {
            Some(scope) if !scope.placeholders.is_empty() => scope.placeholders.clone(),
            _ => return term.clone(),
        };
        Substitution::new(self.pool, placeholders)
            .expect("invariant: a placeholder has the sort of the variable it replaces")
            .apply(self.pool, term)
    }

    /// Modified in Clean: refuses, while parsing the problem, a `:named` term that mentions a
    /// locally bound variable. SMT-LIB requires a named term to be closed; its name is a global
    /// definition, which a later use would otherwise read with that variable free or captured.
    fn check_named_term_is_closed(&mut self, name: &str, term: &Rc<Term>) -> CarcaraResult<()> {
        if self.problem.is_none() {
            return Ok(());
        }
        // Modified in Clean: the free variables bound locally are found by
        // `locally_bound_free_vars`, which asks the pool for the term's free variables only where
        // it cannot answer without them (outside every local scope it asks nothing), and the
        // message names the variable `first_free_var` chooses.
        let bound = self.locally_bound_free_vars(term)?;
        if bound.is_empty() {
            return Ok(());
        }
        if let Some(var) = first_free_var(self.pool, term, &bound) {
            let var_name = var.as_var().unwrap().to_owned();
            let err = ParserError::NamedTermNotClosed(name.to_owned(), var_name);
            return Err(Error::Parser(err, self.current_position));
        }
        Ok(())
    }

    /// Modified in Clean: refuses the script commands that would make the problem's premises
    /// differ from the query a proof certifies. Upstream ignored `push`, `pop`, `reset` and
    /// `reset-assertions`, kept every `check-sat-assuming` assumption as a permanent premise, read
    /// the assertions after a `check-sat` as part of the problem, and skipped every command it did
    /// not know, so `(assert p) (reset-assertions) (assert (not p))` and `(assert p)
    /// (check-sat-using smt) (assert (not p))` were refuted. A problem here is one query: its
    /// assertions are those before the first `check-sat`, `check-sat-assuming` (whose assumptions
    /// are added) or `exit`, or all of them when there is none, and after that point only commands
    /// that do not change the problem may follow. A command the parser does not read is refused,
    /// wherever it appears: an extension such as AY's `check-sat-using` may end a query or change
    /// the assertions in a way the parser cannot see. See third-party/carcara/DOWNSTREAM.md, fix
    /// 37.
    ///
    /// `define-fun-rec` and `define-funs-rec` are refused too (fix 39). SMT-LIB reads one as a
    /// declaration and a universally quantified equation, an axiom that need not be consistent:
    /// `(define-fun-rec f ((x Int)) Int (+ (f x) 1))` is unsatisfiable on its own, and was refuted
    /// with `forall_inst` and `la_generic`, while AY 0.27.0, which unfolds such a definition
    /// lazily, answers `sat` for it. A refutation through that axiom certifies the SMT-LIB reading
    /// against a producer's other reading, so it is refused rather than certified. No surveyed
    /// producer writes a recursive definition.
    fn check_script_command(
        token: &Token,
        query_end: &mut Option<String>,
        position: Position,
    ) -> CarcaraResult<()> {
        let command = match token {
            Token::ReservedWord(reserved) => reserved.to_string(),
            Token::Symbol(symbol) if Reserved::from_str(symbol).is_err() => symbol.clone(),
            // A quoted symbol spelling a reserved command (`(|assert| p)`) is not the command to
            // this parser, which would skip it.
            Token::Symbol(symbol) => {
                let err = ParserError::UnknownScriptCommand(format!("|{symbol}|"));
                return Err(Error::Parser(err, position));
            }
            other => {
                let err = ParserError::UnexpectedToken(other.clone());
                return Err(Error::Parser(err, position));
            }
        };
        let ends_query = match command.as_str() {
            "push" | "pop" | "reset" | "reset-assertions" => {
                let err = ParserError::UnsupportedScriptCommand(command);
                return Err(Error::Parser(err, position));
            }
            "define-fun-rec" | "define-funs-rec" => {
                let err = ParserError::RecursiveDefinitionRefused(command);
                return Err(Error::Parser(err, position));
            }
            "check-sat" | "check-sat-assuming" => true,
            "exit" => {
                query_end.get_or_insert(command);
                return Ok(());
            }
            "assert" | "declare-fun" | "declare-const" | "declare-sort" | "declare-datatype"
            | "declare-datatypes" | "define-fun" | "define-sort" | "set-logic" => false,
            other if READ_ONLY_COMMANDS.contains(&other) => return Ok(()),
            _ => {
                let err = ParserError::UnknownScriptCommand(command);
                return Err(Error::Parser(err, position));
            }
        };
        if let Some(end) = query_end {
            let err = ParserError::CommandAfterQueryEnd(command, end.clone());
            return Err(Error::Parser(err, position));
        }
        if ends_query {
            *query_end = Some(command);
        }
        Ok(())
    }

    /// Modified in Clean: records a global (problem-level) symbol, refusing an ambiguous datatype
    /// symbol.
    ///
    /// Carcara resolves an application by the symbol's name alone (the later declaration wins),
    /// and a `Term::Var` carries only a name and a sort. So when a datatype constructor, selector
    /// or tester and another global declaration share a name and their argument sorts (see
    /// `symbol_domains_overlap`), the script is ambiguous and Carcara would silently read every
    /// later use as the second declaration; with equal sorts the two would even be one term with
    /// two meanings. The `dt_project` rule reads such a symbol as the datatype's own, so the
    /// declaration that creates the ambiguity is refused, in either order. Such a script is
    /// ill-formed SMT-LIB (a symbol may be declared only once, and an overload needs argument
    /// sorts that tell it apart). Same-named symbols with different argument sorts stay legal: a
    /// use of the earlier one after the later is a sort error, never a misreading. Every other
    /// reuse of a name, and a name read as a built-in operator, is refused by
    /// `check_global_name_is_free` (fix 38; upstream let the later declaration shadow the
    /// earlier one).
    fn record_global_symbol(
        &mut self,
        symbol: &str,
        sort: &Rc<Sort>,
        is_datatype_symbol: bool,
    ) -> CarcaraResult<()> {
        self.check_global_symbol(symbol, sort, is_datatype_symbol)?;
        // Modified in Clean (fix 38): see `check_global_name_is_free`.
        self.check_global_name_is_free(symbol, is_datatype_symbol)?;
        self.state
            .global_symbols
            .entry(symbol.to_owned())
            .or_default()
            .push((sort.clone(), is_datatype_symbol));
        Ok(())
    }

    /// Modified in Clean: the check of `record_global_symbol`, without recording the symbol. Used
    /// for the definitions a proof introduces (`define-fun`, `:named`), which only refer to
    /// datatypes declared before them.
    fn check_global_symbol(
        &self,
        symbol: &str,
        sort: &Rc<Sort>,
        is_datatype_symbol: bool,
    ) -> CarcaraResult<()> {
        let ambiguous = self
            .state
            .global_symbols
            .get(symbol)
            .is_some_and(|earlier| {
                earlier
                    .iter()
                    .any(|(earlier_sort, earlier_is_datatype_symbol)| {
                        (*earlier_is_datatype_symbol || is_datatype_symbol)
                            && symbol_domains_overlap(earlier_sort, sort)
                    })
            });
        if ambiguous {
            let err = ParserError::AmbiguousDatatypeSymbol(symbol.to_owned());
            return Err(Error::Parser(err, self.current_position));
        }
        Ok(())
    }

    /// Modified in Clean: the sort of the symbol a `define-fun` (or `:named`) defines.
    fn function_def_sort(&mut self, func_def: &FunctionDef) -> Rc<Sort> {
        let body_sort = self.pool.sort(&func_def.body);
        if func_def.params.is_empty() {
            return body_sort;
        }
        let mut sorts: Vec<_> = func_def.params.iter().map(|(_, s)| s.clone()).collect();
        sorts.push(body_sort);
        self.pool.add_sort(Sort::Function(sorts))
    }

    /// Modified in Clean: records (while parsing the problem) or checks (while parsing a proof) a
    /// symbol that a `define-fun` expanded as a macro or a `:named` attribute defines. Either takes
    /// precedence over the symbol table when a term is parsed, so it is a global symbol like any
    /// other (see `record_global_symbol`).
    fn record_function_def(&mut self, name: &str, func_def: &FunctionDef) -> CarcaraResult<()> {
        let sort = self.function_def_sort(func_def);
        if self.problem.is_some() {
            self.record_global_symbol(name, &sort, false)
        } else {
            self.check_global_symbol(name, &sort, false)
        }
    }

    /// Modified in Clean: declares a global (problem-level) symbol, after
    /// `record_global_symbol` has accepted it.
    fn declare_global_symbol(
        &mut self,
        symbol: String,
        sort: Rc<Sort>,
        is_datatype_symbol: bool,
    ) -> CarcaraResult<()> {
        self.record_global_symbol(&symbol, &sort, is_datatype_symbol)?;
        self.declare_symbol(symbol, sort);
        Ok(())
    }

    /// Modified in Clean: refuses a `declare-sort` or `define-sort` of a name that is already a
    /// datatype. The other order is refused by `check_not_redeclared` (`parser/datatypes.rs`).
    fn check_sort_is_not_a_datatype(&self, name: &str) -> CarcaraResult<()> {
        if self.state.datatype_declarations.get(name).is_some() {
            let err = ParserError::DatatypeSortRedeclared(name.to_owned());
            return Err(Error::Parser(err, self.current_position));
        }
        Ok(())
    }

    /// Searches the symbol table for a symbol, and, if found, returns its sort.
    fn get_symbol(&mut self, symbol: &str) -> Option<&Rc<Sort>> {
        let cached = HashCache::new(symbol.to_owned());
        self.state.symbol_table.get(&cached)
    }

    /// Returns `true` if the symbol table has a symbol with that name, and its sort is
    /// `Sort::Type`.
    fn has_sort_symbol(&mut self, symbol: &str) -> bool {
        self.get_symbol(symbol)
            .is_some_and(|sort| *sort.as_ref() == Sort::Type)
    }

    /// Compares two sorts according to the sort checking configuration. Return `true` if they are
    /// considered equal.
    fn compare_sort(&self, a: &Sort, b: &Sort) -> bool {
        if self.config.relaxed_sort_checking {
            a.is_compatible_with(b)
        } else {
            a.param_eq(b)
        }
    }

    /// Returns a sort error if `got` does not equal `expected`.
    fn check_sort_eq(&mut self, expected: &Sort, got: &Rc<Sort>) -> Result<(), SortError> {
        if self.compare_sort(expected, got) {
            Ok(())
        } else {
            let expected = self.pool.add_sort(expected.clone());
            Err(SortError {
                expected: vec![expected].into_boxed_slice(),
                got: got.clone(),
            })
        }
    }

    /// Makes sure all terms in `sequence` are equal to each other, otherwise returns an error.
    fn check_sort_all_eq(&mut self, sequence: &[Rc<Sort>]) -> Result<(), SortError> {
        for i in 1..sequence.len() {
            self.check_sort_eq(&sequence[i - 1], &sequence[i])?;
        }
        Ok(())
    }

    /// Returns a sort error if `got` is not one of `possibilities`.
    fn check_sort_one_of(
        &mut self,
        possibilities: &[Sort],
        got: &Rc<Sort>,
    ) -> Result<(), SortError> {
        if possibilities.iter().any(|p| self.compare_sort(p, got)) {
            Ok(())
        } else {
            let expected: Vec<_> = possibilities
                .iter()
                .map(|s| self.pool.add_sort(s.clone()))
                .collect();

            Err(SortError {
                expected: expected.into_boxed_slice(),
                got: got.clone(),
            })
        }
    }

    /// Makes sure `got` is a valid `Array` sort, with the given key and value sorts.
    fn check_array_sort(
        &mut self,
        key: Option<&Rc<Sort>>,
        value: Option<&Rc<Sort>>,
        got: &Rc<Sort>,
    ) -> Result<(), SortError> {
        let any = self.pool.add_sort(Sort::Atom("?".into(), Box::new([])));

        let expected = {
            let [key, value] = [key, value].map(|s| s.cloned().unwrap_or_else(|| any.clone()));
            vec![self.pool.add_sort(Sort::Array(key, value))].into_boxed_slice()
        };
        let Sort::Array(got_key, got_value) = got.as_ref() else {
            return Err(SortError { expected, got: got.clone() });
        };
        if key.is_some_and(|k| !self.compare_sort(got_key, k))
            || value.is_some_and(|v| !self.compare_sort(got_value, v))
        {
            return Err(SortError { expected, got: got.clone() });
        }
        Ok(())
    }

    /// Shortcut for `self.problem.as_mut().unwrap().prelude`
    fn prelude(&mut self) -> &mut ProblemPrelude {
        &mut self.problem.as_mut().unwrap().prelude
    }

    /// Shortcut for `self.problem.as_mut().unwrap().premises`
    fn premises(&mut self) -> &mut IndexSet<Rc<Term>> {
        &mut self.problem.as_mut().unwrap().premises
    }

    /// Constructs and sort checks a variable term.
    fn make_var(&mut self, iden: String) -> Result<Rc<Term>, ParserError> {
        let cached = HashCache::new(iden);
        let sort = match self.state.symbol_table.get(&cached) {
            Some(s) => s.clone(),
            None => return Err(ParserError::UndefinedIden(cached.unwrap())),
        };
        Ok(self.pool.add(Term::Var(cached.unwrap(), sort)))
    }

    /// Return whether we should interpret integer constants as `Real`s.
    ///
    /// If we are working with a logic that contains reals but does not contain integers, and if we
    /// are parsing the problem and not the poof, this will be true.
    fn interpret_ints_as_reals(&self) -> bool {
        self.is_real_only_logic && self.problem.is_some()
    }

    /// Constructs and sort checks an operation term.
    fn make_op(&mut self, op: Operator, args: Vec<Rc<Term>>) -> Result<Rc<Term>, ParserError> {
        let sorts: Vec<_> = args.iter().map(|t| self.pool.sort(t)).collect();

        match op {
            Operator::True | Operator::False => assert_num_args(&args, 0)?,
            Operator::Not => {
                assert_num_args(&args, 1)?;
                self.check_sort_eq(&Sort::Bool, &sorts[0])?;
            }
            Operator::Implies => {
                assert_num_args(&args, 2..)?;
                for s in sorts {
                    self.check_sort_eq(&Sort::Bool, &s)?;
                }
            }
            Operator::Or | Operator::And | Operator::Xor => {
                // If we are not in "strict" parsing mode, we allow these operators to be called
                // with just one argument
                assert_num_args(&args, if self.config.strict { 2.. } else { 1.. })?;
                for s in sorts {
                    self.check_sort_eq(&Sort::Bool, &s)?;
                }
            }
            Operator::Equals | Operator::Distinct => {
                assert_num_args(&args, 2..)?;
                self.check_sort_all_eq(&sorts)?;
            }
            Operator::Ite => {
                assert_num_args(&args, 3)?;
                self.check_sort_eq(&Sort::Bool, &sorts[0])?;
                self.check_sort_eq(sorts[1].as_ref(), &sorts[2])?;
            }
            Operator::Add | Operator::Sub | Operator::Mult => {
                // The `-` operator, in particular, can be called with only one argument, in which
                // case it means negation instead of subtraction
                if op == Operator::Sub {
                    assert_num_args(&args, 1..)?;
                } else {
                    assert_num_args(&args, 2..)?;
                }

                // All the arguments must be either Int or Real. Also, if we are not allowing
                // Int/Real subtyping, all arguments must have the same sort
                if self.config.allow_int_real_subtyping {
                    for s in sorts {
                        self.check_sort_one_of(&[Sort::Int, Sort::Real], &s)?;
                    }
                } else {
                    self.check_sort_one_of(&[Sort::Int, Sort::Real], &sorts[0])?;
                    self.check_sort_all_eq(&sorts)?;
                }
            }
            Operator::IntDiv => {
                assert_num_args(&args, 2..)?;
                self.check_sort_eq(&Sort::Int, &sorts[0])?;
                self.check_sort_all_eq(&sorts)?;
            }
            Operator::RealDiv => {
                assert_num_args(&args, 2..)?;

                // Normally, the `/` operator may only receive Real arguments, but if we are
                // allowing Int/Real subtyping, it may also receive Ints
                if self.config.allow_int_real_subtyping {
                    for s in sorts {
                        self.check_sort_one_of(&[Sort::Int, Sort::Real], &s)?;
                    }
                } else {
                    self.check_sort_eq(&Sort::Real, &sorts[0])?;
                    self.check_sort_all_eq(&sorts)?;
                }

                if let Some(r) = self.interpret_div_as_real_lit(&args[0], &args[1]) {
                    return Ok(r);
                }
            }
            Operator::Mod => {
                assert_num_args(&args, 2)?;
                self.check_sort_eq(&Sort::Int, &sorts[0])?;
                self.check_sort_eq(&Sort::Int, &sorts[1])?;
            }
            Operator::Abs => {
                assert_num_args(&args, 1)?;
                // The argument must be Int unless we are allowing Int/Real subtyping
                if self.config.allow_int_real_subtyping {
                    self.check_sort_one_of(&[Sort::Int, Sort::Real], &sorts[0])?;
                } else {
                    self.check_sort_eq(&Sort::Int, &sorts[0])?;
                }
            }
            Operator::LessThan | Operator::GreaterThan | Operator::LessEq | Operator::GreaterEq => {
                assert_num_args(&args, 2..)?;
                // All the arguments must be either Int or Real sorted, but they don't need to all
                // have the same sort
                for s in sorts {
                    self.check_sort_one_of(&[Sort::Int, Sort::Real], &s)?;
                }
            }
            Operator::ToReal => {
                assert_num_args(&args, 1)?;
                // If the logic contains reals but not integers, integer constants are interpreted
                // as reals, so the argument might have sort Real instead of the expected Int
                self.check_sort_one_of(&[Sort::Int, Sort::Real], &sorts[0])?;
            }
            Operator::ToInt | Operator::IsInt => {
                assert_num_args(&args, 1)?;
                self.check_sort_eq(&Sort::Real, &sorts[0])?;
            }
            Operator::Select => {
                assert_num_args(&args, 2)?;
                self.check_array_sort(Some(&sorts[1]), None, &sorts[0])?;
            }
            Operator::Store => {
                assert_num_args(&args, 3)?;
                self.check_array_sort(Some(&sorts[1]), Some(&sorts[2]), &sorts[0])?;
            }
            Operator::StrConcat => {
                assert_num_args(&args, 2..)?;
                for s in sorts {
                    self.check_sort_eq(&Sort::String, &s)?;
                }
            }
            Operator::StrLen | Operator::StrIsDigit | Operator::StrToCode | Operator::StrToInt => {
                assert_num_args(&args, 1)?;
                self.check_sort_eq(&Sort::String, &sorts[0])?;
            }
            Operator::StrLessThan
            | Operator::StrLessEq
            | Operator::PrefixOf
            | Operator::SuffixOf
            | Operator::Contains
            | Operator::ReRange => {
                assert_num_args(&args, 2)?;
                self.check_sort_eq(&Sort::String, &sorts[0])?;
                self.check_sort_eq(&Sort::String, &sorts[1])?;
            }
            Operator::CharAt => {
                assert_num_args(&args, 2)?;
                self.check_sort_eq(&Sort::String, &sorts[0])?;
                self.check_sort_eq(&Sort::Int, &sorts[1])?;
            }
            Operator::Substring => {
                assert_num_args(&args, 3)?;
                self.check_sort_eq(&Sort::String, &sorts[0])?;
                self.check_sort_eq(&Sort::Int, &sorts[1])?;
                self.check_sort_eq(&Sort::Int, &sorts[2])?;
            }
            Operator::IndexOf => {
                assert_num_args(&args, 3)?;
                self.check_sort_eq(&Sort::String, &sorts[0])?;
                self.check_sort_eq(&Sort::String, &sorts[1])?;
                self.check_sort_eq(&Sort::Int, &sorts[2])?;
            }
            Operator::IndexOfRe => {
                assert_num_args(&args, 3)?;
                self.check_sort_eq(&Sort::String, &sorts[0])?;
                self.check_sort_eq(&Sort::RegLan, &sorts[1])?;
                self.check_sort_eq(&Sort::Int, &sorts[2])?;
            }
            Operator::Replace | Operator::ReplaceAll => {
                assert_num_args(&args, 3)?;
                self.check_sort_eq(&Sort::String, &sorts[0])?;
                self.check_sort_eq(&Sort::String, &sorts[1])?;
                self.check_sort_eq(&Sort::String, &sorts[2])?;
            }
            Operator::ReFromAutomaton => {
                assert_num_args(&args, 1)?;
                self.check_sort_eq(&Sort::String, &sorts[0])?;
                if let Term::Const(Constant::String(s)) = args[0].as_ref() {
                    let automata = match parse_automaton(s.trim()) {
                        Ok((remaining, automata)) => {
                            if !remaining.is_empty() {
                                return Err(ParserError::InvalidAutomatonDeclaration(s.clone()));
                            }
                            Ok(automata)
                        }
                        Err(_) => Err(ParserError::InvalidAutomatonDeclaration(s.clone())),
                    }?;
                    return Ok(self
                        .pool
                        .add(Term::Const(Constant::RegLan(s.to_owned(), automata))));
                } else {
                    return Err(ParserError::ExpectedAnAutomatonDeclaration(args[0].clone()));
                }
            }
            Operator::StrFromCode | Operator::StrFromInt => {
                assert_num_args(&args, 1)?;
                self.check_sort_eq(&Sort::Int, &sorts[0])?;
            }
            Operator::StrToRe => {
                assert_num_args(&args, 1)?;
                self.check_sort_eq(&Sort::String, &sorts[0])?;
            }
            Operator::StrInRe => {
                assert_num_args(&args, 2)?;
                self.check_sort_eq(&Sort::String, &sorts[0])?;
                self.check_sort_eq(&Sort::RegLan, &sorts[1])?;
            }
            Operator::ReNone | Operator::ReAll | Operator::ReAllChar => {
                assert_num_args(&args, 0)?;
            }
            Operator::ReConcat
            | Operator::ReUnion
            | Operator::ReIntersection
            | Operator::ReDiff => {
                assert_num_args(&args, 2..)?;
                for s in sorts {
                    self.check_sort_eq(&Sort::RegLan, &s)?;
                }
            }
            Operator::ReKleeneClosure
            | Operator::ReComplement
            | Operator::ReKleeneCross
            | Operator::ReOption => {
                assert_num_args(&args, 1)?;
                self.check_sort_eq(&Sort::RegLan, &sorts[0])?;
            }
            Operator::ReplaceRe | Operator::ReplaceReAll => {
                assert_num_args(&args, 3)?;
                self.check_sort_eq(&Sort::String, &sorts[0])?;
                self.check_sort_eq(&Sort::RegLan, &sorts[1])?;
                self.check_sort_eq(&Sort::String, &sorts[2])?;
            }
            Operator::BvNot | Operator::BvNeg => {
                assert_num_args(&args, 1)?;
                for s in sorts {
                    if !s.is_bitvec() {
                        return Err(ParserError::ExpectedBvSort(s));
                    }
                }
            }
            Operator::BvSize | Operator::UBvToInt | Operator::SBvToInt => {
                assert_num_args(&args, 1)?;
                if !sorts[0].is_bitvec() {
                    return Err(ParserError::ExpectedBvSort(sorts[0].clone()));
                }
            }
            Operator::BvBbTerm => {
                assert_num_args(&args, 1..)?;
                self.check_sort_eq(&Sort::Bool, &sorts[0])?;
                self.check_sort_all_eq(&sorts)?;
            }
            Operator::BvPBbTerm => {
                assert_num_args(&args, 1..)?;
                self.check_sort_eq(&Sort::Int, &sorts[0])?;
                self.check_sort_all_eq(&sorts)?;
            }
            Operator::BvConst => {
                assert_num_args(&args, 2)?;
                self.check_sort_eq(&Sort::Int, &sorts[0])?;
                self.check_sort_eq(&Sort::Int, &sorts[1])?;
            }
            Operator::BvConcat => {
                assert_num_args(&args, 2..)?;
                // Modified in Clean: the result width is the operands' sum, which
                // `TermPool::compute_sort` adds unchecked and cannot refuse, so a sum that does not
                // fit `usize` is refused here (third-party/carcara/DOWNSTREAM.md, "Also hardened").
                // A `ParamBitVec` operand has no width to add.
                let mut width = 0usize;
                for s in sorts {
                    match s.as_ref() {
                        Sort::BitVec(w) => {
                            width = width
                                .checked_add(*w)
                                .ok_or_else(|| ParserError::BitVecWidthOverflow("concat".into()))?;
                        }
                        Sort::ParamBitVec => {}
                        _ => return Err(ParserError::ExpectedBvSort(s)),
                    }
                }
            }
            Operator::Cl => {}
            Operator::Delete => {
                self.check_sort_eq(&Sort::Bool, &sorts[0])?;
                assert_num_args(&args, 1)?;
            }
            Operator::BvAdd
            | Operator::BvMul
            | Operator::BvAnd
            | Operator::BvOr
            | Operator::BvXor => {
                assert_num_args(&args, 2..)?;
                if !sorts[0].is_bitvec() {
                    return Err(ParserError::ExpectedBvSort(sorts[0].clone()));
                }
                self.check_sort_all_eq(&sorts)?;
            }
            Operator::BvUDiv
            | Operator::BvURem
            | Operator::BvShl
            | Operator::BvLShr
            | Operator::BvULt
            | Operator::BvNAnd
            | Operator::BvNOr
            | Operator::BvXNor
            | Operator::BvComp
            | Operator::BvSub
            | Operator::BvSDiv
            | Operator::BvSRem
            | Operator::BvSMod
            | Operator::BvAShr
            | Operator::BvULe
            | Operator::BvUGt
            | Operator::BvUGe
            | Operator::BvSLt
            | Operator::BvSLe
            | Operator::BvSGt
            | Operator::BvSGe => {
                assert_num_args(&args, 2)?;
                if !sorts[0].is_bitvec() {
                    return Err(ParserError::ExpectedBvSort(sorts[0].clone()));
                }
                self.check_sort_all_eq(&sorts)?;
            }
            Operator::RareList => (),
            Operator::Pow2 | Operator::Log2 | Operator::IsPow2 => {
                assert_num_args(&args, 1)?;
                self.check_sort_eq(&Sort::Int, &sorts[0])?;
            }
            Operator::RealPi => assert_num_args(&args, 0)?,
            Operator::Sqrt
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
            | Operator::Arccot => {
                assert_num_args(&args, 1)?;
                self.check_sort_eq(&Sort::Real, &sorts[0])?;
            }
            Operator::SetUnion | Operator::SetInter | Operator::SetMinus | Operator::SetSubset => {
                assert_num_args(&args, 2)?;
                self.check_sort_all_eq(&sorts)?;
                for sort in sorts {
                    check_set_sort(&sort)?;
                }
            }
            Operator::SetMember => {
                assert_num_args(&args, 2)?;
                let expected = self.pool.add_sort(Sort::Set(sorts[0].clone()));
                self.check_sort_eq(&expected, &sorts[1])?;
            }
            Operator::SetSingleton => {
                assert_num_args(&args, 1)?;
            }
            Operator::SetIsEmpty
            | Operator::SetIsSingleton
            | Operator::SetCard
            | Operator::SetComplement => {
                assert_num_args(&args, 1)?;
                check_set_sort(&sorts[0])?;
            }
            Operator::SetInsert => {
                assert_num_args(&args, 2..)?;
                self.check_sort_all_eq(&sorts[..sorts.len() - 1])?;
                let expected = self.pool.add_sort(Sort::Set(sorts[0].clone()));
                self.check_sort_eq(&expected, sorts.last().unwrap())?;
            }
            Operator::Tuple => {
                assert_num_args(&args, 1..)?;
            }
            Operator::TupleUnit => {
                assert_num_args(&args, 0)?;
            }
            Operator::RelTranspose => {
                assert_num_args(&args, 1)?;
                check_relation_sort(&sorts[0])?;
            }
            Operator::RelTclosure => {
                assert_num_args(&args, 1)?;
                check_relation_sort(&sorts[0])?;
                let Sort::Set(tuple) = sorts[0].as_ref() else {
                    unreachable!()
                };
                let Sort::Tuple(elems) = tuple.as_ref() else {
                    unreachable!()
                };
                if elems.len() != 2 {
                    // Hacky way to print an error saying the relation should be binary
                    let any = self.pool.add_sort(Sort::Var("?".into()));
                    let tuple = self.pool.add_sort(Sort::Tuple(vec![any.clone(), any]));
                    let expected = vec![self.pool.add_sort(Sort::Set(tuple))].into_boxed_slice();
                    return Err(SortError { expected, got: sorts[0].clone() }.into());
                }
            }
            Operator::RelJoin => {
                assert_num_args(&args, 2)?;
                check_relation_sort(&sorts[0])?;
                check_relation_sort(&sorts[1])?;
                // TODO: check properly
            }
            Operator::RelProduct => {
                assert_num_args(&args, 2)?;
                check_relation_sort(&sorts[0])?;
                check_relation_sort(&sorts[1])?;
            }
        }
        Ok(self.pool.add(Term::Op(op, args)))
    }

    fn interpret_div_as_real_lit(&mut self, a: &Rc<Term>, b: &Rc<Term>) -> Option<Rc<Term>> {
        // If the term is a division between two positive integer constants, and their GCD is 1,
        // then it should be interpreted as a rational literal. The only exception to this is the
        // term '(/ 1 1)', which is still interpreted as a division term.

        let [a, b] = [a, b].map(|t| match t.as_ref() {
            Term::Const(Constant::Integer(i)) => Some(i),
            Term::Const(Constant::Real(r)) if self.interpret_ints_as_reals() && r.is_integer() => {
                Some(r.numer())
            }
            _ => None,
        });
        let [a, b] = [a?, b?];

        if *a > 0 && *b > 0 && !(*a == 1 && *b == 1) && a.clone().gcd(b) == 1 {
            Some(self.pool.add(Term::new_real(Rational::from((a, b)))))
        } else {
            None
        }
    }

    /// Constructs and sort checks an application term.
    fn make_app(
        &mut self,
        function: Rc<Term>,
        args: Vec<Rc<Term>>,
    ) -> Result<Rc<Term>, ParserError> {
        let sort = self.pool.sort(&function);
        let mut param_function = false;
        let sorts = {
            if let Sort::Function(sorts) = sort.as_ref() {
                sorts
            } else if let Sort::Par(_, p_sort) = sort.as_ref() {
                if let Sort::Function(sorts) = p_sort.as_ref() {
                    param_function = true;
                    sorts
                } else {
                    // Parametric function does not have function sort
                    return Err(ParserError::NotAFunction(p_sort.clone()));
                }
            } else {
                // Function does not have function sort
                return Err(ParserError::NotAFunction(sort.clone()));
            }
        };
        // We allow partial application
        assert_num_args(&args, 1..sorts.len())?;
        let mut map = IndexMap::new();
        for i in 0..args.len() {
            let arg_sort_i = self.pool.sort(&args[i]);
            if param_function {
                if !sorts[i].match_with(&arg_sort_i, &mut map) {
                    return Err(ParserError::IncompatibleSorts(
                        sorts[i].clone(),
                        arg_sort_i.clone(),
                    ));
                }
                continue;
            };
            self.check_sort_eq(&sorts[i], &arg_sort_i)?;
        }
        Ok(self.pool.add(Term::App(function, args)))
    }

    /// Consumes the current token if it equals `expected`. Returns an error otherwise.
    fn expect_token(&mut self, expected: Token) -> CarcaraResult<()> {
        let (got, pos) = self.next_token()?;
        if got == expected {
            Ok(())
        } else {
            Err(Error::Parser(ParserError::UnexpectedToken(got), pos))
        }
    }

    /// Consumes the current token if it is a symbol, and returns the inner `String`. Returns an
    /// error otherwise.
    fn expect_symbol(&mut self) -> CarcaraResult<String> {
        match self.next_token()? {
            (Token::Symbol(s), _) => Ok(s),
            (other, pos) => Err(Error::Parser(ParserError::UnexpectedToken(other), pos)),
        }
    }

    /// Consumes the current token if it is a keyword, and returns the inner `String`. Returns an
    /// error otherwise.
    fn expect_keyword(&mut self) -> CarcaraResult<String> {
        match self.next_token()? {
            (Token::Keyword(s), _) => Ok(s),
            (other, pos) => Err(Error::Parser(ParserError::UnexpectedToken(other), pos)),
        }
    }

    /// Consumes the current token if it is a numeral, and returns the inner `Integer`. Returns an
    /// error otherwise.
    fn expect_numeral(&mut self) -> CarcaraResult<Integer> {
        match self.next_token()? {
            (Token::Numeral(n), _) => Ok(n),
            (other, pos) => Err(Error::Parser(ParserError::UnexpectedToken(other), pos)),
        }
    }

    /// Calls `parse_func` repeatedly until a closing parenthesis is reached.
    ///
    /// If `non_empty` is true, empty sequences will result in an error. This method consumes the
    /// ending `)` token.
    fn parse_sequence<T, F>(&mut self, mut parse_func: F, non_empty: bool) -> CarcaraResult<Vec<T>>
    where
        F: FnMut(&mut Self) -> CarcaraResult<T>,
    {
        let mut result = Vec::new();
        while self.current_token != Token::CloseParen {
            result.push(parse_func(self)?);
        }
        if non_empty && result.is_empty() {
            Err(Error::Parser(
                ParserError::EmptySequence,
                self.current_position,
            ))
        } else {
            self.next_token()?; // Consume `)` token
            Ok(result)
        }
    }

    /// Reads tokens until the matching closing parenthesis is reached.
    fn read_until_close_parens(&mut self) -> CarcaraResult<Vec<Token>> {
        let mut result = Vec::new();
        let mut parens_depth = 1;
        while parens_depth > 0 {
            let token = self.next_token()?;
            parens_depth += match token {
                (Token::OpenParen, _) => 1,
                (Token::CloseParen, _) => -1,
                (Token::Eof, pos) => {
                    return Err(Error::Parser(ParserError::UnexpectedToken(Token::Eof), pos));
                }
                _ => 0,
            };
            result.push(token.0);
        }
        Ok(result)
    }

    /// Consumes and drops tokens until the matching closing parenthesis is reached.
    fn ignore_until_close_parens(&mut self) -> CarcaraResult<()> {
        self.read_until_close_parens()?;
        Ok(())
    }

    /// Consumes and ignores attributes and their values until a closing parenthesis is reached.
    fn ignore_remaining_attributes(&mut self) -> CarcaraResult<()> {
        while let Token::Keyword(_) = self.current_token {
            self.next_token()?;
            match self.current_token {
                // If we reached the closing parenthesis or the end of the file, we stop
                Token::CloseParen | Token::Eof => break,

                // If there is no value for this attribute, we may encounter the next attribute, in
                // which case we must continue without consuming the keyword token
                Token::Keyword(_) => (),

                // If there is a single token as a value we consume it
                Token::Symbol(_)
                | Token::Numeral(_)
                | Token::Decimal(_)
                | Token::Bitvector(_, _)
                | Token::String(_)
                | Token::ReservedWord(_) => {
                    self.next_token()?;
                }

                // And if the value is an s-expression we read tokens until it's closed
                Token::OpenParen => {
                    self.next_token()?;
                    self.ignore_until_close_parens()?;
                }
            }
            if self.current_token == Token::CloseParen {
                break;
            }
        }
        Ok(())
    }

    /// Reads an SMT-LIB script and parses the assertions, declarations and definitions.
    ///
    /// The following commands are parsed:
    ///
    /// - `assert`
    /// - `declare-const`
    /// - `declare-fun`
    /// - `declare-sort`
    /// - `define-fun`
    /// - `set-logic`
    ///
    /// All other commands are ignored. This method returns a hash set containing the premises
    /// introduced in `assert` commands.
    pub fn parse_problem(&mut self) -> CarcaraResult<Problem> {
        self.problem = Some(Problem::new());

        // Modified in Clean: the command that ended the query, if any (see
        // `check_script_command`).
        let mut query_end = None;

        while self.current_token != Token::Eof {
            self.expect_token(Token::OpenParen)?;
            let (command, position) = self.next_token()?;
            // Modified in Clean: see `check_script_command`.
            Self::check_script_command(&command, &mut query_end, position)?;
            match command {
                // Modified in Clean: global declarations go through `declare_global_symbol` (or
                // `record_global_symbol`), which refuses an ambiguous datatype symbol, and sort
                // names through `check_sort_is_not_a_datatype`.
                Token::ReservedWord(Reserved::DeclareFun) => {
                    let (name, sort) = self.parse_declare_fun()?;
                    self.declare_global_symbol(name.clone(), sort.clone(), false)?;
                    self.prelude().function_declarations.push((name, sort));
                }
                Token::ReservedWord(Reserved::DeclareConst) => {
                    let name = self.expect_symbol()?;
                    let sort = self.parse_sort()?;
                    self.expect_token(Token::CloseParen)?;
                    self.declare_global_symbol(name.clone(), sort.clone(), false)?;
                    self.prelude().function_declarations.push((name, sort));
                }
                Token::ReservedWord(Reserved::DeclareSort) => {
                    let (name, arity) = self.parse_declare_sort()?;
                    // Modified in Clean: see `check_sort_is_not_a_datatype` and
                    // `check_sort_name_is_free`.
                    self.check_sort_is_not_a_datatype(&name)?;
                    self.check_sort_name_is_free(&name)?;

                    self.prelude().sort_declarations.push((name.clone(), arity));

                    // User declared sorts are represented with the `Atom` sort kind, and an
                    // argument which is a string terminal representing the sort name.
                    self.state.sort_declarations.insert(name, arity);
                }
                Token::ReservedWord(Reserved::DeclareDatatype) => self.parse_declare_datatype()?,
                Token::ReservedWord(Reserved::DeclareDatatypes) => {
                    self.parse_declare_datatypes()?;
                }
                Token::ReservedWord(Reserved::DefineFun) => {
                    let (name, func_def) = self.parse_define_fun()?;

                    if self.config.apply_function_defs {
                        // Modified in Clean: see `record_function_def`.
                        self.record_function_def(&name, &func_def)?;
                        self.state.function_defs.insert(name, func_def);
                    } else {
                        // If `self.apply_function_defs` is false, we instead add the function name
                        // to the symbol table, and add a new premise that defines the function
                        let lambda_term = if func_def.params.is_empty() {
                            func_def.body
                        } else {
                            self.pool.add(Term::Binder(
                                Binder::Lambda,
                                BindingList(func_def.params),
                                func_def.body,
                            ))
                        };
                        let sort = self.pool.sort(&lambda_term);
                        // Modified in Clean: see `declare_global_symbol`.
                        self.declare_global_symbol(name.clone(), sort.clone(), false)?;
                        let var_term = self.pool.add((name, sort).into());
                        let assertion_term = self
                            .pool
                            .add(Term::Op(Operator::Equals, vec![var_term, lambda_term]));
                        self.premises().insert(assertion_term);
                    }
                }
                // Modified in Clean: `check_script_command` refuses both commands in the problem
                // (fix 39), so these upstream arms are not reached.
                Token::ReservedWord(Reserved::DefineFunRec) => self.parse_define_fun_rec(false)?,
                Token::ReservedWord(Reserved::DefineFunsRec) => self.parse_define_fun_rec(true)?,
                Token::ReservedWord(Reserved::DefineSort) => {
                    let (name, def) = self.parse_define_sort()?;
                    // Modified in Clean: see `check_sort_is_not_a_datatype` and
                    // `check_sort_name_is_free`.
                    self.check_sort_is_not_a_datatype(&name)?;
                    self.check_sort_name_is_free(&name)?;
                    self.state.sort_defs.insert(name, def);
                }
                // Modified in Clean: an assertion or assumption must be a formula (fix 38);
                // upstream took `(assert 5)` as a premise.
                Token::ReservedWord(Reserved::Assert) => {
                    let term = self.parse_term_expecting_sort(&Sort::Bool)?;
                    self.expect_token(Token::CloseParen)?;
                    self.premises().insert(term);
                }
                Token::ReservedWord(Reserved::CheckSatAssuming) => {
                    self.expect_token(Token::OpenParen)?;
                    let terms =
                        self.parse_sequence(|p| p.parse_term_expecting_sort(&Sort::Bool), true)?;
                    self.expect_token(Token::CloseParen)?;
                    self.premises().extend(terms);
                }
                Token::ReservedWord(Reserved::SetLogic) => {
                    let logic = self.expect_symbol()?;
                    self.expect_token(Token::CloseParen)?;
                    self.prelude().logic = Some(logic.clone());

                    // When the problem's logic contains real numbers but not integers, integer
                    // literals should be parsed as reals. For instance, `1` should be interpreted
                    // as `1.0`. We must be careful to avoid false positives with non-standard
                    // logics like "HORN".
                    self.is_real_only_logic =
                        (logic.contains("LRA") || logic.contains("NRA") || logic.contains("RDL"))
                            && !logic.contains('I');
                }
                _ => {
                    // If the command is not one of the commands we care about, we just ignore it.
                    // We do that by reading tokens until the command parenthesis is closed
                    self.ignore_until_close_parens()?;
                }
            }
        }
        Ok(self.problem.take().unwrap())
    }

    /// Parses a proof in the Alethe format. All function, constant and sort declarations needed
    /// should already be in the parser state. Note that the `premises` field in the proof will not
    /// be set.
    pub fn parse_proof(&mut self) -> CarcaraResult<Proof> {
        // To avoid stack overflows in proofs with many nested subproofs, we parse the subproofs
        // iteratively, instead of recursively. Therefore, we need to manually keep a stack.
        //
        // Each frame of the stack stores the subproof that is being constructed, the id of the
        // step that will end it, and a bool representing whether a `step` has been issued yet.
        // The first frame of the stack represents the root proof, so every
        // field except for the subproof commands is irrelevant.
        let mut stack: Vec<(Subproof, String, bool)> =
            vec![(Subproof::default(), String::new(), false)];

        let mut next_subproof_context_id = 0;

        let mut constant_definitions = Vec::new();

        // Some proofs may include an extra set of surrounding parentheses around the whole proof
        let mut has_extra_surrounding_parens = false;
        let mut read_first_token = false;

        // Some solvers print the satisfiability result (unsat) together with the proof. To save the
        // user from having to remove this, we consume this first "unsat" token if it exists
        if self.current_token == Token::Symbol("unsat".into()) {
            self.next_token()?;
        }

        while self.current_token != Token::Eof && self.current_token != Token::CloseParen {
            self.expect_token(Token::OpenParen)?;

            if !read_first_token && self.current_token == Token::OpenParen
                || self.current_token == Token::CloseParen
            {
                has_extra_surrounding_parens = true;
                read_first_token = true;
                continue;
            }
            read_first_token = true;

            let (token, position) = self.next_token()?;

            let (id, command) = match token {
                Token::ReservedWord(Reserved::Assume) => {
                    let (id, term) = self.parse_assume_command()?;

                    // Check whether the assume appears after a step.
                    if stack.last().unwrap().2 {
                        // It is permissible but weird if it happens at the top level.
                        if stack.len() == 1 {
                            log::warn!("`assume` command '{}' appears after `step` commands", &id);
                        }
                        // It is disallowed within subproofs.
                        else {
                            return Err(Error::Parser(
                                ParserError::AssumeAfterStepInSubproof(id),
                                position,
                            ));
                        }
                    }

                    (id.clone(), ProofCommand::Assume { id, term })
                }
                Token::ReservedWord(Reserved::Step) => {
                    stack.last_mut().unwrap().2 = true;
                    let step = self.parse_step_command()?;
                    (step.id.clone(), ProofCommand::Step(step))
                }
                Token::ReservedWord(Reserved::DefineFun) => {
                    let (name, func_def) = self.parse_define_fun()?;
                    // Modified in Clean: see `record_function_def`.
                    self.record_function_def(&name, &func_def)?;
                    if func_def.params.is_empty() {
                        constant_definitions.push((name.clone(), func_def.body.clone()));
                    }
                    self.state.function_defs.insert(name, func_def);
                    continue;
                }
                Token::ReservedWord(Reserved::Anchor) => {
                    let (end_step_id, args) = self.parse_anchor_command()?;

                    // When we encounter an `anchor` command, we push a new scope into the step ids
                    // symbol table, a fresh commands vector into the commands stack for the
                    // subproof to fill, and the `anchor` data (end step and arguments) into their
                    // respective stacks. All of this will be popped off at the end of the subproof.
                    // We don't need to push a new scope into the symbol table because
                    // `Parser::parse_anchor_command` already does that for us
                    self.state.step_ids.push_scope();
                    let subproof = Subproof {
                        commands: Vec::new(),
                        args,
                        context_id: next_subproof_context_id,
                    };
                    stack.push((subproof, end_step_id, false));
                    next_subproof_context_id += 1;
                    continue;
                }
                _ => {
                    return Err(Error::Parser(ParserError::UnexpectedToken(token), position));
                }
            };
            let id = HashCache::new(id);
            if self.state.step_ids.get(&id).is_some() {
                return Err(Error::Parser(
                    ParserError::RepeatedStepId(id.unwrap()),
                    position,
                ));
            }

            let (top_subproof, top_end_step, _) = stack.last_mut().unwrap();
            top_subproof.commands.push(command);
            if top_end_step == id.as_ref() {
                // If this is the last step in a subproof, we need to pop all the subproof data off
                // of the stacks and build the subproof command with it
                self.state.symbol_table.pop_scope();
                self.state.step_ids.pop_scope();
                let (subproof, _, _) = stack.pop().unwrap();

                // The subproof must contain at least two commands: the end step and the previous
                // command it implicitly references
                if subproof.commands.len() < 2 {
                    return Err(Error::Parser(
                        ParserError::EmptySubproof(id.unwrap()),
                        position,
                    ));
                }

                // We also need to make sure that the last command is in fact a `step`
                if !subproof.commands.last().unwrap().is_step() {
                    return Err(Error::Parser(
                        ParserError::LastSubproofStepIsNotStep(id.unwrap()),
                        position,
                    ));
                }

                let (outer, _, _) = stack.last_mut().unwrap();
                outer.commands.push(ProofCommand::Subproof(subproof));
            }
            let index = stack.last().unwrap().0.commands.len() - 1;
            self.state.step_ids.insert(id, index);
        }

        if has_extra_surrounding_parens {
            self.expect_token(Token::CloseParen)?;
        }
        self.expect_token(Token::Eof)?;

        let commands = match stack.len() {
            0 => unreachable!(),
            1 => stack.pop().unwrap().0.commands,

            // If there is more than one layer in the stack, we are inside a subproof that should be
            // closed before the outer proof is finished
            _ => {
                return Err(Error::Parser(
                    ParserError::UnclosedSubproof(stack.pop().unwrap().1),
                    self.current_position,
                ))
            }
        };
        Ok(Proof { constant_definitions, commands })
    }

    /// Parses an `assume` proof command. This method assumes that the `(` and `assume` tokens were
    /// already consumed.
    fn parse_assume_command(&mut self) -> CarcaraResult<(String, Rc<Term>)> {
        let id = self.expect_symbol()?;
        let term = self.parse_term_expecting_sort(&Sort::Bool)?;
        self.ignore_remaining_attributes()?;
        self.expect_token(Token::CloseParen)?;
        Ok((id, term))
    }

    /// Parses a `step` proof command. This method assumes that the `(` and `step` tokens were
    /// already consumed.
    fn parse_step_command(&mut self) -> CarcaraResult<ProofStep> {
        let id = self.expect_symbol()?;
        let clause = self.parse_clause()?;
        self.expect_token(Token::Keyword("rule".into()))?;
        let rule = match self.next_token()? {
            (Token::Symbol(s), _) => s,
            (Token::ReservedWord(r), _) => format!("{}", r),
            (other, pos) => {
                return Err(Error::Parser(ParserError::UnexpectedToken(other), pos));
            }
        };

        let premises = if self.current_token == Token::Keyword("premises".into()) {
            self.next_token()?;
            self.expect_token(Token::OpenParen)?;
            self.parse_sequence(Self::parse_step_premise, true)?
        } else {
            Vec::new()
        };

        let args = if self.current_token == Token::Keyword("args".into()) {
            self.next_token()?;
            self.expect_token(Token::OpenParen)?;

            // If the rule is `hole` and `--parse-hole-args` is not enabled, we want to allow any
            // invalid arguments, so we read the rest of the `:args` attribute without trying to
            // parse anything
            if rule == "hole" && !self.config.parse_hole_args {
                self.ignore_until_close_parens()?;
                Vec::new()
            } else {
                self.parse_sequence(Self::parse_term, true)?
            }
        } else {
            Vec::new()
        };

        // For some rules (notably the `subproof` rule), there is also a `:discharge` attribute that
        // takes a series of command ids, in addition to the regular premises
        let discharge = if self.current_token == Token::Keyword("discharge".into()) {
            self.next_token()?;
            self.expect_token(Token::OpenParen)?;
            self.parse_sequence(|p| p.parse_discharge_premise(&id), true)?
        } else {
            Vec::new()
        };

        self.ignore_remaining_attributes()?;
        self.expect_token(Token::CloseParen)?;

        Ok(ProofStep {
            id,
            clause,
            rule,
            premises,
            args,
            discharge,
        })
    }

    /// Parses a premise for a `step` command. This already converts it into the depth and command
    /// index used to reference commands in the AST.
    fn parse_step_premise(&mut self) -> CarcaraResult<(usize, usize)> {
        let position = self.current_position;
        let id = HashCache::new(self.expect_symbol()?);
        self.state
            .step_ids
            .get_with_depth(&id)
            .map(|(d, &i)| (d, i))
            .ok_or_else(|| Error::Parser(ParserError::UndefinedStepId(id.unwrap()), position))
    }

    /// Parses an argument for the `:discharge` attribute.
    ///
    /// Due to a bug in veriT, commands local to the current subproof are passed by their "relative"
    /// id. That is, the command `t5.t4.h2` is passed as simply `h2`. This behavior is not present
    /// in other SMT solvers, like cvc5. To work around that, this function tries to find the
    /// command considering both possibilities.
    fn parse_discharge_premise(&mut self, root_id: &str) -> CarcaraResult<(usize, usize)> {
        let position = self.current_position;
        let id = self.expect_symbol()?;
        let absolute_id = format!("{}.{}", root_id, &id);
        let id = HashCache::new(id);
        let absolute_id = HashCache::new(absolute_id);
        self.state
            .step_ids
            .get_with_depth(&absolute_id)
            .or_else(|| self.state.step_ids.get_with_depth(&id))
            .map(|(d, &i)| (d, i))
            .ok_or_else(|| Error::Parser(ParserError::UndefinedStepId(id.unwrap()), position))
    }

    /// Parses an `anchor` proof command. This method assumes that the `(` and `anchor` tokens were
    /// already consumed.
    ///
    /// In order to parse the subproof arguments, this method pushes a new scope into the symbol
    /// table which must be removed after parsing the subproof.
    fn parse_anchor_command(&mut self) -> CarcaraResult<(String, Vec<AnchorArg>)> {
        self.expect_token(Token::Keyword("step".into()))?;
        let end_step_id = self.expect_symbol()?;

        // We have to push a new scope into the symbol table in order to parse the subproof
        // arguments
        self.state.symbol_table.push_scope();

        let args = if self.current_token == Token::Keyword("args".into()) {
            self.next_token()?;
            self.expect_token(Token::OpenParen)?;
            self.parse_sequence(Parser::parse_anchor_argument, true)?
        } else {
            Vec::new()
        };
        self.ignore_remaining_attributes()?;
        self.expect_token(Token::CloseParen)?;
        Ok((end_step_id, args))
    }

    /// Parses an argument for an `anchor` proof command. This can be either a variable binding of
    /// the form `(<symbol> <sort>)` or an assignment, of the form `(:= (<symbol> <sort>) <term>)`.
    fn parse_anchor_argument(&mut self) -> CarcaraResult<AnchorArg> {
        self.expect_token(Token::OpenParen)?;
        Ok(if self.current_token == Token::Keyword("=".into()) {
            self.next_token()?;

            // To make Carcara more robust to recent changes in the Alethe format, we support
            // parsing the two versions of assign-style anchor arguments:
            // - the old version, without the sort hint: `(:= <symbol> <term>)`
            // - and the new version, with the sort hint: `(:= (<symbol> <sort>) <term>)`
            // However, if "strict" parsing is enabled, we only allow the new version
            let (var, value, sort) =
                if !self.config.strict && matches!(self.current_token, Token::Symbol(_)) {
                    let var = self.expect_symbol()?;
                    let value = self.parse_term()?;
                    let sort = self.pool.sort(&value);
                    (var, value, sort)
                } else {
                    let (var, sort) = self.parse_sorted_var()?;
                    let value = self.parse_term_expecting_sort(&sort)?;
                    (var, value, sort)
                };
            self.declare_symbol(var.clone(), sort.clone());
            self.expect_token(Token::CloseParen)?;
            AnchorArg::Assign((var, sort), value)
        } else {
            let symbol = self.expect_symbol()?;
            let sort = self.parse_sort()?;
            self.declare_symbol(symbol.clone(), sort.clone());
            self.expect_token(Token::CloseParen)?;
            AnchorArg::Variable((symbol, sort))
        })
    }

    /// Parses a `declare-fun` proof command. Returns the function name and its sort. This method
    /// assumes that the `(` and `declare-fun` tokens were already consumed.
    fn parse_declare_fun(&mut self) -> CarcaraResult<(String, Rc<Sort>)> {
        let name = self.expect_symbol()?;
        let sort = {
            self.expect_token(Token::OpenParen)?;
            let mut sorts = self.parse_sequence(Parser::parse_sort, false)?;
            sorts.push(self.parse_sort()?);
            if sorts.len() == 1 {
                sorts.into_iter().next().unwrap()
            } else {
                self.pool.add_sort(Sort::Function(sorts))
            }
        };
        self.expect_token(Token::CloseParen)?;
        Ok((name, sort))
    }

    /// Parses a declare-sort proof command. Returns the sort name and its arity. This method
    /// assumes that the `(` and `declare-sort` tokens were already consumed.
    fn parse_declare_sort(&mut self) -> CarcaraResult<(String, usize)> {
        let name = self.expect_symbol()?;
        let arity_pos = self.current_position;
        let arity = self.expect_numeral()?;
        self.expect_token(Token::CloseParen)?;
        let arity = arity.to_usize().ok_or(Error::Parser(
            ParserError::InvalidSortArity(arity),
            arity_pos,
        ))?;
        Ok((name, arity))
    }

    /// Parses a function declaration, of the form `(<symbol> (<sorted var>*) <sort>)`. If the
    /// parameter `consume_parens` is `false`, the opening and closing parentheses are not consumed
    fn parse_function_dec(
        &mut self,
        consume_parens: bool,
    ) -> CarcaraResult<(String, Vec<SortedVar>, Rc<Sort>)> {
        if consume_parens {
            self.expect_token(Token::OpenParen)?;
        }
        let name = self.expect_symbol()?;
        self.expect_token(Token::OpenParen)?;
        let params = self.parse_sequence(Self::parse_sorted_var, false)?;
        let return_sort = self.parse_sort()?;
        if consume_parens {
            self.expect_token(Token::CloseParen)?;
        }
        Ok((name, params, return_sort))
    }

    /// Parses a `define-fun` proof command. Returns the function name and its definition. This
    /// method assumes that the `(` and `define-fun` tokens were already consumed.
    fn parse_define_fun(&mut self) -> CarcaraResult<(String, FunctionDef)> {
        let (name, params, return_sort) = self.parse_function_dec(false)?;

        // In order to correctly parse the function body, we push a new scope to the symbol table
        // and add the functions arguments to it.
        self.state.symbol_table.push_scope();
        // Modified in Clean: the parameter scope, for hygienic macro expansion in the body (see
        // `DefineFunScope`). A `define-fun` cannot occur inside another one.
        let depth = self.state.symbol_table.height() - 1;
        let enclosing = self.state.define_fun_scope.replace(DefineFunScope {
            depth,
            placeholders: IndexMap::new(),
        });
        for (var, sort) in &params {
            self.declare_symbol(var.clone(), sort.clone());
        }
        let body = self.parse_term_expecting_sort(&return_sort);
        let scope = std::mem::replace(&mut self.state.define_fun_scope, enclosing);
        let body = body?;
        self.state.symbol_table.pop_scope();
        let (params, body) = match scope {
            Some(scope) => self.close_define_fun(scope, params, body),
            None => (params, body),
        };

        self.expect_token(Token::CloseParen)?;

        Ok((name, FunctionDef { params, body }))
    }

    /// Adds the premise corresponding to a `define-fun-rec` function definition.
    fn add_define_fun_rec_premise(&mut self, name: String, params: Vec<SortedVar>, body: Rc<Term>) {
        let application = {
            let cached = HashCache::new(name);
            let func_sort = self.state.symbol_table.get(&cached).unwrap();
            let name = cached.unwrap();
            let func_term = self.pool.add((name, func_sort.clone()).into());
            if params.is_empty() {
                func_term
            } else {
                let args = params
                    .iter()
                    .map(|var| self.pool.add(var.clone().into()))
                    .collect();
                self.pool.add(Term::App(func_term, args))
            }
        };
        let equality_term = build_term!(self.pool, (= {application} {body}));
        let premise = if params.is_empty() {
            equality_term
        } else {
            let bindings = BindingList(params);
            self.pool
                .add(Term::Binder(Binder::Forall, bindings, equality_term))
        };
        self.premises().insert(premise);
    }

    /// Parses a `define-fun-rec`/`define-funs-rec` command. Inserts the function names into the
    /// symbol table, and adds the appropriate premises. This method assumes the `(` and
    /// `define-fun-rec`/`define-funs-rec` tokens were already consumed.
    fn parse_define_fun_rec(&mut self, is_multiple: bool) -> CarcaraResult<()> {
        let declarations = if is_multiple {
            self.expect_token(Token::OpenParen)?;
            self.parse_sequence(|p| p.parse_function_dec(true), true)?
        } else {
            vec![self.parse_function_dec(false)?]
        };

        for (name, params, return_sort) in &declarations {
            let sort = if params.is_empty() {
                return_sort.clone()
            } else {
                let mut param_sorts: Vec<_> = params.iter().map(|(_, sort)| sort.clone()).collect();
                param_sorts.push(return_sort.clone());
                self.pool.add_sort(Sort::Function(param_sorts))
            };
            // Modified in Clean: see `declare_global_symbol`.
            self.declare_global_symbol(name.clone(), sort, false)?;
        }

        if is_multiple {
            self.expect_token(Token::OpenParen)?;
        }
        for (name, params, return_sort) in declarations {
            self.state.symbol_table.push_scope();
            for (var, sort) in &params {
                self.declare_symbol(var.clone(), sort.clone());
            }
            let body = self.parse_term_expecting_sort(&return_sort)?;
            self.state.symbol_table.pop_scope();

            self.add_define_fun_rec_premise(name, params, body);
        }
        if is_multiple {
            self.expect_token(Token::CloseParen)?;
        }
        self.expect_token(Token::CloseParen)?;

        Ok(())
    }

    /// Parses a `define-sort` proof command. Returns the sort name and its definition. This method
    /// assumes that the `(` and `define-sort` tokens were already consumed.
    fn parse_define_sort(&mut self) -> CarcaraResult<(String, SortDef)> {
        let name = self.expect_symbol()?;
        self.expect_token(Token::OpenParen)?;
        let params = self.parse_sequence(Self::expect_symbol, false)?;

        // In order to correctly parse the sort definition, we push a new scope to the symbol table
        // and add the sort parameters to it.
        self.state.symbol_table.push_scope();
        for s in &params {
            let sort = self.pool.add_sort(Sort::Type);
            self.declare_symbol(s.clone(), sort);
        }
        let body = self.parse_sort()?;
        self.state.symbol_table.pop_scope();

        self.expect_token(Token::CloseParen)?;

        Ok((name, SortDef { params, body }))
    }

    /// Parses a clause of the form `(cl <term>*)`.
    fn parse_clause(&mut self) -> CarcaraResult<Vec<Rc<Term>>> {
        self.expect_token(Token::OpenParen)?;
        self.expect_token(Token::ReservedWord(Reserved::Cl))?;
        self.parse_sequence(|p| p.parse_term_expecting_sort(&Sort::Bool), false)
    }

    /// Parses a sorted variable of the form `(<symbol> <sort>)`.
    fn parse_sorted_var(&mut self) -> CarcaraResult<SortedVar> {
        self.expect_token(Token::OpenParen)?;
        let symbol = self.expect_symbol()?;
        let sort = self.parse_sort()?;
        self.expect_token(Token::CloseParen)?;
        Ok((symbol, sort))
    }

    /// Parses a term.
    ///
    /// Modified in Clean: a term more than `MAX_TERM_DEPTH` deep is refused.
    pub fn parse_term(&mut self) -> CarcaraResult<Rc<Term>> {
        let position = self.current_position;
        let outer = self.lambda_term_depth == 0;
        if outer {
            let expected = self.lambda_expected.take();
            self.lambda_array_positions.clear();
            if self.config.array_lambda_dialect == ArrayLambdaDialect::TypedArrayContexts {
                let frame = array_lambda::TermFrame::enter(self, false)?;
                let planned = array_lambda::plan(&mut *frame.parser, expected);
                drop(frame);
                self.lambda_array_positions = planned?;
            }
        }
        let frame = array_lambda::TermFrame::enter(self, outer)?;
        let parsed = frame.parser.parse_term_here();
        drop(frame);
        let term = parsed?;
        self.check_term_depth(&term)
            .map_err(|err| Error::Parser(err, position))?;
        Ok(term)
    }

    /// Added in Clean: refuses `term` if it is more than `MAX_TERM_DEPTH` deep, and records its
    /// depth and that of each subterm it had not seen.
    fn check_term_depth(&mut self, term: &Rc<Term>) -> Result<(), ParserError> {
        record_depth(
            &mut self.state.term_depths,
            term,
            |term, visit| match term {
                Term::Const(_) | Term::Var(..) => {}
                Term::App(func, args) => {
                    visit(func);
                    args.iter().for_each(visit);
                }
                Term::Op(_, args) | Term::AsOp(_, _, args) => args.iter().for_each(visit),
                Term::Binder(_, _, body) => visit(body),
                Term::Let(bindings, body) => {
                    bindings.iter().for_each(|(_, value)| visit(value));
                    visit(body);
                }
                Term::Match(scrutinee, cases) => {
                    visit(scrutinee);
                    cases.iter().for_each(|case| visit(&case.body));
                }
                Term::ParamOp { op_args, args, .. } => op_args.iter().chain(args).for_each(visit),
            },
        )
    }

    /// Added in Clean: refuses `sort` if it is more than `MAX_TERM_DEPTH` deep, as
    /// `check_term_depth` does for a term.
    fn check_sort_depth(&mut self, sort: &Rc<Sort>) -> Result<(), ParserError> {
        record_depth(
            &mut self.state.sort_depths,
            sort,
            |sort, visit| match sort {
                Sort::Function(sorts) | Sort::Tuple(sorts) => sorts.iter().for_each(visit),
                Sort::Atom(_, args) => args.iter().for_each(visit),
                Sort::Datatype { args, .. } => args.iter().for_each(visit),
                Sort::Array(x, y) => {
                    visit(x);
                    visit(y);
                }
                Sort::Par(_, sort) | Sort::Set(sort) => visit(sort),
                Sort::Var(_)
                | Sort::Bool
                | Sort::Int
                | Sort::Real
                | Sort::String
                | Sort::RegLan
                | Sort::BitVec(_)
                | Sort::ParamBitVec
                | Sort::Type => {}
            },
        )
    }

    /// Added in Clean: runs `parse` one level of nesting deeper, or refuses past
    /// `MAX_WRITTEN_NESTING`.
    fn nested<T>(&mut self, parse: impl FnOnce(&mut Self) -> CarcaraResult<T>) -> CarcaraResult<T> {
        if self.state.nesting >= MAX_WRITTEN_NESTING {
            let err = ParserError::WrittenTooDeep(MAX_WRITTEN_NESTING);
            return Err(Error::Parser(err, self.current_position));
        }
        self.state.nesting += 1;
        let result = parse(self);
        self.state.nesting -= 1;
        result
    }

    fn parse_term_here(&mut self) -> CarcaraResult<Rc<Term>> {
        let (token, position) = self.next_token()?;
        // Modified in Clean: a number is refused where SMT-LIB reads a symbol in scope (fix 40).
        if matches!(token, Token::Numeral(_) | Token::Decimal(_)) {
            self.check_number_is_not_a_bound_symbol(position)?;
        }
        let term = match (token, position) {
            (Token::Bitvector(value, width), _) => Term::new_bv(value, width),
            (Token::Numeral(n), _) if self.interpret_ints_as_reals() => Term::new_real(n),
            (Token::Numeral(n), _) => Term::new_int(n),
            (Token::Decimal(r), _) => Term::new_real(r),
            (Token::String(s), _) => Term::new_string(s),
            (Token::Symbol(s), pos) => {
                // Check to see if there is a nullary function defined with this name
                // Modified in Clean: unless a local binding shadows it, and expanded hygienically
                // (see `is_macro_use` and `expand_macro`).
                return if self.is_macro_use(&s) {
                    self.expand_macro(&s, Vec::new(), pos)
                } else if self.local_binding_depth(&s).is_some() {
                    // Modified in Clean: a local binding shadows a built-in operator of the same
                    // name. Upstream read `re.all` in `(let ((re.all re.none)) (str.in_re s
                    // re.all))` as the built-in (see third-party/carcara/DOWNSTREAM.md, fix 38).
                    self.make_var(s).map_err(|err| Error::Parser(err, pos))
                } else if let Ok(op) = Operator::from_str(&s) {
                    let args = Vec::new();

                    self.make_op(op, args)
                        .map_err(|err| Error::Parser(err, pos))
                } else {
                    self.make_var(s).map_err(|err| Error::Parser(err, pos))
                };
            }
            (Token::OpenParen, _) => return self.parse_application(),
            (other, pos) => {
                return Err(Error::Parser(ParserError::UnexpectedToken(other), pos));
            }
        };
        Ok(self.pool.add(term))
    }

    /// Parses a term and checks that its sort matches the expected sort. If not, returns an error.
    fn parse_term_expecting_sort(&mut self, expected_sort: &Sort) -> CarcaraResult<Rc<Term>> {
        let pos = self.current_position;
        if self.lambda_term_depth == 0 {
            self.lambda_expected = Some(self.pool.add_sort(expected_sort.clone()));
        }
        let term = self.parse_term()?;
        self.check_sort_eq(expected_sort, &self.pool.sort(&term))
            .map_err(|e| Error::Parser(e.into(), pos))?;
        Ok(term)
    }

    /// Parses a binder term. This method assumes that the `(` and binder tokens were
    /// already consumed.
    fn parse_binder(&mut self, binder: Binder) -> CarcaraResult<Rc<Term>> {
        self.expect_token(Token::OpenParen)?;
        self.state.symbol_table.push_scope();
        let bindings = if binder == Binder::Choice {
            let (var, sort) = self.parse_sorted_var()?;
            self.declare_symbol(var.clone(), sort.clone());
            self.expect_token(Token::CloseParen)?;
            BindingList(vec![(var, sort)])
        } else {
            BindingList(self.parse_sequence(
                |p| {
                    let (var, sort) = p.parse_sorted_var()?;
                    p.declare_symbol(var.clone(), sort.clone());
                    Ok((var, sort))
                },
                true,
            )?)
        };
        let term = match binder {
            Binder::Lambda | Binder::ArrayLambda => self.parse_term()?,
            _ => self.parse_term_expecting_sort(&Sort::Bool)?,
        };
        self.state.symbol_table.pop_scope();
        self.expect_token(Token::CloseParen)?;
        if binder == Binder::ArrayLambda && bindings.len() != 1 {
            return Err(Error::Parser(
                ParserError::InvalidArrayLambda,
                self.current_position,
            ));
        }
        Ok(self.pool.add(Term::Binder(binder, bindings, term)))
    }

    /// Parses a `let` term. This method assumes that the `(` and `let` tokens were already
    /// consumed.
    fn parse_let_term(&mut self) -> CarcaraResult<Rc<Term>> {
        self.expect_token(Token::OpenParen)?;

        // Since the let binding semantics is *simultaneous*, we first parse all bindings, and only
        // then add them to the symbol table.
        let bindings = self.parse_sequence(
            |p| {
                p.expect_token(Token::OpenParen)?;
                let name = p.expect_symbol()?;
                let value = p.parse_term()?;
                p.expect_token(Token::CloseParen)?;
                Ok((name, value))
            },
            true,
        )?;

        self.state.symbol_table.push_scope();
        for (name, value) in &bindings {
            let sort = self.pool.sort(value);
            self.declare_symbol(name.clone(), sort);
        }

        let inner = self.parse_term()?;
        self.expect_token(Token::CloseParen)?;

        self.state.symbol_table.pop_scope();

        if self.config.expand_lets {
            let substitution = bindings
                .into_iter()
                .map(|(name, value)| {
                    let var = Term::new_var(name, self.pool.sort(&value));
                    (self.pool.add(var), value)
                })
                .collect();

            let result = Substitution::new(self.pool, substitution)
                .unwrap()
                .apply(self.pool, &inner);

            Ok(result)
        } else {
            Ok(self.pool.add(Term::Let(BindingList(bindings), inner)))
        }
    }

    /// Parses an annotated term, of the form `(! <term> <attribute>+)`. This method assumes that
    /// the `(` and `!` tokens were already consumed.
    ///
    /// The two supported attributes are `:named` and `:pattern`, though the latter is ignored. If
    /// any other attribute is present, an error will be returned.
    fn parse_annotated_term(&mut self) -> CarcaraResult<Rc<Term>> {
        let inner = self.parse_term()?;
        self.parse_sequence(
            |p| {
                let attribute = p.expect_keyword()?;
                match attribute.as_str() {
                    "named" => {
                        // If the term has a `:named` attribute, we introduce a new nullary function
                        // definition that maps the name to the term
                        let name = p.expect_symbol()?;
                        // Modified in Clean: see `check_named_term_is_closed` and
                        // `resolve_placeholders`.
                        p.check_named_term_is_closed(&name, &inner)?;
                        let func_def = FunctionDef {
                            params: Vec::new(),
                            body: p.resolve_placeholders(&inner),
                        };
                        // Modified in Clean: see `record_function_def`.
                        p.record_function_def(&name, &func_def)?;
                        p.state.function_defs.insert(name, func_def);
                        Ok(())
                    }

                    // We allow unknown attributes, and just ignore them
                    _ => match p.current_token {
                        // If the argument is a list, we consume it until the `)` token
                        Token::OpenParen => {
                            p.next_token()?;
                            p.ignore_until_close_parens()
                        }

                        // If the attribute has no argument, we don't do anything
                        Token::Keyword(_) | Token::CloseParen | Token::Eof => Ok(()),

                        // If the argument is a single token, we consume it
                        _ => {
                            p.next_token()?;
                            Ok(())
                        }
                    },
                }
            },
            true,
        )?;
        Ok(inner)
    }

    fn parse_indexed_operator(&mut self) -> CarcaraResult<(ParamOperator, Vec<Rc<Term>>)> {
        let op_symbol = self.expect_symbol()?;

        if let Some(value) = op_symbol.strip_prefix("bv") {
            // Modified in Clean: `(_ bv 4)` or `(_ bvx 4)` is a parse error, not a panic (see
            // third-party/carcara/DOWNSTREAM.md, "Malformed steps are refused, not a panic").
            let Ok(parsed_value) = value.parse::<Integer>() else {
                return Err(Error::Parser(
                    ParserError::InvalidIndexedOp(op_symbol),
                    self.current_position,
                ));
            };
            let args = self.parse_sequence(Self::parse_term, true)?;
            let mut constant_args = Vec::new();
            for arg in args {
                if let Some(i) = arg.as_signed_integer() {
                    constant_args.push(self.pool.add(Term::Const(Constant::Integer(i))));
                } else {
                    return Err(Error::Parser(
                        ParserError::ExpectedIntegerConstant(arg.clone()),
                        self.current_position,
                    ));
                }
            }
            constant_args.insert(
                0,
                self.pool.add(Term::Const(Constant::Integer(parsed_value))),
            );
            return Ok((ParamOperator::BvConst, constant_args));
        }
        let op = ParamOperator::from_str(op_symbol.as_str()).map_err(|_| {
            Error::Parser(
                ParserError::InvalidIndexedOp(op_symbol),
                self.current_position,
            )
        })?;
        if op == ParamOperator::Tester {
            let cons = self.parse_term()?;
            self.expect_token(Token::CloseParen)?;
            let args = vec![cons.clone()];
            return Ok((op, args));
        }
        let args = self.parse_sequence(Self::parse_term, true)?;
        let mut constant_args = Vec::new();
        for arg in args {
            if let Some(i) = arg.as_signed_integer() {
                constant_args.push(self.pool.add(Term::Const(Constant::Integer(i))));
            } else {
                return Err(Error::Parser(
                    ParserError::ExpectedIntegerConstant(arg.clone()),
                    self.current_position,
                ));
            }
        }
        Ok((op, constant_args))
    }

    /// Constructs, check operation arguments and sort checks an indexed operation term.
    fn make_indexed_op(
        &mut self,
        op: ParamOperator,
        op_args: Vec<Rc<Term>>,
        args: Vec<Rc<Term>>,
    ) -> Result<Rc<Term>, ParserError> {
        let sorts: Vec<_> = args.iter().map(|t| self.pool.sort(t)).collect();
        let op_sorts: Vec<_> = op_args.iter().map(|t| self.pool.sort(t)).collect();
        match &op {
            ParamOperator::BvConst => {
                assert_num_args(&op_args, 2)?;
                assert_num_args(&args, 0)?;
                // Modified in Clean: check the value and the width before reading them. A width
                // that is negative or does not fit a `usize` was unwrapped and panicked (see
                // third-party/carcara/DOWNSTREAM.md, "Malformed steps are refused, not a panic").
                assert_indexed_op_args_value(&[op_args[0].clone()], 0..)?;
                assert_indexed_op_args_value(&[op_args[1].clone()], 1..)?;
                let (Some(value), Some(width)) = (
                    op_args[0].as_integer(),
                    op_args[1].as_integer().as_ref().and_then(Integer::to_usize),
                ) else {
                    return Err(ParserError::ExpectedIntegerConstant(op_args[1].clone()));
                };
                // Modified in Clean: `(_ bv<n> <w>)` denotes `n mod 2^w` (SMT-LIB, FixedSizeBitVectors).
                // Keeping `n` as written made `(_ bv5 2)` a distinct term from `#b01`, which it
                // denotes (see third-party/carcara/DOWNSTREAM.md).
                //
                // `n` is non-negative (checked above), so `n mod 2^w` is `n` itself unless `n` has
                // more than `w` significant bits. Only then is it truncated, and then `w` is below
                // `n`'s bit count, a `u32`, so the cast is exact. Casting `w` unconditionally
                // (`keep_bits(width as u32)`) reduced modulo `2^(w mod 2^32)` for `w >= 2^32`,
                // making `(_ bv5 4294967298)` the term `(_ bv1 4294967298)` (fix 35).
                let value = if value.significant_bits() as usize > width {
                    value.keep_bits(width as u32)
                } else {
                    value
                };
                return Ok(self.pool.add(Term::Const(Constant::BitVec(value, width))));
            }
            ParamOperator::BvExtract => {
                /*
                ((_ extract i j) (_ BitVec m) (_ BitVec n))

                where
                - i, j, m, n are numerals
                - m > i ≥ j ≥ 0,
                - n = i - j + 1
                 */
                assert_num_args(&op_args, 2)?;
                assert_num_args(&args, 1)?;
                if !sorts[0].is_bitvec() {
                    return Err(ParserError::ExpectedBvSort(sorts[0].clone()));
                }

                for s in &op_sorts {
                    self.check_sort_eq(&Sort::Int, s)?;
                }

                assert_indexed_op_args_value(&op_args, 0..)?;
                let i = op_args[0].as_integer().as_ref().and_then(Integer::to_usize);
                let j = op_args[1].as_integer().as_ref().and_then(Integer::to_usize);

                // j >= 0 is ensured by the parser. We need to ensure that m > i && i >= j, if they
                // are all statically known
                if let (Some(i), Some(j), Sort::BitVec(m)) = (i, j, sorts[0].as_ref()) {
                    if !(*m > i && i >= j) {
                        return Err(ParserError::InvalidExtractArgs(i, j, *m));
                    }
                }
                // Modified in Clean: `compute_sort` computes the width `i - j + 1` unchecked, so
                // `i >= j` and a width that fits are required also when `m` is not known (a
                // `ParamBitVec` operand); see third-party/carcara/DOWNSTREAM.md, "Also hardened".
                if let (Some(i), Some(j)) = (i, j) {
                    if i < j || (i - j).checked_add(1).is_none() {
                        return Err(ParserError::BitVecWidthOverflow("extract".into()));
                    }
                }
            }
            ParamOperator::IntToBv => {
                assert_num_args(&op_args, 1)?;
                assert_num_args(&args, 1)?;
                self.check_sort_eq(&Sort::Int, &op_sorts[0])?;
                self.check_sort_eq(&Sort::Int, &sorts[0])?;
            }
            ParamOperator::BvBitOf
            | ParamOperator::BvIntOf
            | ParamOperator::ZeroExtend
            | ParamOperator::SignExtend
            | ParamOperator::RotateLeft
            | ParamOperator::RotateRight
            | ParamOperator::Repeat => {
                assert_num_args(&op_args, 1)?;
                assert_num_args(&args, 1)?;
                self.check_sort_eq(&Sort::Int, &op_sorts[0])?;
                if !sorts[0].is_bitvec() {
                    return Err(ParserError::ExpectedBvSort(sorts[0].clone()));
                }
                assert_indexed_op_args_value(&op_args, 0..)?;
                // Modified in Clean: the extensions add `k` to the operand's width and `repeat`
                // multiplies it by `k`, unchecked in `compute_sort`; a result that does not fit
                // `usize` is refused here (third-party/carcara/DOWNSTREAM.md, "Also hardened").
                let k = op_args[0].as_integer().as_ref().and_then(Integer::to_usize);
                if let (Some(k), Sort::BitVec(w)) = (k, sorts[0].as_ref()) {
                    let result = match op {
                        ParamOperator::ZeroExtend | ParamOperator::SignExtend => w.checked_add(k),
                        ParamOperator::Repeat => w.checked_mul(k),
                        _ => Some(*w),
                    };
                    if result.is_none() {
                        return Err(ParserError::BitVecWidthOverflow(op.to_string()));
                    }
                    // Modified in Clean: `((_ repeat 0) x)` would be a 0-bit term, which SMT-LIB
                    // does not have and whose bits the bit-blasting rules index (see
                    // third-party/carcara/DOWNSTREAM.md, "Malformed steps are refused, not a
                    // panic").
                    if result == Some(0) {
                        return Err(ParserError::WrongValueOfArgs(
                            (1..).into(),
                            Integer::from(k),
                        ));
                    }
                }
            }
            ParamOperator::RePower => {
                assert_num_args(&op_args, 1)?;
                assert_num_args(&args, 1)?;
                self.check_sort_eq(&Sort::Int, &op_sorts[0])?;
                self.check_sort_eq(&Sort::RegLan, &sorts[0])?;
                assert_indexed_op_args_value(&op_args, 0..)?;
            }
            ParamOperator::ReLoop => {
                assert_num_args(&op_args, 2)?;
                assert_num_args(&args, 1)?;
                for s in &op_sorts {
                    self.check_sort_eq(&Sort::Int, s)?;
                }
                self.check_sort_eq(&Sort::RegLan, &sorts[0])?;
                assert_indexed_op_args_value(&op_args, 0..)?;
            }
            // Modified in Clean: `(_ is C)` must name a constructor `C` of its single argument's
            // datatype, and `C` must be that global constructor, not a local binding of its name.
            // Upstream accepted any term as `C` and any arguments (a `TODO`). Substitution and
            // free variables do not look inside an indexed operator's arguments, so a
            // `define-fun` parameter or binder variable there was never substituted or seen (see
            // third-party/carcara/DOWNSTREAM.md, "Also hardened").
            ParamOperator::Tester => {
                assert_num_args(&op_args, 1)?;
                assert_num_args(&args, 1)?;
                let constructor = match op_args[0].as_ref() {
                    Term::Var(name, _) if self.local_binding_depth(name).is_none() => name.clone(),
                    Term::Var(name, _) => return Err(ParserError::InvalidTester(name.clone())),
                    _ => return Err(ParserError::InvalidTester("<term>".to_owned())),
                };
                let Sort::Datatype { name, .. } = sorts[0].as_ref() else {
                    return Err(ParserError::ExpectedDatatypeSort(sorts[0].clone()));
                };
                if !self
                    .pool
                    .get_datatype(name)
                    .constructors
                    .contains_key(&constructor)
                {
                    return Err(ParserError::InvalidTester(constructor));
                }
            }
            ParamOperator::TupleSelect => {
                assert_num_args(&op_args, 1)?;
                assert_num_args(&args, 1)?;
                if op_args[0]
                    .as_integer()
                    .as_ref()
                    .and_then(Integer::to_usize)
                    .is_none()
                {
                    return Err(ParserError::ExpectedIntegerConstant(op_args[0].clone()));
                }
                let Sort::Tuple(elems) = sorts[0].as_ref() else {
                    return Err(ParserError::ExpectedTupleSort(sorts[0].clone()));
                };
                assert_indexed_op_args_value(&op_args, ..elems.len())?;
            }
        }
        // Modified in Clean: Clean's Alethe dialect reads `zero_extend` as its SMT-LIB definition
        // (third-party/carcara/DOWNSTREAM.md § Dialect).
        if self.config.expand_zero_extend && op == ParamOperator::ZeroExtend {
            return self.zero_extend_definition(&op_args, args);
        }
        Ok(self.pool.add(Term::ParamOp { op, op_args, args }))
    }

    /// Modified in Clean: `((_ zero_extend k) t)` as its definition, `t` for `k = 0` and
    /// otherwise `(concat Z t)` built by `make_op`, with `Z` the all-zero constant of width `k`
    /// (third-party/carcara/DOWNSTREAM.md § Dialect). The caller has checked the arity, the
    /// operand's sort and the index.
    fn zero_extend_definition(
        &mut self,
        op_args: &[Rc<Term>],
        mut args: Vec<Rc<Term>>,
    ) -> Result<Rc<Term>, ParserError> {
        let k = op_args[0]
            .as_integer()
            .as_ref()
            .and_then(Integer::to_usize)
            .ok_or_else(|| ParserError::ExpectedIntegerConstant(op_args[0].clone()))?;
        let operand = args.remove(0);
        if k == 0 {
            return Ok(operand);
        }
        let zero = self
            .pool
            .add(Term::Const(Constant::BitVec(Integer::new(), k)));
        self.make_op(Operator::BvConcat, vec![zero, operand])
    }

    /// Constructs and sort checks a qualified operation term
    fn make_qualified_op(
        &mut self,
        op: QualifiedOperator,
        sort: Rc<Sort>,
        args: Vec<Rc<Term>>,
    ) -> Result<Rc<Term>, ParserError> {
        let sorts: Vec<_> = args.iter().map(|t| self.pool.sort(t)).collect();
        match op {
            QualifiedOperator::Const => {
                assert_num_args(&args, 1)?;
                self.check_array_sort(None, Some(&sorts[0]), &sort)?;
            }
            QualifiedOperator::SetEmpty | QualifiedOperator::SetUniverse => {
                assert_num_args(&args, 0)?;
                check_set_sort(&sort)?;
            }
        }
        Ok(self.pool.add(Term::AsOp(op, sort, args)))
    }

    /// Parses any term that starts with `(`, that is, any term that is not a constant or a
    /// variable. This method assumes that the `(` token was already consumed.
    // Modified in Clean: every term written inside another is read through here, so this is where
    // the parser's nesting is counted (see `MAX_WRITTEN_NESTING`).
    fn parse_application(&mut self) -> CarcaraResult<Rc<Term>> {
        self.nested(Self::parse_application_here)
    }

    fn parse_application_here(&mut self) -> CarcaraResult<Rc<Term>> {
        let head_pos = self.current_position;
        match &self.current_token {
            &Token::ReservedWord(reserved) => {
                self.next_token()?;
                match reserved {
                    Reserved::Underscore => {
                        let (op, op_args) = self.parse_indexed_operator()?;
                        self.make_indexed_op(op, op_args, Vec::new())
                            .map_err(|err| Error::Parser(err, head_pos))
                    }
                    Reserved::As => {
                        let op_symbol = self.expect_symbol()?;
                        // Modified in Clean: unless a local binding shadows the operator (fix 38).
                        let qualified = QualifiedOperator::from_str(op_symbol.as_str())
                            .ok()
                            .filter(|_| self.local_binding_depth(&op_symbol).is_none());
                        if let Some(op) = qualified {
                            let sort = self.parse_sort()?;
                            self.expect_token(Token::CloseParen)?;
                            self.make_qualified_op(op, sort, Vec::new())
                                .map_err(|err| Error::Parser(err, head_pos))
                        } else {
                            let var = self
                                .make_var(op_symbol.clone())
                                .map_err(|err| Error::Parser(err, self.current_position))?;
                            let var_sort = self.pool.sort(&var);
                            if let Sort::Par(_, par_sort) = var_sort.as_ref() {
                                let sort = self.parse_sort()?;
                                self.expect_token(Token::CloseParen)?;
                                // Modified in Clean: `(as f S)` denotes `f` instantiated at `S`,
                                // so `S` must be an instance of `f`'s `par` sort. Upstream built
                                // `f` at any `S` ("TODO test unification"): with `L` declaring a
                                // `par` constructor `snd` after `P` declared a selector `snd`,
                                // `(as snd (-> P Int))` was the very `Term::Var` of `P`'s
                                // selector, and `dt_project` read it as one. The parser's
                                // datatype guard lets same-named symbols of different arities
                                // coexist, so this is what keeps their readings apart. See
                                // third-party/carcara/DOWNSTREAM.md, C2.
                                let mut map = IndexMap::new();
                                if !par_sort.match_with(&sort, &mut map) {
                                    return Err(Error::Parser(
                                        ParserError::NotAnInstanceOfParSort(
                                            op_symbol,
                                            sort,
                                            var_sort.clone(),
                                        ),
                                        self.current_position,
                                    ));
                                }
                                Ok(self.pool.add(Term::new_var(op_symbol, sort)))
                            } else {
                                Err(Error::Parser(
                                    ParserError::InvalidQualifiedOp(op_symbol),
                                    self.current_position,
                                ))
                            }
                        }
                    }
                    Reserved::Match => self.parse_match(),
                    Reserved::Exists => self.parse_binder(Binder::Exists),
                    Reserved::Forall => self.parse_binder(Binder::Forall),
                    Reserved::Choice => self.parse_binder(Binder::Choice),
                    Reserved::Lambda => {
                        let binder = if self.lambda_array_positions.contains(&head_pos) {
                            Binder::ArrayLambda
                        } else {
                            Binder::Lambda
                        };
                        self.parse_binder(binder)
                    }
                    Reserved::Bang => self.parse_annotated_term(),
                    Reserved::Let => self.parse_let_term(),
                    Reserved::Cl => {
                        let args = self.parse_sequence(Self::parse_term, false)?;
                        self.make_op(Operator::Cl, args)
                            .map_err(|err| Error::Parser(err, head_pos))
                    }
                    _ => Err(Error::Parser(
                        ParserError::UnexpectedToken(Token::ReservedWord(reserved)),
                        head_pos,
                    )),
                }
            }
            // Here, I would like to use an `if let` guard, like:
            //
            //     Token::Symbol(s) if let Ok(operator) = Operator::from_str(s) => { ... }
            //
            // However, `if let` guards are still nightly only. For more info, see:
            // https://github.com/rust-lang/rust/issues/51114
            // Modified in Clean: unless a local binding shadows the operator (see
            // `parse_term`, fix 38); the application is then read by the last arm.
            Token::Symbol(s)
                if Operator::from_str(s).is_ok() && self.local_binding_depth(s).is_none() =>
            {
                let operator = Operator::from_str(s).unwrap();
                self.next_token()?;
                let args = self.parse_sequence(Self::parse_term, true)?;
                self.make_op(operator, args)
                    .map_err(|err| Error::Parser(err, head_pos))
            }
            Token::Symbol(s)
                if s == "bv2nat"
                    && self.config.allow_legacy_bv2nat
                    && self.state.function_defs.get(s).is_none()
                    && self
                        .state
                        .symbol_table
                        .get(&HashCache::new(s.clone()))
                        .is_none() =>
            {
                self.next_token()?;
                let args = self.parse_sequence(Self::parse_term, true)?;
                self.make_op(Operator::UBvToInt, args)
                    .map_err(|err| Error::Parser(err, head_pos))
            }
            // Modified in Clean: unless a local binding shadows the operator (fix 38).
            Token::Symbol(s)
                if ParamOperator::from_str(s).is_ok()
                    && self.config.allow_higher_order_indexed_ops
                    && self.local_binding_depth(s).is_none() =>
            {
                let op = ParamOperator::from_str(s).unwrap();
                self.next_token()?;
                let mut op_args = self.parse_sequence(Self::parse_term, true)?;
                let args = op_args.split_off(op.num_op_args());
                self.make_indexed_op(op, op_args, args)
                    .map_err(|err| Error::Parser(err, head_pos))
            }
            // Modified in Clean: unless a local binding shadows `eo` (fix 38).
            Token::Symbol(s) if s == "eo" && self.local_binding_depth(s).is_none() => {
                // "Let" constructions unfold
                self.expect_token(Token::Symbol("eo".to_owned()))?;
                self.expect_keyword()?;
                self.expect_token(Token::Keyword("define".to_owned()))?;
                self.expect_token(Token::OpenParen)?;
                let args = self.parse_sequence(
                    |parser| {
                        parser.expect_token(Token::OpenParen)?;
                        let let_arg = parser.expect_symbol()?;
                        let body = parser.parse_term()?;
                        parser.expect_token(Token::CloseParen)?;
                        Ok((let_arg, body))
                    },
                    true,
                )?;

                self.state.symbol_table.push_scope();
                for (name, value) in &args {
                    let sort = self.pool.sort(value);
                    self.declare_symbol(name.clone(), sort);
                }

                let inner = self.parse_term()?;
                self.expect_token(Token::CloseParen)?;

                self.state.symbol_table.pop_scope();
                let substitution = args
                    .into_iter()
                    .map(|(name, value)| {
                        let var = Term::new_var(name, self.pool.sort(&value));
                        (self.pool.add(var), value)
                    })
                    .collect();

                let result = Substitution::new(self.pool, substitution)
                    .unwrap()
                    .apply(self.pool, &inner);

                Ok(result)
            }
            // Modified in Clean: unless a local binding shadows it, and expanded hygienically (see
            // `is_macro_use` and `expand_macro`).
            Token::Symbol(s) if self.is_macro_use(s) => {
                let head_pos = self.current_position;
                let func_name = self.expect_symbol()?;
                let args = self.parse_sequence(Self::parse_term, true)?;
                self.expand_macro(&func_name, args, head_pos)
            }
            Token::OpenParen => {
                self.next_token()?;
                match self.current_token {
                    Token::ReservedWord(Reserved::Underscore) => {
                        self.next_token()?;
                        let (op, op_args) = self.parse_indexed_operator()?;
                        let args = self.parse_sequence(Self::parse_term, true)?;
                        self.make_indexed_op(op, op_args, args)
                            .map_err(|err| Error::Parser(err, head_pos))
                    }
                    Token::ReservedWord(Reserved::As) => {
                        self.next_token()?;
                        let op_symbol = self.expect_symbol()?;
                        // Modified in Clean: unless a local binding shadows the operator (fix 38).
                        let qualified = QualifiedOperator::from_str(op_symbol.as_str())
                            .ok()
                            .filter(|_| self.local_binding_depth(&op_symbol).is_none());
                        if let Some(op) = qualified {
                            let sort = self.parse_sort()?;
                            self.expect_token(Token::CloseParen)?;
                            let args = self.parse_sequence(Self::parse_term, true)?;
                            self.make_qualified_op(op, sort, args)
                                .map_err(|err| Error::Parser(err, head_pos))
                        } else {
                            let var = self
                                .make_var(op_symbol.clone())
                                .map_err(|err| Error::Parser(err, self.current_position))?;
                            let var_sort = self.pool.sort(&var);
                            if let Sort::Par(_, f_sort) = var_sort.as_ref() {
                                if let Sort::Function(sorts) = f_sort.as_ref() {
                                    let sort = self.parse_sort()?;
                                    self.expect_token(Token::CloseParen)?;
                                    // unify return sort with as_sort
                                    let ret_sort = sorts.last().unwrap();
                                    let mut map = IndexMap::<_, _>::new();
                                    if !ret_sort.match_with(&sort, &mut map) {
                                        return Err(Error::Parser(
                                            ParserError::IncompatibleSorts(
                                                ret_sort.clone(),
                                                sort.clone(),
                                            ),
                                            self.current_position,
                                        ));
                                    }
                                    // if types are unifiable, create variable with sort after applying the substitution
                                    let result =
                                        SortSubstitution::new(map).apply(self.pool, &var_sort);
                                    let func = self.pool.add(Term::new_var(op_symbol, result));
                                    // now apply it to args
                                    let args = self.parse_sequence(Self::parse_term, true)?;
                                    return self
                                        .make_app(func, args)
                                        .map_err(|err| Error::Parser(err, head_pos));
                                }
                            }
                            Err(Error::Parser(
                                ParserError::InvalidQualifiedOp(op_symbol),
                                self.current_position,
                            ))
                        }
                    }
                    _ => {
                        let func = self.parse_application()?;
                        let args = self.parse_sequence(Self::parse_term, true)?;
                        self.make_app(func, args)
                            .map_err(|err| Error::Parser(err, head_pos))
                    }
                }
            }
            _ => {
                let func = self.parse_term()?;
                let args = self.parse_sequence(Self::parse_term, true)?;
                self.make_app(func, args)
                    .map_err(|err| Error::Parser(err, head_pos))
            }
        }
    }

    fn make_sort(&mut self, name: String, args: Vec<Rc<Sort>>) -> Result<Rc<Sort>, ParserError> {
        // Modified in Clean: a local sort parameter shadows a built-in sort of the same name, and
        // takes no arguments (see `is_local_sort_parameter`, fix 38). Upstream matched the
        // built-in names first, so `val` in `(par (Bool) ((mk (val Bool))))` returned `Bool` at
        // every instance, and dropped the arguments of a parameter applied to some.
        if self.is_local_sort_parameter(&name) {
            assert_num_args(&args, 0)?;
            return Ok(self.pool.add_sort(Sort::Var(name)));
        }
        let sort = match name.as_str() {
            "->" => Sort::Function(args),
            "Bool" | "Int" | "Real" | "String" | "RegLan" | "Type" if !args.is_empty() => {
                return Err(ParserError::WrongNumberOfArgs(0.into(), args.len()))
            }
            "Bool" => Sort::Bool,
            "Int" => Sort::Int,
            "Real" => Sort::Real,
            "String" => Sort::String,
            "RegLan" => Sort::RegLan,
            "Type" => Sort::Type,
            "Array" => match args.as_slice() {
                [x, y] => Sort::Array(x.clone(), y.clone()),
                _ => return Err(ParserError::WrongNumberOfArgs(2.into(), args.len())),
            },
            "rare-list" | "RareList" => match args.as_slice() {
                [] => Sort::Var("?".to_owned()),
                [s] => return Ok(s.clone()),
                _ => return Err(ParserError::WrongNumberOfArgs(1.into(), args.len())),
            },

            // From sets and relations extension
            "Set" => {
                assert_num_args(&args, 1)?;
                Sort::Set(args[0].clone())
            }
            "Tuple" => {
                assert_num_args(&args, 1..)?;
                Sort::Tuple(args)
            }
            "UnitTuple" => {
                assert_num_args(&args, 0)?;
                Sort::Tuple(Vec::new())
            }
            "Relation" => {
                assert_num_args(&args, 1..)?;
                Sort::Set(self.pool.add_sort(Sort::Tuple(args)))
            }

            // Local sort parameter
            other if self.has_sort_symbol(other) => Sort::Var(other.to_owned()),

            // Local sort parameter, but with leading `@` implicitly removed
            other
                if self.config.implicit_at_sort_alias
                    && self.has_sort_symbol(&format!("@{}", other)) =>
            {
                Sort::Var(other.to_owned())
            }

            // Sort definition, from `define-sort`
            other if self.state.sort_defs.get(other).is_some() => {
                let def = self.state.sort_defs.get(other).unwrap();
                return if def.params.len() != args.len() {
                    Err(ParserError::WrongNumberOfArgs(
                        def.params.len().into(),
                        args.len(),
                    ))
                } else if def.params.is_empty() {
                    Ok(def.body.clone())
                } else {
                    let substitution = def.params.iter().cloned().zip(args).collect();
                    let result = SortSubstitution::new(substitution).apply(self.pool, &def.body);
                    Ok(result)
                };
            }

            // Datatype sort, from `declare-datatype(s)`
            other if self.state.datatype_declarations.get(other).is_some() => {
                let arity = self.state.datatype_declarations.get(other).unwrap();
                if *arity == args.len() {
                    Sort::Datatype { name: name.into_boxed_str(), args }
                } else {
                    return Err(ParserError::WrongNumberOfArgs((*arity).into(), args.len()));
                }
            }

            // Sort declaration, from `declare-sort`
            other if self.state.sort_declarations.get(other).is_some() => {
                let arity = self.state.sort_declarations.get(other).unwrap();
                if *arity == args.len() {
                    Sort::Atom(name.into_boxed_str(), args.into_boxed_slice())
                } else {
                    return Err(ParserError::WrongNumberOfArgs((*arity).into(), args.len()));
                }
            }

            // Unknown
            _ => return Err(ParserError::UndefinedSort(name)),
        };
        Ok(self.pool.add_sort(sort))
    }

    fn make_indexed_sort(
        &mut self,
        name: String,
        args: Vec<Rc<Term>>,
    ) -> Result<Rc<Sort>, ParserError> {
        match name.as_str() {
            "BitVec" => {
                if args.len() != 1 {
                    return Err(ParserError::WrongNumberOfArgs(1.into(), args.len()));
                }
                let sort = if let Some(width) = args[0].as_integer() {
                    // Modified in Clean: a width is a positive numeral that fits a `usize`
                    // (SMT-LIB: `(_ BitVec m)` with `m > 0`). A width of 2^64 or more was
                    // unwrapped and panicked, and width 0 made the bit-blasting rules index an
                    // empty list of bits (see third-party/carcara/DOWNSTREAM.md, "Malformed steps
                    // are refused, not a panic").
                    match width.to_usize() {
                        Some(width) if width > 0 => Sort::BitVec(width),
                        _ => return Err(ParserError::WrongValueOfArgs((1..).into(), width)),
                    }
                } else {
                    // TODO: used to be an error. maybe still should be an error outside rare files
                    Sort::ParamBitVec
                };
                Ok(self.pool.add_sort(sort))
            }
            _ => Err(ParserError::UndefinedSort(name)),
        }
    }

    /// Parses a sort.
    // Modified in Clean: a sort written inside another is counted with the terms (see
    // `MAX_WRITTEN_NESTING`), and a sort more than `MAX_TERM_DEPTH` deep is refused.
    fn parse_sort(&mut self) -> CarcaraResult<Rc<Sort>> {
        let pos = self.current_position;
        let sort = if self.current_token == Token::OpenParen {
            self.nested(Self::parse_sort_here)?
        } else {
            self.parse_sort_here()?
        };
        self.check_sort_depth(&sort)
            .map_err(|err| Error::Parser(err, pos))?;
        Ok(sort)
    }

    fn parse_sort_here(&mut self) -> CarcaraResult<Rc<Sort>> {
        let pos = self.current_position;
        let (name, args) = match self.next_token()?.0 {
            Token::Symbol(s) => (s, Vec::new()),
            Token::OpenParen if self.current_token == Token::ReservedWord(Reserved::Underscore) => {
                self.next_token()?;
                let name = self.expect_symbol()?;
                let args = self.parse_sequence(Self::parse_term, true)?;
                return self
                    .make_indexed_sort(name, args)
                    .map_err(|e| Error::Parser(e, pos));
            }
            Token::OpenParen => {
                let name = self.expect_symbol()?;

                // Currently `BitVec` is the only indexed/dependently typed sort
                if name == "BitVec" && self.config.allow_higher_order_indexed_ops {
                    let args = self.parse_sequence(Self::parse_term, true)?;
                    return self
                        .make_indexed_sort(name, args)
                        .map_err(|e| Error::Parser(e, pos));
                }
                let args = self.parse_sequence(Parser::parse_sort, true)?;
                (name, args)
            }
            other => {
                return Err(Error::Parser(ParserError::UnexpectedToken(other), pos));
            }
        };
        self.make_sort(name, args)
            .map_err(|e| Error::Parser(e, pos))
    }
}
