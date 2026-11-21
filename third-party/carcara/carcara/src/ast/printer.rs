// Modified in Clean: typed array-lambda dialect and explicit lambda export refusal.
//! A pretty printer for Alethe proofs.

use crate::{
    ast::{
        pool::{PrimitivePool, TermPool},
        AnchorArg, Binder, BindingList, Constant, MatchCase, MatchPattern, Operator, ParamOperator,
        ProblemPrelude, Proof, ProofCommand, ProofIter, ProofStep, Rc, Sort, SortedVar, Term,
    },
    parser::Token,
    utils::{is_symbol_character, DedupIterator},
};
use indexmap::IndexMap;
use std::{
    borrow::Cow,
    collections::{HashMap, HashSet},
    fmt, io,
    sync::atomic::{AtomicBool, Ordering},
};

/// A global variable that controls whether the default implementation of [`fmt::Display`] should
/// make use of term sharing or not.
pub static USE_SHARING_IN_TERM_DISPLAY: AtomicBool = AtomicBool::new(false);

// Added in Clean: `Display` (and so `Debug`, and every error message) writes a term or a sort
// abridged. A term is a DAG, and its text is the unshared tree: a definition chain
// `d_i = (and d_(i-1) d_(i-1))` 40 deep is 40 terms, and its text 2^40 copies of `d_0`. Upstream
// rendered that text whole into a buffer first, so a rule that only *formatted* an error about
// such a term (`bitvector_size` on a `bitblast_equal` step over a Boolean) ran out of memory. Each
// `Display` now writes at most `MAX_DISPLAYED_BYTES`, streamed, and stops writing there, ending
// the text with `...`; past `MAX_DISPLAYED_DEPTH` nested terms or sorts it writes `...` for the
// subterm. Output that must be exact (a proof printed by `AlethePrinter`, a term or prelude sent to
// an external tool, a translation) is written by `AlethePrinter` or through `unabridged()`, whose
// size is that of the unshared tree (see third-party/carcara/DOWNSTREAM.md, "Diagnostics write a
// term abridged").

/// Added in Clean: the most bytes `Display` writes for one term or sort, before its closing
/// `...`.
pub const MAX_DISPLAYED_BYTES: usize = 4096;

/// Added in Clean: the most terms and sorts `Display` writes nested inside each other; a subterm
/// deeper than this is written as `...`. It bounds the printer's recursion, and so its stack, well
/// below what `MAX_DISPLAYED_BYTES` alone would allow: writing a term 64 deep takes about 60 KiB of
/// stack in a release build (280 KiB unoptimized), where 4,096 levels would take 4 MiB (18 MiB).
pub const MAX_DISPLAYED_DEPTH: usize = 64;

/// Prints a proof to the standard output.
///
/// If `use_sharing` is `true`, terms that are used multiple times will make use of sharing. The
/// first time a novel term appears, it receives a unique name using the `:named` attribute. After
/// that, any occurrence of that term will simply use this name, instead of printing the whole term.
pub fn print_proof(
    pool: &mut PrimitivePool,
    prelude: &ProblemPrelude,
    proof: &Proof,
    use_sharing: bool,
) -> io::Result<()> {
    let mut stdout = io::stdout();
    AlethePrinter::new(pool, prelude, use_sharing, &mut stdout).write_proof(proof)
}

/// Writes a proof to the provided destination.
///
/// If `use_sharing` is `true`, terms that are used multiple times will make use of sharing. The
/// first time a novel term appears, it receives a unique name using the `:named` attribute. After
/// that, any occurrence of that term will simply use this name, instead of printing the whole term.
pub fn write_proof_to_dest(
    pool: &mut PrimitivePool,
    prelude: &ProblemPrelude,
    proof: &Proof,
    dest: &mut dyn io::Write,
    use_sharing: bool,
) -> io::Result<()> {
    AlethePrinter::new(pool, prelude, use_sharing, dest).write_proof(proof)
}

/// Given the conclusion clause of a step, writes to `dest` an SMT-LIB problem that corresponds to
// the negation of that clause.
pub(crate) fn write_clause_smt_problem(
    pool: &mut PrimitivePool,
    prelude: &ProblemPrelude,
    dest: &mut dyn io::Write,
    clause: &[Rc<Term>],
    use_sharing: bool,
) -> io::Result<()> {
    let mut printer = AlethePrinter::new(pool, prelude, use_sharing, dest);
    // We have to override the default prefix "@p_" because symbols starting with "@" are reserved
    // in SMT-LIB.
    printer.term_sharing_variable_prefix = "p_".to_owned();
    // Since we are printing an SMT-LIB problem, we have to be compliant. For Carcara, this means
    // that arithmetic constants cannot use the GMP notation
    printer.smt_lib_strict = true;
    printer.write_clause_smt_problem(clause)
}

/// Writes the assertions of an SMT-LIB problem to the provided destination.
pub fn write_asserts<'a, I: IntoIterator<Item = &'a Rc<Term>>>(
    pool: &mut PrimitivePool,
    prelude: &ProblemPrelude,
    dest: &mut dyn io::Write,
    assertions: I,
    use_sharing: bool,
) -> io::Result<()> {
    let mut printer = AlethePrinter::new(pool, prelude, use_sharing, dest);
    // We have to override the default prefix "@p_" because symbols starting with "@" are reserved
    // in SMT-LIB.
    printer.term_sharing_variable_prefix = "p_".to_owned();
    // Since we are printing an SMT-LIB problem, we have to be
    // compliant. For Carcara, this means that arithmetic constants
    // cannot use the GMP notation
    printer.smt_lib_strict = true;

    for assertion in assertions {
        write!(printer.inner, "(assert ")?;
        assertion.print_with_sharing(&mut printer)?;
        writeln!(printer.inner, ")")?;
    }
    Ok(())
}

/// Writes a term to the provided destination.
pub(crate) fn write_term(
    pool: &mut PrimitivePool,
    prelude: &ProblemPrelude,
    dest: &mut dyn io::Write,
    term: &Rc<Term>,
    use_sharing: bool,
    prefix: String,
) -> io::Result<()> {
    let mut printer = AlethePrinter::new(pool, prelude, use_sharing, dest);
    printer.term_sharing_variable_prefix = prefix;
    // Since we are printing an SMT-LIB problem, we have to be
    // compliant. For Carcara, this means that arithmetic constants
    // cannot use the GMP notation
    printer.smt_lib_strict = true;
    term.print_with_sharing(&mut printer)?;
    Ok(())
}

trait PrintProof {
    fn write_proof(&mut self, proof: &Proof) -> io::Result<()>;
}

trait PrintWithSharing {
    fn print_with_sharing(&self, p: &mut AlethePrinter) -> io::Result<()>;
}

impl<T: PrintWithSharing> PrintWithSharing for &T {
    fn print_with_sharing(&self, p: &mut AlethePrinter) -> io::Result<()> {
        PrintWithSharing::print_with_sharing(*self, p)
    }
}

impl PrintWithSharing for Rc<Term> {
    fn print_with_sharing(&self, p: &mut AlethePrinter) -> io::Result<()> {
        if let Some(name) = p.defined_constants.get(self) {
            return write!(p.inner, "{}", quote_symbol(name));
        }
        if let Some(indices) = &mut p.term_indices {
            // There are a few cases where we don't use sharing when printing a term:
            let cannot_use_sharing =
                // - Terminal terms (i.e., constants or variables) could in theory be shared,
                // but, since they are very small, it's not worth it to give them a name.
                self.is_const() || self.is_var()
                // - If a term is only used once in the proof, there is no reason to give it a
                // name. We detect this case by checking if the number of references to it's `Rc` is
                // no more than 3: one in the pool storage, one in the pool sorts cache, and one in
                // the proof itself.
                // TODO: this is a terrible way of checking if it is only used once in the proof,
                // as it depends on internal implementation details of the term pool.
                || Rc::strong_count(self) <= 3
                // - Terms which are not closed, that is, terms which have free variables besides
                // the global variables, cannot be shared
                || !self.is_closed(p.pool, &p.global_variables);

            if !cannot_use_sharing {
                return if let Some(i) = indices.get(self) {
                    write!(p.inner, "{}{}", p.term_sharing_variable_prefix, i)
                } else if p.use_sharing {
                    let i = indices.len();
                    indices.insert(self.clone(), i);
                    write!(p.inner, "(! ")?;
                    p.write_raw_term(self)?;
                    write!(p.inner, " :named {}{})", p.term_sharing_variable_prefix, i)
                } else {
                    p.write_raw_term(self)
                };
            }
        }
        p.write_raw_term(self)
    }
}

impl PrintWithSharing for Rc<Sort> {
    fn print_with_sharing(&self, p: &mut AlethePrinter) -> io::Result<()> {
        p.write_sort(self)
    }
}

impl PrintWithSharing for SortedVar {
    fn print_with_sharing(&self, p: &mut AlethePrinter) -> io::Result<()> {
        let (name, sort) = self;
        write!(p.inner, "({} ", quote_symbol(name))?;
        sort.print_with_sharing(p)?;
        write!(p.inner, ")")
    }
}

impl<T> PrintWithSharing for BindingList<T>
where
    (String, T): PrintWithSharing,
{
    fn print_with_sharing(&self, p: &mut AlethePrinter) -> io::Result<()> {
        match self.as_slice() {
            [] => write!(p.inner, "()"),
            [head, tail @ ..] => p.write_s_expr(head, tail),
        }
    }
}

impl PrintWithSharing for (String, Rc<Term>) {
    fn print_with_sharing(&self, p: &mut AlethePrinter) -> io::Result<()> {
        let (name, value) = self;
        write!(p.inner, "({} ", quote_symbol(name))?;
        value.print_with_sharing(p)?;
        write!(p.inner, ")")
    }
}

impl PrintWithSharing for Constant {
    fn print_with_sharing(&self, p: &mut AlethePrinter) -> io::Result<()> {
        write!(p.inner, "{}", self)
    }
}

impl PrintWithSharing for Operator {
    fn print_with_sharing(&self, p: &mut AlethePrinter) -> io::Result<()> {
        write!(p.inner, "{}", self)
    }
}

impl PrintWithSharing for ParamOperator {
    fn print_with_sharing(&self, p: &mut AlethePrinter) -> io::Result<()> {
        write!(p.inner, "{}", self)
    }
}

impl PrintWithSharing for MatchCase {
    fn print_with_sharing(&self, p: &mut AlethePrinter) -> io::Result<()> {
        write!(p.inner, "({} ", self.pattern)?;
        self.body.print_with_sharing(p)?;
        write!(p.inner, ")")
    }
}

/// A pretty printer for Alethe proofs.
pub struct AlethePrinter<'a> {
    pool: &'a mut PrimitivePool,
    inner: &'a mut dyn io::Write,
    term_indices: Option<IndexMap<Rc<Term>, usize>>,
    term_sharing_variable_prefix: String,
    global_variables: HashSet<Rc<Term>>,
    defined_constants: HashMap<Rc<Term>, String>,
    smt_lib_strict: bool,
    use_sharing: bool,
    // Added in Clean: how many more terms and sorts may be written nested inside each other, for a
    // printer writing a diagnostic (`Display`); `None`, for every other printer, writes them all.
    depth_left: Option<usize>,
}

impl PrintProof for AlethePrinter<'_> {
    fn write_proof(&mut self, proof: &Proof) -> io::Result<()> {
        for (name, value) in &proof.constant_definitions {
            write!(self.inner, "(define-fun {} () ", quote_symbol(name))?;
            self.pool.sort(value).print_with_sharing(self)?;
            write!(self.inner, " ")?;
            value.print_with_sharing(self)?;
            writeln!(self.inner, ")")?;
        }
        self.defined_constants = proof
            .constant_definitions
            .iter()
            .cloned()
            .map(|(name, term)| (term, name))
            .collect();
        let mut iter = proof.iter();
        while let Some(command) = iter.next() {
            match command {
                ProofCommand::Assume { id, term } => {
                    write!(self.inner, "(assume {} ", quote_symbol(id))?;
                    term.print_with_sharing(self)?;
                    write!(self.inner, ")")?;
                }
                ProofCommand::Step(s) => self.write_step(&mut iter, s)?,
                ProofCommand::Subproof(s) => {
                    write!(self.inner, "(anchor :step {}", quote_symbol(command.id()))?;

                    if !s.args.is_empty() {
                        write!(self.inner, " :args (")?;
                        let mut is_first = true;
                        for arg in &s.args {
                            if !is_first {
                                write!(self.inner, " ")?;
                            }
                            is_first = false;

                            match arg {
                                AnchorArg::Variable((name, sort)) => {
                                    write!(self.inner, "({} ", quote_symbol(name))?;
                                    sort.print_with_sharing(self)?;
                                    write!(self.inner, ")")?;
                                }
                                AnchorArg::Assign(var, value) => {
                                    write!(self.inner, "(:= ")?;
                                    var.print_with_sharing(self)?;
                                    write!(self.inner, " ")?;
                                    value.print_with_sharing(self)?;
                                    write!(self.inner, ")")?;
                                }
                            }
                        }
                        write!(self.inner, ")")?;
                    }

                    write!(self.inner, ")")?;
                }
            }
            writeln!(self.inner)?;
        }
        self.defined_constants.clear();
        Ok(())
    }
}

impl<'a> AlethePrinter<'a> {
    /// Constructs a new `AlethePrinter`.
    ///
    /// If `use_sharing` is `true`, terms that are used multiple times will make use of sharing. The
    /// problem prelude is required to know the proof's global variables, and thus know which terms
    /// are closed.
    pub fn new(
        pool: &'a mut PrimitivePool,
        prelude: &ProblemPrelude,
        use_sharing: bool,
        dest: &'a mut dyn io::Write,
    ) -> Self {
        let global_variables = if use_sharing {
            prelude
                .function_declarations
                .iter()
                .map(|var| pool.add(var.clone().into()))
                .collect()
        } else {
            HashSet::new()
        };
        Self {
            pool,
            inner: dest,
            term_indices: use_sharing.then(IndexMap::new),
            term_sharing_variable_prefix: "@p_".to_owned(),
            global_variables,
            defined_constants: HashMap::new(),
            smt_lib_strict: false,
            use_sharing,
            depth_left: None,
        }
    }

    /// Added in Clean: a printer that writes as `Display` does: a fresh pool, no defined constants,
    /// not SMT-LIB strict, sharing only if `USE_SHARING_IN_TERM_DISPLAY` asks for it, and nesting
    /// limited to `depth_left` (`None` for no limit).
    fn for_display(
        pool: &'a mut PrimitivePool,
        dest: &'a mut dyn io::Write,
        use_sharing: bool,
        depth_left: Option<usize>,
    ) -> Self {
        Self {
            pool,
            inner: dest,
            term_indices: use_sharing.then(IndexMap::new),
            term_sharing_variable_prefix: "@p_".to_owned(),
            global_variables: HashSet::new(),
            defined_constants: HashMap::new(),
            smt_lib_strict: false,
            use_sharing,
            depth_left,
        }
    }

    /// Added in Clean: runs `write` one level deeper, or writes `...` in its place past the
    /// printer's depth limit.
    fn nested(&mut self, write: impl FnOnce(&mut Self) -> io::Result<()>) -> io::Result<()> {
        let Some(depth_left) = self.depth_left else {
            return write(self);
        };
        if depth_left == 0 {
            return write!(self.inner, "...");
        }
        self.depth_left = Some(depth_left - 1);
        let result = write(self);
        self.depth_left = Some(depth_left);
        result
    }

    fn write_s_expr<H, T>(&mut self, head: &H, tail: &[T]) -> io::Result<()>
    where
        H: PrintWithSharing + ?Sized,
        T: PrintWithSharing,
    {
        write!(self.inner, "(")?;
        head.print_with_sharing(self)?;
        self.write_s_expr_tail(tail)
    }

    fn write_s_expr_tail<T: PrintWithSharing>(&mut self, tail: &[T]) -> io::Result<()> {
        for t in tail {
            write!(self.inner, " ")?;
            t.print_with_sharing(self)?;
        }
        write!(self.inner, ")")
    }

    fn write_raw_term(&mut self, term: &Term) -> io::Result<()> {
        self.nested(|p| p.write_raw_term_here(term))
    }

    fn write_raw_term_here(&mut self, term: &Term) -> io::Result<()> {
        match term {
            Term::Const(c) => {
                if self.smt_lib_strict {
                    if let Constant::Integer(i) = c {
                        if i.is_negative() {
                            write!(self.inner, "(- {})", i.clone().abs())
                        } else {
                            write!(self.inner, "{}", i)
                        }
                    } else if let Constant::Real(r) = c {
                        if r.is_negative() {
                            write!(self.inner, "(- ")?;
                        }
                        if r.is_integer() {
                            write!(self.inner, "{}.0", r.clone().abs())?;
                        } else {
                            write!(
                                self.inner,
                                "(/ {}.0 {}.0)",
                                r.numer().clone().abs(),
                                r.denom()
                            )?;
                        }
                        if r.is_negative() {
                            write!(self.inner, ")")?;
                        }
                        Ok(())
                    } else {
                        write!(self.inner, "{}", c)
                    }
                } else {
                    write!(self.inner, "{}", c)
                }
            }
            Term::Var(name, _) => write!(self.inner, "{}", quote_symbol(name)),
            Term::App(func, args) => self.write_s_expr(func, args),
            Term::Op(op, args) => {
                if args.is_empty() {
                    write!(self.inner, "{}", op)
                } else {
                    self.write_s_expr(op, args)
                }
            }
            Term::Binder(binder, bindings, term) => {
                write!(self.inner, "({} ", binder)?;
                bindings.print_with_sharing(self)?;
                write!(self.inner, " ")?;
                // TODO: should we avoid creating names within binders?
                // let place_holder = self.use_sharing;
                // self.use_sharing = false;
                term.print_with_sharing(self)?;
                // self.use_sharing = place_holder;
                write!(self.inner, ")")
            }
            Term::Let(bindings, term) => {
                write!(self.inner, "(let ")?;
                bindings.print_with_sharing(self)?;
                write!(self.inner, " ")?;
                term.print_with_sharing(self)?;
                write!(self.inner, ")")
            }
            Term::Match(term, cases) => {
                // Modified in Clean: the scrutinee is written as before, as `Display` writes a term
                // (without this printer's sharing, names or SMT-LIB strictness), but streamed into
                // this printer's destination and within its depth limit, not rendered into a
                // buffer of its own first.
                write!(self.inner, "(match ")?;
                let mut pool = PrimitivePool::new();
                let use_sharing = USE_SHARING_IN_TERM_DISPLAY.load(Ordering::Relaxed);
                let mut scrutinee =
                    AlethePrinter::for_display(&mut pool, self.inner, use_sharing, self.depth_left);
                scrutinee.write_raw_term(term)?;
                write!(self.inner, " (")?;
                for case in cases {
                    case.print_with_sharing(self)?;
                }
                write!(self.inner, ")")
            }
            Term::ParamOp { op, op_args, args } => {
                if !args.is_empty() {
                    write!(self.inner, "(")?;
                }
                write!(self.inner, "(_ {}", op)?;
                self.write_s_expr_tail(op_args)?;
                if !args.is_empty() {
                    self.write_s_expr_tail(args)?;
                }
                Ok(())
            }
            Term::AsOp(op, sort, args) => {
                if !args.is_empty() {
                    write!(self.inner, "(")?;
                }
                write!(self.inner, "(as {} ", op)?;
                self.write_sort(sort)?;
                write!(self.inner, ")")?;
                if !args.is_empty() {
                    self.write_s_expr_tail(args)?;
                }
                Ok(())
            }
        }
    }

    /// Writes a sort as upstream's `Display` for `Sort` wrote it.
    ///
    /// Added in Clean: it is the printer's, so a sort is written within the printer's limits (see
    /// `MAX_DISPLAYED_BYTES`); a sort is a DAG too (`define-sort`).
    fn write_sort(&mut self, sort: &Sort) -> io::Result<()> {
        self.nested(|p| p.write_sort_here(sort))
    }

    fn write_sort_here(&mut self, sort: &Sort) -> io::Result<()> {
        match sort {
            Sort::Function(args) => self.write_sort_s_expr("->", args),
            Sort::Atom(name, args) => match args.len() {
                0 => write!(self.inner, "{}", quote_symbol(name)),
                _ => self.write_sort_s_expr(&quote_symbol(name), args),
            },
            Sort::Bool => write!(self.inner, "Bool"),
            Sort::Int => write!(self.inner, "Int"),
            Sort::Real => write!(self.inner, "Real"),
            Sort::String => write!(self.inner, "String"),
            Sort::RegLan => write!(self.inner, "RegLan"),
            Sort::Datatype { name, args, .. } if args.is_empty() => {
                write!(self.inner, "{}", quote_symbol(name))
            }
            Sort::Datatype { name, args, .. } => self.write_sort_s_expr(&quote_symbol(name), args),
            Sort::Var(name) => write!(self.inner, "{}", name),
            Sort::Par(args, s) => {
                write!(self.inner, "(par ({}", args[0])?;
                for arg in &args[1..] {
                    write!(self.inner, " {}", arg)?;
                }
                write!(self.inner, ") ")?;
                self.write_sort(s)?;
                write!(self.inner, ")")
            }
            Sort::Array(x, y) => {
                write!(self.inner, "(Array ")?;
                self.write_sort(x)?;
                write!(self.inner, " ")?;
                self.write_sort(y)?;
                write!(self.inner, ")")
            }
            Sort::BitVec(w) => write!(self.inner, "(_ BitVec {})", w),
            Sort::ParamBitVec => write!(self.inner, "(_ BitVec ?)"),
            Sort::Type => write!(self.inner, "Type"),
            Sort::Set(s) => {
                write!(self.inner, "(Set ")?;
                self.write_sort(s)?;
                write!(self.inner, ")")
            }
            Sort::Tuple(sorts) if sorts.is_empty() => write!(self.inner, "UnitTuple"),
            Sort::Tuple(sorts) => self.write_sort_s_expr("Tuple", sorts),
        }
    }

    fn write_sort_s_expr(&mut self, head: &str, tail: &[Rc<Sort>]) -> io::Result<()> {
        write!(self.inner, "({}", head)?;
        for sort in tail {
            write!(self.inner, " ")?;
            self.write_sort(sort)?;
        }
        write!(self.inner, ")")
    }

    fn write_step(&mut self, iter: &mut ProofIter, step: &ProofStep) -> io::Result<()> {
        write!(self.inner, "(step {} (cl", quote_symbol(&step.id))?;

        for t in &step.clause {
            write!(self.inner, " ")?;
            t.print_with_sharing(self)?;
        }
        write!(self.inner, ")")?;

        write!(self.inner, " :rule {}", step.rule)?;

        if let [head, tail @ ..] = step.premises.as_slice() {
            let id = iter.get_premise(*head).id();
            write!(self.inner, " :premises ({}", quote_symbol(id))?;
            for premise in tail {
                let id = iter.get_premise(*premise).id();
                write!(self.inner, " {}", quote_symbol(id))?;
            }
            write!(self.inner, ")")?;
        }

        if let [head, tail @ ..] = step.args.as_slice() {
            write!(self.inner, " :args (")?;
            head.print_with_sharing(self)?;
            for arg in tail {
                write!(self.inner, " ")?;
                arg.print_with_sharing(self)?;
            }
            write!(self.inner, ")")?;
        }

        if let [head, tail @ ..] = step.discharge.as_slice() {
            let id = iter.get_premise(*head).id();
            write!(self.inner, " :discharge ({}", id)?;
            for discharge in tail {
                let id = iter.get_premise(*discharge).id();
                write!(self.inner, " {}", quote_symbol(id))?;
            }
            write!(self.inner, ")")?;
        }

        write!(self.inner, ")")?;
        Ok(())
    }

    fn write_clause_smt_problem(&mut self, clause: &[Rc<Term>]) -> io::Result<()> {
        for term in clause.iter().dedup() {
            write!(self.inner, "(assert (not ")?;
            term.print_with_sharing(self)?;
            writeln!(self.inner, "))")?;
        }
        Ok(())
    }
}

fn write_s_expr<H, T>(
    f: &mut fmt::Formatter,
    head: H,
    tail: impl IntoIterator<Item = T>,
) -> fmt::Result
where
    H: fmt::Display,
    T: fmt::Display,
{
    write!(f, "({}", head)?;
    for e in tail {
        write!(f, " {}", e)?;
    }
    write!(f, ")")
}

fn quote_symbol(symbol: &str) -> Cow<'_, str> {
    use crate::parser::Reserved;
    use std::str::FromStr;

    assert!(symbol.chars().all(|c| c != '|'));

    // Any symbol that:
    // - is an empty string,
    // - starts with a digit,
    // - is a reserved word, or
    // - contains non-symbol characters
    // must be quoted
    if symbol.is_empty()
        || symbol.chars().next().unwrap().is_ascii_digit()
        || Reserved::from_str(symbol).is_ok()
        || symbol.chars().any(|c| !is_symbol_character(c))
    {
        Cow::Owned(format!("|{}|", symbol))
    } else {
        Cow::Borrowed(symbol)
    }
}

fn escape_string(string: &str) -> Cow<'_, str> {
    if string.contains('"') {
        Cow::Owned(string.replace('"', "\"\""))
    } else {
        Cow::Borrowed(string)
    }
}

// Modified in Clean: `Display` writes a term abridged, streamed into the formatter, where upstream
// rendered the whole unshared tree into a buffer first (see `MAX_DISPLAYED_BYTES`).
impl fmt::Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        display(f, true, |p| p.write_raw_term(self))
    }
}

impl fmt::Debug for Term {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}

/// Added in Clean: a term or sort written in full by `Display`, as upstream's `Display` wrote it.
/// Made by [`Term::unabridged`] and [`Sort::unabridged`].
///
/// Its text is the unshared tree, exponential in the size of a shared term, so it is for output
/// that must be exact, never for a diagnostic.
pub struct Unabridged<'a, T: ?Sized>(&'a T);

impl Term {
    /// Added in Clean: this term written in full by `Display` (see [`Unabridged`]).
    pub fn unabridged(&self) -> Unabridged<'_, Term> {
        Unabridged(self)
    }
}

impl Sort {
    /// Added in Clean: this sort written in full by `Display` (see [`Unabridged`]).
    pub fn unabridged(&self) -> Unabridged<'_, Sort> {
        Unabridged(self)
    }
}

impl fmt::Display for Unabridged<'_, Term> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        display(f, false, |p| p.write_raw_term(self.0))
    }
}

impl fmt::Display for Unabridged<'_, Sort> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        display(f, false, |p| p.write_sort(self.0))
    }
}

/// Added in Clean: writes into `f` what `write` writes with a printer set up as `Display`'s, within
/// `MAX_DISPLAYED_BYTES` and `MAX_DISPLAYED_DEPTH` if `abridged`. Text cut at the byte limit ends
/// in `...`.
fn display(
    f: &mut fmt::Formatter<'_>,
    abridged: bool,
    write: impl FnOnce(&mut AlethePrinter) -> io::Result<()>,
) -> fmt::Result {
    // If the alternate flag (`#`) is passed, or the global `USE_SHARING_IN_TERM_DISPLAY` is
    // false, we disable printing with sharing
    let use_sharing = USE_SHARING_IN_TERM_DISPLAY.load(Ordering::Relaxed) && !f.alternate();
    let mut out = FormatterWriter {
        f,
        bytes_left: abridged.then_some(MAX_DISPLAYED_BYTES),
        cut: false,
    };
    // This pool is only used for the free variables cache, so it's fine to use a fresh pool
    let mut pool = PrimitivePool::new();
    let depth_left = abridged.then_some(MAX_DISPLAYED_DEPTH);
    let result = write(&mut AlethePrinter::for_display(
        &mut pool,
        &mut out,
        use_sharing,
        depth_left,
    ));
    match result {
        Ok(()) => Ok(()),
        Err(_) if out.cut => out.f.write_str("..."),
        Err(_) => Err(fmt::Error),
    }
}

/// Added in Clean: the printer's destination when it writes for `Display`: the formatter, taking at
/// most `bytes_left` bytes (all of them if `None`). A write past the limit writes what fits (whole
/// characters), sets `cut` and fails, which stops the printer.
struct FormatterWriter<'f, 'a> {
    f: &'f mut fmt::Formatter<'a>,
    bytes_left: Option<usize>,
    cut: bool,
}

impl io::Write for FormatterWriter<'_, '_> {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        // The printer writes through `write!`, which hands over whole `str`s, so this borrows.
        let text = String::from_utf8_lossy(buf);
        let fits = match self.bytes_left {
            Some(left) if text.len() > left => {
                let mut end = left;
                while !text.is_char_boundary(end) {
                    end -= 1;
                }
                self.cut = true;
                end
            }
            _ => text.len(),
        };
        if let Some(left) = &mut self.bytes_left {
            *left -= fits;
        }
        self.f
            .write_str(&text[..fits])
            .map_err(|_| io::Error::from(io::ErrorKind::Other))?;
        if self.cut {
            return Err(io::ErrorKind::WriteZero.into());
        }
        Ok(buf.len())
    }

    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

impl fmt::Display for Constant {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Constant::Integer(i) => write!(f, "{}", i),
            Constant::Real(r) => {
                // TODO: add option to control whether we use GMP notation
                if r.is_integer() && !r.is_negative() {
                    write!(f, "{}.0", r.numer())
                } else {
                    write!(f, "{}/{}", r.numer(), r.denom())
                }
            }
            Constant::String(s) => write!(f, "\"{}\"", escape_string(s)),
            Constant::RegLan(s, _) => write!(f, "(re.from_automaton \"{}\")", s),
            Constant::BitVec(val, width) => write!(f, "(_ bv{} {})", val, width), // TODO: comeback to this
        }
    }
}

impl fmt::Display for Binder {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let s = match self {
            Binder::Forall => "forall",
            Binder::Exists => "exists",
            Binder::Choice => "choice",
            Binder::Lambda | Binder::ArrayLambda => "lambda",
        };
        write!(f, "{}", s)
    }
}

impl<T: fmt::Display> fmt::Display for BindingList<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.as_slice() {
            [] => write!(f, "()"),
            [head, tail @ ..] => {
                write!(f, "(({} {})", quote_symbol(&head.0), head.1)?;
                for (var, term) in tail {
                    write!(f, " ({} {})", quote_symbol(var), term)?;
                }
                write!(f, ")")
            }
        }
    }
}

// Modified in Clean: `Display` writes a sort as `AlethePrinter` does, abridged like a term (see
// `MAX_DISPLAYED_BYTES`), and `Debug` is `Display`, as for a term; both used to write the whole
// unshared tree of a sort built by `define-sort`.
impl fmt::Display for Sort {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        display(f, true, |p| p.write_sort(self))
    }
}

impl fmt::Debug for Sort {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        fmt::Display::fmt(self, f)
    }
}

impl fmt::Display for MatchPattern {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            MatchPattern::Wildcard => write!(f, "_"),
            MatchPattern::Variable((var, _)) => write!(f, "{}", quote_symbol(var)),
            MatchPattern::Cons(cons, args) => write_s_expr(
                f,
                quote_symbol(cons),
                args.iter().map(|(var, _)| quote_symbol(var)),
            ),
        }
    }
}

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Token::OpenParen => write!(f, "("),
            Token::CloseParen => write!(f, ")"),
            Token::Symbol(s) => write!(f, "{}", quote_symbol(s)),
            Token::Keyword(k) => write!(f, ":{}", k),
            Token::Numeral(n) => write!(f, "{}", n),
            Token::Decimal(r) => write!(f, "{}", r),
            Token::Bitvector(value, width) => {
                write!(f, "#b{v:0>w$b}", v = value, w = { *width })
            }
            Token::String(s) => write!(f, "\"{}\"", escape_string(s)),
            Token::ReservedWord(r) => write!(f, "{}", r),
            Token::Eof => write!(f, "EOF"),
        }
    }
}

impl fmt::Display for ProblemPrelude {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        writeln!(f, "(set-logic {})", self.logic.as_deref().unwrap_or("ALL"))?;

        for (name, arity) in &self.sort_declarations {
            writeln!(f, "(declare-sort {} {})", quote_symbol(name), arity)?;
        }

        // Modified in Clean: the sorts are written in full (`unabridged`): this text is a problem
        // handed to an external tool.
        for (name, sort) in &self.function_declarations {
            write!(f, "(declare-fun {} ", quote_symbol(name))?;
            if let Sort::Function(sorts) = sort.as_ref() {
                write_s_expr(
                    f,
                    sorts[0].unabridged(),
                    sorts[1..sorts.len() - 1].iter().map(|s| s.unabridged()),
                )?;
                writeln!(f, " {})", sorts.last().unwrap().unabridged())?;
            } else {
                writeln!(f, "() {})", sort.unabridged())?;
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_sharing() {
        use crate::parser;

        let definitions = "
            (declare-const a Bool)
            (declare-const b Bool)
            (declare-const y Bool)
            (declare-const z Bool)
        ";
        let proof = "
            (step t1 (cl (and (= 1 2) (= 1 2))) :rule hole)
            (step t2 (cl (and (or a b) (not (or a b)))) :rule hole)
            (step t3 (cl (and (forall ((x Int)) (or (= x 2) (= 2 3))) (= 2 3))) :rule hole)
            (step t4 (cl (forall ((x Int)) (= (+ x 2) (+ x 2)))) :rule hole)
            (step t5 (cl (and (forall ((p Bool)) p) (forall ((p Bool)) p))) :rule hole)
            (anchor :step t6 :args ((x Int)))
            (step t6.t1 (cl (= (+ x 2) (+ x 2))) :rule hole)
            (step t6 (cl) :rule hole)
        ";
        let expected = "\
            (step t1 (cl (and (! (= 1 2) :named @p_0) @p_0)) :rule hole)\n\
            (step t2 (cl (and (! (or a b) :named @p_1) (not @p_1))) :rule hole)\n\
            (step t3 (cl (and (forall ((x Int)) (or (= x 2) (! (= 2 3) :named @p_2))) @p_2)) :rule hole)\n\
            (step t4 (cl (forall ((x Int)) (= (+ x 2) (+ x 2)))) :rule hole)\n\
            (step t5 (cl (and (! (forall ((p Bool)) p) :named @p_3) @p_3)) :rule hole)\n\
            (anchor :step t6 :args ((x Int)))\n\
            (step t6.t1 (cl (= (+ x 2) (+ x 2))) :rule hole)\n\
            (step t6 (cl) :rule hole)\n\
        ";
        let (problem, proof, _, mut pool) =
            parser::parse_instance(definitions, proof, None, parser::Config::new()).unwrap();

        let mut buf = Vec::new();
        AlethePrinter::new(&mut pool, &problem.prelude, true, &mut buf)
            .write_proof(&proof)
            .unwrap();

        println!("{}", std::str::from_utf8(&buf).unwrap());
        println!("{}", expected);

        assert_eq!(expected, std::str::from_utf8(&buf).unwrap());
    }

    // Added in Clean: `Display` writes a term or a sort abridged (see `MAX_DISPLAYED_BYTES`), and
    // `unabridged()` writes it in full, as `Display` did before.

    /// `d_i = (and d_(i-1) d_(i-1))`, `depth` deep over `p`: `depth + 1` terms, whose text is
    /// `2^depth` copies of `p`.
    fn doubling_chain(pool: &mut PrimitivePool, depth: usize) -> Rc<Term> {
        let bool_sort = pool.add_sort(Sort::Bool);
        let mut term = pool.add(Term::new_var("p", bool_sort));
        for _ in 0..depth {
            term = pool.add(Term::Op(Operator::And, vec![term.clone(), term]));
        }
        term
    }

    fn doubling_chain_text(depth: usize) -> String {
        match depth {
            0 => "p".to_owned(),
            _ => {
                let inner = doubling_chain_text(depth - 1);
                format!("(and {inner} {inner})")
            }
        }
    }

    /// The text `Display` writes for `doubling_chain(depth)`: the tree's first `MAX_DISPLAYED_BYTES`
    /// bytes, what lies past `MAX_DISPLAYED_DEPTH` elided.
    fn abridged_chain_text(depth: usize) -> String {
        fn write(out: &mut String, depth: usize, level: usize) {
            if out.len() > MAX_DISPLAYED_BYTES {
                return;
            }
            match (level, depth) {
                (MAX_DISPLAYED_DEPTH, _) => out.push_str("..."),
                (_, 0) => out.push('p'),
                _ => {
                    out.push_str("(and ");
                    write(out, depth - 1, level + 1);
                    out.push(' ');
                    write(out, depth - 1, level + 1);
                    out.push(')');
                }
            }
        }
        let mut out = String::new();
        write(&mut out, depth, 0);
        if out.len() > MAX_DISPLAYED_BYTES {
            out.truncate(MAX_DISPLAYED_BYTES);
            out.push_str("...");
        }
        out
    }

    #[test]
    fn display_writes_a_shared_term_abridged() {
        let mut pool = PrimitivePool::new();
        // 2^40 and 2^100 copies of `p`: upstream's `Display` grew without bound on either.
        for depth in [40, 100] {
            let term = doubling_chain(&mut pool, depth);
            let expected = abridged_chain_text(depth);
            assert_eq!(expected.len(), MAX_DISPLAYED_BYTES + 3);
            for text in [term.to_string(), format!("{term:?}"), format!("{term:#}")] {
                assert_eq!(text, expected);
            }
            // An error naming the term twice writes it abridged twice.
            let error = crate::checker::error::CheckerError::ReflexivityFailed(term.clone(), term)
                .to_string();
            assert_eq!(
                error,
                format!("reflexivity failed with terms '{expected}' and '{expected}'")
            );
        }
        assert!(abridged_chain_text(100).contains("(and ... ...)"));

        // Up to the limit, `Display` writes the whole text; past it, `unabridged()` does.
        let small = doubling_chain(&mut pool, 8);
        assert!(doubling_chain_text(8).len() <= MAX_DISPLAYED_BYTES);
        assert_eq!(small.to_string(), doubling_chain_text(8));
        let large = doubling_chain(&mut pool, 12);
        assert_eq!(large.unabridged().to_string(), doubling_chain_text(12));
        assert_eq!(large.to_string(), abridged_chain_text(12));
    }

    #[test]
    fn display_cuts_at_a_character_boundary() {
        let mut pool = PrimitivePool::new();
        let bool_sort = pool.add_sort(Sort::Bool);
        // `(and |xéé…| |xéé…| |xéé…|)`: the byte limit falls inside an `é` of the third.
        let var = pool.add(Term::new_var(format!("x{}", "é".repeat(1000)), bool_sort));
        let term = pool.add(Term::Op(Operator::And, vec![var.clone(), var.clone(), var]));
        let text = term.to_string();
        let cut = text.strip_suffix("...").unwrap();
        assert_eq!(cut.len(), MAX_DISPLAYED_BYTES - 1);
        assert!(term.unabridged().to_string().starts_with(cut));
    }

    #[test]
    fn display_elides_what_lies_past_the_depth_limit() {
        // On a 1 MiB stack: without the limit, writing this term 100,000 deep would take about
        // 400 MiB unoptimized. (The sort is 200 deep: dropping a sort recurses once per level.)
        let text = std::thread::Builder::new()
            .stack_size(1 << 20)
            .spawn(|| {
                let mut pool = PrimitivePool::new();
                let bool_sort = pool.add_sort(Sort::Bool);
                let mut term = pool.add(Term::new_var("p", bool_sort.clone()));
                for _ in 0..100_000 {
                    term = pool.add(Term::Op(Operator::Not, vec![term]));
                }
                let mut sort = bool_sort.clone();
                for _ in 0..200 {
                    sort = pool.add_sort(Sort::Array(sort, bool_sort.clone()));
                }
                (term.to_string(), sort.to_string())
            })
            .unwrap()
            .join()
            .unwrap();
        let n = MAX_DISPLAYED_DEPTH;
        assert_eq!(text.0, format!("{}...{}", "(not ".repeat(n), ")".repeat(n)));
        // The innermost `(Array x Bool)` written is `(Array ... ...)`: both sorts lie past the limit.
        assert_eq!(
            text.1,
            format!("{}... ...){}", "(Array ".repeat(n), " Bool)".repeat(n - 1))
        );
    }

    #[test]
    fn display_writes_a_shared_sort_abridged() {
        let mut pool = PrimitivePool::new();
        let mut sort = pool.add_sort(Sort::Bool);
        for _ in 0..64 {
            sort = pool.add_sort(Sort::Array(sort.clone(), sort));
        }
        for text in [sort.to_string(), format!("{sort:?}")] {
            assert!(text.starts_with("(Array (Array"), "{text}");
            assert!(text.ends_with("..."), "{text}");
            assert!(text.len() <= MAX_DISPLAYED_BYTES + 3);
        }
    }

    /// Every sort is written as upstream's `Display` for `Sort` wrote it, abridged or not.
    #[test]
    fn sorts_are_written_as_before() {
        let mut pool = PrimitivePool::new();
        let int = pool.add_sort(Sort::Int);
        let bool_sort = pool.add_sort(Sort::Bool);
        let real = pool.add_sort(Sort::Real);
        let cases = [
            (
                Sort::Function(vec![int.clone(), bool_sort.clone()]),
                "(-> Int Bool)",
            ),
            (Sort::Atom("U".into(), Box::new([])), "U"),
            (Sort::Atom("a b".into(), Box::new([])), "|a b|"),
            (
                Sort::Atom("Pair".into(), Box::new([int.clone(), real.clone()])),
                "(Pair Int Real)",
            ),
            (Sort::Bool, "Bool"),
            (Sort::Int, "Int"),
            (Sort::Real, "Real"),
            (Sort::String, "String"),
            (Sort::RegLan, "RegLan"),
            (Sort::Datatype { name: "D".into(), args: Vec::new() }, "D"),
            (
                Sort::Datatype {
                    name: "List".into(),
                    args: vec![int.clone()],
                },
                "(List Int)",
            ),
            (Sort::Var("T".into()), "T"),
            (
                Sort::Par(vec!["X".into(), "Y".into()], int.clone()),
                "(par (X Y) Int)",
            ),
            (Sort::Array(int.clone(), real.clone()), "(Array Int Real)"),
            (Sort::BitVec(32), "(_ BitVec 32)"),
            (Sort::ParamBitVec, "(_ BitVec ?)"),
            (Sort::Type, "Type"),
            (Sort::Set(int.clone()), "(Set Int)"),
            (Sort::Tuple(Vec::new()), "UnitTuple"),
            (
                Sort::Tuple(vec![int, bool_sort, real]),
                "(Tuple Int Bool Real)",
            ),
        ];
        for (sort, expected) in cases {
            assert_eq!(sort.to_string(), expected);
            assert_eq!(format!("{sort:?}"), expected);
            assert_eq!(sort.unabridged().to_string(), expected);
        }
    }

    /// `Display`, `unabridged()` and the proof printer write `match`, `as`, binders, `let`, sorts
    /// and constants as before (the texts are upstream's, `match`'s missing parenthesis included).
    #[test]
    fn terms_are_written_as_before() {
        use crate::parser;

        let definitions = "
            (declare-datatype Opt ((none) (some (val Int))))
            (declare-const o Opt)
            (declare-const a (Array Int Int))
            (declare-sort U 0)
            (declare-sort P 2)
            (define-sort Q () (P U (Array Int Bool)))
            (declare-const q Q)
            (declare-fun f (Q (_ BitVec 4)) Bool)
        ";
        let cases = [
            (
                "(= (match o ((none 0) ((some x) x))) 1)",
                "(= (match o (((none) 0)((some x) x)) 1)",
            ),
            (
                "(= a ((as const (Array Int Int)) 0))",
                "(= a ((as const (Array Int Int)) 0))",
            ),
            (
                "(forall ((x Int) (y (Array Int Bool))) (select y x))",
                "(forall ((x Int) (y (Array Int Bool))) (select y x))",
            ),
            ("(f q #b0101)", "(f q (_ bv5 4))"),
            (
                "(exists ((z Q)) (f z ((_ zero_extend 2) #b01)))",
                "(exists ((z (P U (Array Int Bool)))) (f z ((_ zero_extend 2) (_ bv1 2))))",
            ),
            (
                "(let ((w 3.0)) (= w (- 4.0 1.5 (- 2.5))))",
                "(let ((w 3.0)) (= w (- 4.0 3/2 (- 5/2))))",
            ),
        ];
        let proof: String = cases
            .iter()
            .enumerate()
            .map(|(i, (term, _))| format!("(step t{i} (cl {term}) :rule hole)\n"))
            .collect();
        let (problem, proof, _, mut pool) =
            parser::parse_instance(definitions, &proof, None, parser::Config::new()).unwrap();
        let mut buf = Vec::new();
        AlethePrinter::new(&mut pool, &problem.prelude, false, &mut buf)
            .write_proof(&proof)
            .unwrap();
        let printed = String::from_utf8(buf).unwrap();
        for (i, (command, (_, expected))) in proof.commands.iter().zip(cases).enumerate() {
            let ProofCommand::Step(step) = command else {
                panic!("not a step")
            };
            assert_eq!(step.clause[0].to_string(), expected);
            assert_eq!(step.clause[0].unabridged().to_string(), expected);
            let line = format!("(step t{i} (cl {expected}) :rule hole)");
            assert!(printed.contains(&line), "{printed}");
        }
        assert_eq!(
            problem.prelude.to_string(),
            "(set-logic ALL)\n(declare-sort U 0)\n(declare-sort P 2)\n(declare-fun o () Opt)\n\
             (declare-fun a () (Array Int Int))\n(declare-fun q () (P U (Array Int Bool)))\n\
             (declare-fun f ((P U (Array Int Bool)) (_ BitVec 4)) Bool)\n"
        );
    }
}
