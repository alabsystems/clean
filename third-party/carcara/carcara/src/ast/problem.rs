use super::{Rc, Sort, Term};
use indexmap::IndexSet;

/// An SMT problem in the SMT-LIB format.
#[derive(Debug, Clone, Default)]
pub struct Problem {
    /// The problem's prelude.
    pub prelude: ProblemPrelude,

    /// The proof's premises.
    ///
    /// Those are the terms introduced in the original problem's `assert` commands.
    pub premises: IndexSet<Rc<Term>>,
}

impl Problem {
    /// Constructs a new empty `Problem`.
    pub fn new() -> Self {
        Self::default()
    }
}

/// The prelude of an SMT-LIB problem instance.
///
/// This stores the sort declarations, function declarations and the problem's logic string.
#[derive(Debug, Clone, Default)]
pub struct ProblemPrelude {
    /// The sort declarations, each represented by its name and arity.
    pub(crate) sort_declarations: Vec<(String, usize)>,

    /// The function declarations, each represented by its name and sort.
    pub(crate) function_declarations: Vec<(String, Rc<Sort>)>,

    /// The problem's logic string, if it exists.
    pub(crate) logic: Option<String>,
}

impl ProblemPrelude {
    /// Constructs a new empty `ProblemPrelude`.
    pub fn new() -> Self {
        Self::default()
    }

    /// Modified in Clean: read access to the `declare-fun`/`declare-const` declarations, for the
    /// soundness battery (`third-party/carcara/soundness`), which reads a datatype symbol that one
    /// of them redeclares with the same sort as uninterpreted.
    pub fn function_declarations(&self) -> &[(String, Rc<Sort>)] {
        &self.function_declarations
    }
}
