// Added in Clean (not part of upstream Carcara). See third-party/carcara/DOWNSTREAM.md,
// completeness extension C2.
//
//! Datatype rules.
//!
//! Upstream Carcara has no datatype rule: constructors and selectors are registered as ordinary
//! function symbols (`parser/datatypes.rs`), so with no rule a proof cannot use the defining
//! property of a selector at all.
//!
//! `dt_project` is that property. Its conclusion is the unit clause
//!
//! ```text
//! (= (S (C t_0 ... t_n)) t_i)
//! ```
//!
//! where `C` is a constructor of a non-parametric datatype and `S` is the `i`-th selector *of
//! `C`*. Every SMT-LIB model of a datatype satisfies it, because a model interprets `C` and its
//! selectors as the constructor and projections of a term algebra. Nothing else is accepted: a
//! selector of a different constructor (whose value SMT-LIB leaves unspecified), an uninterpreted
//! function, either orientation but this one (use `symm` for the other), a conclusion with more
//! than one literal, premises or arguments.
//!
//! Symbols are identified by name and sort, which is all a `Term::Var` carries. Three things make
//! that identification sound:
//!
//! - The parser refuses any global declaration (including a `define-fun` expanded as a macro and a
//!   `:named` term) that shares its name and argument sorts with a datatype constructor, selector
//!   or tester, in either order; a datatype declared twice, or named like a `declare-sort` or
//!   `define-sort` sort; and a name used twice inside one datatype (`parser/mod.rs`,
//!   `parser/datatypes.rs`). A `par` symbol counts as overlapping every declaration of its arity.
//! - The parser instantiates a `par` symbol `f` only at an instance of its own sort, which has
//!   `f`'s arity: `(as f S)` requires `S` to be one, and `((as f S) ..)` substitutes into `f`'s
//!   sort (`parser/mod.rs`; `Sort::match_with` compares lengths). So a `par` symbol of another
//!   arity cannot be qualified into the `Term::Var` of a same-named symbol of a non-parametric
//!   datatype, and `as` refuses a symbol that is not `par`. With the first point, outside an
//!   anchor `S` and `C` can only denote the datatype's own symbols.
//! - Inside an anchor, an argument `(S (-> D T))` or `(C (-> T.. D))` binds a variable that is the
//!   very same `Term::Var`. The rule refuses a conclusion whose selector or constructor name is
//!   bound by any enclosing anchor.

use super::{assert_clause_len, assert_eq, assert_num_args, assert_num_premises, RuleArgs};
use super::{CheckerError, RuleResult};
use crate::ast::{match_term_err, Rc, Sort, Term};
use crate::checker::scoping::arg_name;

fn refuse(reason: &str) -> RuleResult {
    Err(CheckerError::Explanation(format!("dt_project: {}", reason)))
}

pub fn dt_project(
    RuleArgs {
        conclusion,
        premises,
        args,
        pool,
        context,
        ..
    }: RuleArgs,
) -> RuleResult {
    assert_num_premises(premises, 0)?;
    assert_num_args(args, 0)?;
    assert_clause_len(conclusion, 1)?;

    let (projection, value) = match_term_err!((= p v) = &conclusion[0])?;

    // `(S (C t_0 ... t_n))`, with `S` and `C` plain symbols.
    let Term::App(selector, selector_args) = projection.as_ref() else {
        return refuse("the left side is not a selector application");
    };
    let [constructed] = selector_args.as_slice() else {
        return refuse("a selector takes exactly one argument");
    };
    let Term::Var(selector_name, selector_sort) = selector.as_ref() else {
        return refuse("the selector is not a symbol");
    };
    let Term::App(constructor, fields) = constructed.as_ref() else {
        return refuse("the selector is not applied to a constructor application");
    };
    let Term::Var(constructor_name, constructor_sort) = constructor.as_ref() else {
        return refuse("the constructor is not a symbol");
    };

    // An anchor argument with the same name is a variable, not the datatype's symbol.
    for depth in 0..context.len() {
        let Some(anchor_args) = context.args_at(depth) else {
            return refuse("an enclosing context is missing");
        };
        if anchor_args.iter().any(|arg| {
            let name = arg_name(arg);
            name == selector_name.as_str() || name == constructor_name.as_str()
        }) {
            return refuse("an enclosing anchor binds the selector or constructor name");
        }
    }

    // `C : (-> T_0 .. T_n D)`, with `D` a declared, non-parametric datatype.
    let Sort::Function(constructor_sorts) = constructor_sort.as_ref() else {
        return refuse("the constructor is not a function symbol");
    };
    let Some((datatype_sort, field_sorts)) = constructor_sorts.split_last() else {
        return refuse("the constructor has an empty sort");
    };
    let Sort::Datatype {
        name: datatype_name,
        args: sort_args,
    } = datatype_sort.as_ref()
    else {
        return refuse("the constructor does not return a datatype");
    };
    // A constructor of a parametric datatype written bare has a `(par ..)` sort and was refused
    // above; qualified with `as`, as in `((as some (Opt Int)) a)`, its sort is instantiated and it
    // is refused here.
    if !sort_args.is_empty() {
        return refuse("parametric datatypes are not supported");
    }
    // `get_datatype` is only reached for a `Sort::Datatype`, which the parser creates only for a
    // declared datatype, so the lookup cannot miss.
    let datatype = pool.get_datatype(datatype_name);
    // A backup for the check above, never reached while it is there: the parser gives a
    // parametric datatype's sort its arguments. With the check above removed, this one refuses the
    // `as`-qualified constructor with the same message (measured by mutation).
    if !datatype.params.is_empty() {
        return refuse("parametric datatypes are not supported");
    }
    let Some(declaration) = datatype.constructors.get(constructor_name.as_str()) else {
        return refuse("the constructor is not a constructor of its datatype");
    };
    let selectors = &declaration.selectors;
    if selectors.len() != fields.len() || selectors.len() != field_sorts.len() {
        return refuse("the constructor is applied with the wrong arity");
    }
    if selectors
        .iter()
        .zip(field_sorts)
        .any(|((_, declared), used)| declared != used)
    {
        return refuse("the constructor's sort does not match its declaration");
    }

    // The selector and the constructor must each be one symbol of the datatype, never two: the
    // parser refuses such declarations, and this keeps the rule independent of that.
    let is_selector_of_datatype = |name: &str| {
        datatype
            .constructors
            .values()
            .flat_map(|c| c.selectors.iter())
            .filter(|(selector, _)| selector == name)
            .count()
    };
    if is_selector_of_datatype(selector_name) != 1
        || datatype.constructors.contains_key(selector_name.as_str())
        || is_selector_of_datatype(constructor_name) != 0
    {
        return refuse("the selector or constructor name is ambiguous in its datatype");
    }

    // `S` is the `i`-th selector of `C`, with sort `(-> D T_i)`.
    let Some(i) = selectors.iter().position(|(name, _)| name == selector_name) else {
        return refuse("the selector does not belong to this constructor");
    };
    let field_sort: &Rc<Sort> = &selectors[i].1;
    let expected_selector_sort = [datatype_sort.clone(), field_sort.clone()];
    match selector_sort.as_ref() {
        Sort::Function(sorts) if sorts.as_slice() == expected_selector_sort.as_slice() => {}
        _ => return refuse("the selector's sort does not match its declaration"),
    }
    if pool.sort(&fields[i]) != *field_sort {
        return refuse("the projected field does not have the declared sort");
    }

    assert_eq(value, &fields[i])
}
