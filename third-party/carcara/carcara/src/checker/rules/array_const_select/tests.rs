use super::*;
use crate::ast::{
    pool::{Datatype, FreeVars, PrimitivePool},
    rare_rules::Rules,
    ContextStack,
};
use std::{cell::Cell, time::Duration};

struct ReadPool<'a> {
    inner: &'a PrimitivePool,
    reads: Cell<usize>,
    forbidden: bool,
}
impl TermPool for ReadPool<'_> {
    fn add(&mut self, _: Term) -> Rc<Term> {
        panic!("no constructed terms")
    }
    fn add_sort(&mut self, _: Sort) -> Rc<Sort> {
        panic!("no constructed sorts")
    }
    fn find(&self, _: &Term) -> Option<Rc<Term>> {
        panic!("no unrelated lookup")
    }
    fn sort(&self, t: &Rc<Term>) -> Rc<Sort> {
        assert!(!self.forbidden);
        self.reads.set(self.reads.get() + 1);
        self.inner.sort(t)
    }
    fn free_vars(&mut self, _: &Rc<Term>) -> FreeVars {
        panic!("no opaque body walk")
    }
    fn get_datatype(&self, _: &str) -> &Datatype {
        panic!("no datatype authority")
    }
}
fn run(
    root: &Rc<Term>,
    pool: &mut dyn TermPool,
    work: usize,
    expired: &mut dyn FnMut() -> bool,
) -> RuleResult {
    let clause = [root.clone()];
    let rules = Rules { rules: Default::default() };
    let mut context = ContextStack::new();
    let mut time = Duration::ZERO;
    validate_with_control(
        RuleArgs {
            conclusion: &clause,
            premises: &[],
            args: &[],
            pool,
            context: &mut context,
            rare_rules: &rules,
            previous_command: None,
            discharge: &[],
            polyeq_time: &mut time,
        },
        work,
        expired,
    )
}
fn exact(pool: &mut PrimitivePool, name: &str) -> Rc<Term> {
    let bool_sort = pool.add_sort(Sort::Bool);
    let index = pool.add_sort(Sort::BitVec(32));
    let key = pool.add(Term::new_var(name, index.clone()));
    let fill = pool.add(Term::new_var("fill", bool_sort.clone()));
    let array_sort = pool.add_sort(Sort::Array(index, bool_sort));
    let array = pool.add(Term::AsOp(
        QualifiedOperator::Const,
        array_sort,
        vec![fill.clone()],
    ));
    let read = pool.add(Term::Op(Operator::Select, vec![array, key]));
    pool.add(Term::Op(Operator::Equals, vec![read, fill]))
}
#[test]
fn array_const_select_short_work_and_initial_stop_refuse_before_ast_reads() {
    let mut pool = PrimitivePool::new();
    let root = exact(&mut pool, "k");
    let mut read = ReadPool {
        inner: &pool,
        reads: Cell::new(0),
        forbidden: true,
    };
    assert!(matches!(
        run(&root, &mut read, WORK - 1, &mut || false),
        Err(CheckerError::ArrayConstSelectWorkExceeded)
    ));
    assert!(matches!(
        run(&root, &mut read, WORK, &mut || true),
        Err(CheckerError::DeadlineExceeded)
    ));
    assert_eq!(read.reads.get(), 0);
}
#[test]
fn array_const_select_fixed_work_borrows_wide_names_and_checks_final_stop() {
    let mut pool = PrimitivePool::new();
    let root = exact(&mut pool, &"k".repeat(100_000));
    let mut read = ReadPool {
        inner: &pool,
        reads: Cell::new(0),
        forbidden: false,
    };
    assert!(run(&root, &mut read, WORK, &mut || false).is_ok());
    assert_eq!(read.reads.get(), 1);
    for stop_at in 1..=2 {
        let mut calls = 0;
        assert!(matches!(
            run(&root, &mut read, WORK, &mut || {
                calls += 1;
                calls == stop_at
            }),
            Err(CheckerError::DeadlineExceeded)
        ));
        assert_eq!(calls, stop_at);
    }
}
