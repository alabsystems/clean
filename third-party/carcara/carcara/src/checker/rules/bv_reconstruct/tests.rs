use super::*;

#[test]
fn fixed_private_state_fits_the_reservation() {
    assert!(
        std::mem::size_of::<Option<Pending>>() * (MAX_DEPTH + 1)
            + 128
            + std::mem::size_of::<Inspector>()
            < BYTES
    );
}

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
        panic!("no intermediate terms")
    }
    fn add_sort(&mut self, _: Sort) -> Rc<Sort> {
        panic!("no intermediate sorts")
    }
    fn find(&self, _: &Term) -> Option<Rc<Term>> {
        panic!("no term lookup/materialization")
    }
    fn sort(&self, t: &Rc<Term>) -> Rc<Sort> {
        assert!(!self.forbidden, "before admission");
        self.reads.set(self.reads.get() + 1);
        self.inner.sort(t)
    }
    fn free_vars(&mut self, _: &Rc<Term>) -> FreeVars {
        panic!("no opaque body walk")
    }
    fn get_datatype(&self, _: &str) -> &Datatype {
        panic!("no unrelated authority")
    }
}
fn run(
    root: &Rc<Term>,
    pool: &mut dyn TermPool,
    work: usize,
    bytes: usize,
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
        bytes,
        expired,
    )
}
#[test]
fn bounded_work_bytes_and_deadline_refuse_before_all_term_reads() {
    let mut pool = PrimitivePool::new();
    let sort = pool.add_sort(Sort::BitVec(8));
    let x = pool.add(Term::new_var("x", sort));
    let root = pool.add(Term::Op(Operator::Equals, vec![x.clone(), x]));
    let mut read = ReadPool {
        inner: &pool,
        reads: Cell::new(0),
        forbidden: true,
    };
    assert!(matches!(
        run(&root, &mut read, 1, BYTES, &mut || false),
        Err(CheckerError::BvReconstructWorkExceeded)
    ));
    assert!(matches!(
        run(&root, &mut read, WORK, BYTES - 1, &mut || false),
        Err(CheckerError::BvReconstructWorkExceeded)
    ));
    assert!(matches!(
        run(&root, &mut read, WORK, BYTES, &mut || true),
        Err(CheckerError::DeadlineExceeded)
    ));
    assert_eq!(read.reads.get(), 0);
}
#[test]
fn identical_deep_word_is_borrowed_and_does_not_materialize_or_walk() {
    let mut pool = PrimitivePool::new();
    let sort = pool.add_sort(Sort::BitVec(8));
    let mut word = pool.add(Term::new_var("x", sort));
    for _ in 0..4096 {
        word = pool.add(Term::Op(Operator::BvAdd, vec![word.clone(), word]));
    }
    let root = pool.add(Term::Op(Operator::Equals, vec![word.clone(), word]));
    let mut read = ReadPool {
        inner: &pool,
        reads: Cell::new(0),
        forbidden: false,
    };
    assert!(run(&root, &mut read, WORK, BYTES, &mut || false).is_ok());
    assert!(
        read.reads.get() <= 6,
        "opaque sort reads {}",
        read.reads.get()
    );
}
