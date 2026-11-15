// Added in Clean: independent boundary, work and deadline controls for v1.
use super::*;
use crate::ast::{
    pool::{Datatype, FreeVars, PrimitivePool},
    rare_rules::Rules,
    ContextStack,
};
use rug::Integer;
use std::{
    cell::Cell,
    time::{Duration, Instant},
};

fn app(pool: &mut PrimitivePool, op: Operator, args: &[Rc<Term>]) -> Rc<Term> {
    pool.add(Term::Op(op, args.to_vec()))
}
fn var(pool: &mut PrimitivePool, name: &str, width: usize) -> Rc<Term> {
    let sort = pool.add_sort(Sort::BitVec(width));
    pool.add(Term::new_var(name, sort))
}
fn claim(pool: &mut PrimitivePool, a: Rc<Term>, b: Rc<Term>, truth: bool) -> Rc<Term> {
    let eq = app(pool, Operator::Equals, &[a, b]);
    let truth = pool.add(Term::new_bool(truth));
    app(pool, Operator::Equals, &[eq, truth])
}
fn spine(
    pool: &mut PrimitivePool,
    mut base: Rc<Term>,
    frames: usize,
    literal: Rc<Term>,
) -> Rc<Term> {
    for i in 0..frames {
        base = if i % 3 == 0 {
            app(pool, Operator::BvSub, &[base, literal.clone()])
        } else if i % 3 == 1 {
            app(pool, Operator::BvAdd, &[literal.clone(), base])
        } else {
            app(pool, Operator::BvAdd, &[base, literal.clone()])
        };
    }
    base
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

struct ReadPool<'a> {
    inner: &'a PrimitivePool,
    reads: Cell<usize>,
    forbidden: bool,
    changed_sort: Option<(Rc<Term>, Rc<Sort>)>,
}
impl TermPool for ReadPool<'_> {
    fn add(&mut self, _: Term) -> Rc<Term> {
        panic!("inspector must not materialize terms")
    }
    fn add_sort(&mut self, _: Sort) -> Rc<Sort> {
        panic!("inspector must not materialize sorts")
    }
    fn find(&self, _: &Term) -> Option<Rc<Term>> {
        panic!("inspector must not build terms")
    }
    fn sort(&self, term: &Rc<Term>) -> Rc<Sort> {
        assert!(!self.forbidden, "access before work/deadline admission");
        self.reads.set(self.reads.get() + 1);
        match &self.changed_sort {
            Some((changed, sort)) if changed == term => sort.clone(),
            _ => self.inner.sort(term),
        }
    }
    fn free_vars(&mut self, _: &Rc<Term>) -> FreeVars {
        panic!("opaque base traversal")
    }
    fn get_datatype(&self, _: &str) -> &Datatype {
        panic!("unrelated semantic authority")
    }
}

#[test]
fn spine_work_admission_and_deadline_precede_any_term_access() {
    let mut pool = PrimitivePool::new();
    let x = var(&mut pool, "x", 64);
    let root = claim(&mut pool, x.clone(), x, true);
    let mut unread = ReadPool {
        inner: &pool,
        reads: Cell::new(0),
        forbidden: true,
        changed_sort: None,
    };
    assert!(matches!(
        run(&root, &mut unread, 0, &mut || panic!(
            "work denial precedes poll"
        )),
        Err(CheckerError::BvOffsetSpinesWorkExceeded)
    ));
    assert!(matches!(
        run(&root, &mut unread, MAX_WORK, &mut || true),
        Err(CheckerError::DeadlineExceeded)
    ));
    assert_eq!(unread.reads.get(), 0);
    let _armed = deadline::arm(Some(Instant::now()));
    assert!(matches!(
        run(&root, &mut unread, MAX_WORK, &mut deadline::expired_now),
        Err(CheckerError::DeadlineExceeded)
    ));
}

#[test]
fn spine_success_and_failure_share_one_bounded_meter_and_cancel_between_frames() {
    let mut pool = PrimitivePool::new();
    let x = var(&mut pool, "x", 128);
    let y = var(&mut pool, "y", 128);
    let zero = pool.add(Term::new_bv(0, 128));
    let left = spine(&mut pool, x.clone(), 16, zero.clone());
    let right = spine(&mut pool, x, 16, zero.clone());
    let valid = claim(&mut pool, left.clone(), right.clone(), true);
    let wrong = claim(&mut pool, left.clone(), right, false);
    let other = spine(&mut pool, y, 16, zero);
    let alias = claim(&mut pool, left, other, true);
    for root in [&valid, &wrong, &alias] {
        // This allowance admits one complete sixteen-frame side. The second
        // side must spend from the same remaining allowance, even on refusal.
        assert!(matches!(
            run(root, &mut pool, 3_000, &mut || false),
            Err(CheckerError::BvOffsetSpinesWorkExceeded)
        ));
        let complete = (0..=MAX_WORK)
            .find(|&work| {
                !matches!(
                    run(root, &mut pool, work, &mut || false),
                    Err(CheckerError::BvOffsetSpinesWorkExceeded)
                )
            })
            .expect("fixed accounting envelope");
        assert!(complete > 0 && complete <= 6816, "cost {complete}");
        assert!(matches!(
            run(root, &mut pool, complete - 1, &mut || false),
            Err(CheckerError::BvOffsetSpinesWorkExceeded)
        ));
    }
    assert!(run(&valid, &mut pool, MAX_WORK, &mut || false).is_ok());
    assert!(matches!(
        run(&wrong, &mut pool, MAX_WORK, &mut || false),
        Err(CheckerError::BvOffsetSpinesInvalid)
    ));
    let mut polls = 0;
    let cancelled = run(&valid, &mut pool, MAX_WORK, &mut || {
        polls += 1;
        polls == 4
    });
    assert!(matches!(cancelled, Err(CheckerError::DeadlineExceeded)));
    assert_eq!(
        polls, 4,
        "a refusal must never start another direction or side"
    );
}

#[test]
fn spine_cap_is_sixteen_and_frame_seventeen_is_not_hidden_as_a_base() {
    for width in [1, 8, 64, 128] {
        let mut pool = PrimitivePool::new();
        let x = var(&mut pool, "x", width);
        let zero = pool.add(Term::new_bv(0, width));
        for (left_frames, right_frames, accepted) in [
            (0, 0, true),
            (16, 16, true),
            (17, 16, false),
            (16, 17, false),
            (17, 17, false),
        ] {
            let a = spine(&mut pool, x.clone(), left_frames, zero.clone());
            let b = spine(&mut pool, x.clone(), right_frames, zero.clone());
            let root = claim(&mut pool, a, b, true);
            assert_eq!(
                run(&root, &mut pool, MAX_WORK, &mut || false).is_ok(),
                accepted,
                "w={width} left={left_frames} right={right_frames}"
            );
        }
    }
}

#[test]
fn spine_malformed_literals_opened_heads_and_recorded_sorts_refuse() {
    let mut pool = PrimitivePool::new();
    let x = var(&mut pool, "x", 8);
    let zero = pool.add(Term::new_bv(0, 8));
    let one = pool.add(Term::new_bv(1, 8));
    let bad_literals = [
        pool.add(Term::Const(Constant::BitVec(Integer::from(-1), 8))),
        pool.add(Term::Const(Constant::BitVec(Integer::from(256), 8))),
        pool.add(Term::new_bv(1, 7)),
        pool.add(Term::new_int(1)),
        pool.add(Term::new_bool(true)),
    ];
    for literal in bad_literals {
        let source = app(&mut pool, Operator::BvAdd, &[x.clone(), literal]);
        let root = claim(&mut pool, source, x.clone(), true);
        assert!(matches!(
            run(&root, &mut pool, MAX_WORK, &mut || false),
            Err(CheckerError::BvOffsetSpinesInvalid)
        ));
    }
    for op in [Operator::BvAdd, Operator::BvSub] {
        for args in [
            vec![],
            vec![x.clone()],
            vec![x.clone(), zero.clone(), one.clone()],
            vec![zero.clone(), one.clone()],
        ] {
            let source = app(&mut pool, op, &args);
            let root = claim(&mut pool, source, x.clone(), true);
            assert!(run(&root, &mut pool, MAX_WORK, &mut || false).is_err());
        }
    }
    let source = app(&mut pool, Operator::BvAdd, &[x.clone(), zero]);
    let root = claim(&mut pool, source.clone(), x, true);
    let int = pool.add_sort(Sort::Int);
    for changed in [root.clone(), source] {
        let mut wrong = ReadPool {
            inner: &pool,
            reads: Cell::new(0),
            forbidden: false,
            changed_sort: Some((changed, int.clone())),
        };
        assert!(run(&root, &mut wrong, MAX_WORK, &mut || false).is_err());
    }
}

#[test]
fn spine_opaque_shared_base_is_not_traversed_and_no_term_is_materialized() {
    let mut pool = PrimitivePool::new();
    let mut base = var(&mut pool, "x", 64);
    let one = pool.add(Term::new_bv(1, 64));
    for _ in 0..4096 {
        base = app(&mut pool, Operator::BvXor, &[base, one.clone()]);
    }
    let a = app(&mut pool, Operator::BvAdd, &[base.clone(), one.clone()]);
    let a = app(&mut pool, Operator::BvSub, &[a, one]);
    let root = claim(&mut pool, a, base, true);
    let before = pool.terms.len();
    let mut read = ReadPool {
        inner: &pool,
        reads: Cell::new(0),
        forbidden: false,
        changed_sort: None,
    };
    assert!(run(&root, &mut read, MAX_WORK, &mut || false).is_ok());
    assert!(
        read.reads.get() < 40,
        "opaque base must cost only cached root reads"
    );
    assert_eq!(pool.terms.len(), before);
}
