// Added in Clean: the independent scalar inspector's boundary and work controls.
use super::*;
use crate::ast::pool::{PrimitivePool, TermPool};
use rug::Integer;

fn app(pool: &mut PrimitivePool, op: Operator, args: &[Rc<Term>]) -> Rc<Term> {
    pool.add(Term::Op(op, args.to_vec()))
}

fn claim(pool: &mut PrimitivePool, left: Rc<Term>, right: Rc<Term>, value: bool) -> Rc<Term> {
    let source = app(pool, Operator::Equals, &[left, right]);
    let target = pool.add(Term::new_bool(value));
    app(pool, Operator::Equals, &[source, target])
}

fn var(pool: &mut PrimitivePool, name: &str, width: usize) -> Rc<Term> {
    let sort = pool.add_sort(Sort::BitVec(width));
    pool.add(Term::new_var(name, sort))
}

#[test]
fn scalar_inspector_checks_canonical_literals_and_every_operand_sort() {
    let mut pool = PrimitivePool::new();
    let x = var(&mut pool, "x", 8);
    let zero = pool.add(Term::new_bv(0, 8));
    let one = pool.add(Term::new_bv(1, 8));
    let valid = claim(&mut pool, zero.clone(), one.clone(), false);
    assert!(holds(&[valid], &pool).unwrap());

    let negative = pool.add(Term::Const(Constant::BitVec(Integer::from(-1), 8)));
    let oversized = pool.add(Term::Const(Constant::BitVec(Integer::from(256), 8)));
    let other_width = pool.add(Term::new_bv(1, 7));
    let boolean = pool.add(Term::new_bool(true));
    for bad in [negative, oversized, other_width, boolean] {
        let left = app(&mut pool, Operator::BvAdd, &[x.clone(), zero.clone()]);
        let right = app(&mut pool, Operator::BvAdd, &[x.clone(), bad]);
        let root = claim(&mut pool, left, right, false);
        assert!(!holds(&[root], &pool).unwrap());
    }
    for width in [0, 129, usize::MAX] {
        let a = pool.add(Term::Const(Constant::BitVec(Integer::from(0), width)));
        let b = pool.add(Term::Const(Constant::BitVec(Integer::from(1), width)));
        let root = claim(&mut pool, a, b, false);
        assert!(!holds(&[root], &pool).unwrap());
    }
}

#[test]
fn scalar_inspector_refuses_bad_arity_operator_base_and_result() {
    let mut pool = PrimitivePool::new();
    let x = var(&mut pool, "x", 8);
    let y = var(&mut pool, "y", 8);
    let a = pool.add(Term::new_bv(0, 8));
    let b = pool.add(Term::new_bv(1, 8));
    let left = app(&mut pool, Operator::BvAdd, &[x.clone(), a.clone()]);
    for right in [
        app(&mut pool, Operator::BvAdd, &[]),
        app(&mut pool, Operator::BvAdd, &[x.clone()]),
        app(
            &mut pool,
            Operator::BvAdd,
            &[x.clone(), b.clone(), a.clone()],
        ),
        app(&mut pool, Operator::BvMul, &[x.clone(), b.clone()]),
        app(&mut pool, Operator::BvAdd, &[y, b.clone()]),
    ] {
        let root = claim(&mut pool, left.clone(), right, false);
        assert!(!holds(&[root], &pool).unwrap());
    }
    let right = app(&mut pool, Operator::BvAdd, &[x, b]);
    let wrong = claim(&mut pool, left, right, true);
    assert!(!holds(&[wrong], &pool).unwrap());
}

#[test]
fn scalar_inspector_charges_success_and_failure_before_inspection() {
    let mut pool = PrimitivePool::new();
    let x = var(&mut pool, "x", 128);
    let a = pool.add(Term::new_bv(0, 128));
    let b = pool.add(Term::new_bv(u128::MAX, 128));
    let left = app(&mut pool, Operator::BvAdd, &[a, x.clone()]);
    let right = app(&mut pool, Operator::BvAdd, &[x, b]);
    let valid = claim(&mut pool, left.clone(), right.clone(), false);
    let invalid = claim(&mut pool, left, right, true);
    for (root, expected) in [(valid, true), (invalid, false)] {
        let first_complete = (0..=MAX_WORK)
            .find(|&budget| holds_with_budget(&[root.clone()], &pool, budget).is_ok())
            .expect("both bounded attempts must finish within the published budget");
        assert!(first_complete > 0);
        assert!(matches!(
            holds_with_budget(&[root.clone()], &pool, first_complete - 1),
            Err(CheckerError::BvEqSimplifyWorkExceeded)
        ));
        assert_eq!(
            holds_with_budget(&[root], &pool, first_complete).unwrap(),
            expected
        );
    }
}

#[test]
fn scalar_inspector_keeps_a_deep_common_base_opaque() {
    let mut pool = PrimitivePool::new();
    let mut base = var(&mut pool, "x", 64);
    let a = pool.add(Term::new_bv(0, 64));
    let b = pool.add(Term::new_bv(1, 64));
    for _ in 0..4_096 {
        base = app(&mut pool, Operator::BvXor, &[base, b.clone()]);
    }
    let left = app(&mut pool, Operator::BvAdd, &[base.clone(), a]);
    let right = app(&mut pool, Operator::BvAdd, &[b, base]);
    let root = claim(&mut pool, left, right, false);
    let before = pool.terms.len();
    assert!(holds(&[root], &pool).unwrap());
    assert_eq!(
        pool.terms.len(),
        before,
        "inspection must materialize no terms"
    );
}
