// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Exercise structural-cache retirement by a real outer fast-inference frame.

use crate::cert::CertVerifier;
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;
use crate::{Environment, TypeChecker, TypeError};
use std::cell::{Cell, RefCell};
use std::rc::{Rc, Weak};

#[test]
fn outer_fast_frame_clears_reentrant_certificate_support_on_success_and_error() {
    let env = Environment::new();
    let identity = Expr::lam(BinderInfo::Default, Expr::prop(), Expr::bvar(0));
    let identity_type = Expr::arrow(Expr::prop(), Expr::prop());
    let mut nested = identity.clone();
    for _ in 0..8 {
        nested = Expr::let_named(
            Name::from_string("saved"),
            identity_type.clone(),
            identity.clone(),
            nested,
            false,
        );
    }

    for succeeds in [true, false] {
        let entered = Rc::new(Cell::new(false));
        let retained = Rc::new(RefCell::new(Vec::new()));
        // The existing elaborator callback is a production reentry point.
        // Its Weak reference cannot create an ownership cycle, and it returns
        // the ordinary level-equality result: no typing rule is weakened.
        let checker: Rc<TypeChecker<'_>> = Rc::new_cyclic(|owner: &Weak<TypeChecker<'_>>| {
            let owner = owner.clone();
            let entered = entered.clone();
            let retained = retained.clone();
            let nested = nested.clone();
            let expected = identity_type.clone();
            let mut checker = TypeChecker::new(&env);
            checker.set_level_params(vec![Name::from_string("u"), Name::from_string("v")]);
            checker.set_level_eq_override(move |left, right| {
                if !entered.replace(true) {
                    let checker = owner.upgrade().expect("live outer inference caller");
                    let outer_depth = checker.infer_memo_depth.get();
                    assert!(outer_depth > 0, "must be inside the real fast frame");
                    assert_eq!(checker.rebind_closed_memo.borrow().len(), 0);
                    let (ty, certificate) = checker
                        .infer_type_with_cert(&nested)
                        .expect("reentrant actual certificate inference");
                    assert_eq!(ty, expected);
                    assert_eq!(checker.infer_memo_depth.get(), outer_depth);
                    let memo = checker.rebind_closed_memo.borrow();
                    assert!(memo.len() > 0, "nested exit must preserve the outer cache");
                    assert!(memo.hits > 0, "actual binder exits must reuse support");
                    assert!(memo
                        .entries
                        .values()
                        .any(|(owner, _)| owner.upgrade().is_some()));
                    drop(memo);
                    retained.borrow_mut().push(certificate);
                }
                Level::is_def_eq(left, right)
            });
            checker
        });

        let u = Level::param(Name::from_string("u"));
        let v = Level::param(Name::from_string("v"));
        let (left, right) = if succeeds {
            (Level::max(u.clone(), v.clone()), Level::max(v, u))
        } else {
            (u, v)
        };
        assert_ne!(
            left, right,
            "avoid structural equality bypassing the callback"
        );
        assert_eq!(Level::is_def_eq(&left, &right), succeeds);
        // The full fast App check compares Sort(succ right), the argument's
        // type, with Sort(succ left), the lambda's required domain.
        let term = Expr::app(
            Expr::lam(
                BinderInfo::Default,
                Expr::sort(Level::succ(left)),
                Expr::prop(),
            ),
            Expr::sort(right),
        );
        let result = checker.infer_type_full(&term);
        if succeeds {
            assert_eq!(result.expect("equal universe levels"), Expr::type_());
        } else {
            assert!(matches!(result, Err(TypeError::TypeMismatch { .. })));
        }
        assert!(entered.get(), "the callback must actually warm the cache");
        assert_eq!(checker.infer_memo_depth.get(), 0);
        assert_eq!(checker.ctx_len(), 0);
        assert_eq!(checker.rebind_closed_memo.borrow().len(), 0);
        assert!(checker.infer_arc_memo.borrow().is_empty());
        assert!(checker.infer_only.get());

        // Keep the genuine certificate alive beyond outer-cache retirement,
        // and replay it through an independent verifier without the callback.
        let retained = retained.borrow();
        assert_eq!(retained.len(), 1);
        assert_eq!(
            CertVerifier::new(&env)
                .verify(&retained[0], &nested)
                .expect("retained certificate survives outer fast cleanup"),
            identity_type
        );
    }
}
