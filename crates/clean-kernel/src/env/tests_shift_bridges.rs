// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::TypeChecker;

#[test]
fn shift_bridges_require_checked_homogeneous_dictionaries() {
    let env = Environment::with_prelude();
    let tc = TypeChecker::new(&env);
    for class in ["ShiftLeft", "ShiftRight"] {
        let info = env
            .get_class_info(&Name::from_string(class))
            .expect("shift class");
        assert_eq!(info.num_params, 1);
        assert!(info.out_params.is_empty());
        let bridge_name = Name::from_string(&format!("instH{class}"));
        let bridge = env.get_const(&bridge_name).expect("default bridge");
        let bridge_sort = tc
            .infer_type(&bridge.type_)
            .expect("well-formed bridge type");
        assert!(matches!(bridge_sort.kind(), ExprKind::Sort(_)));
        assert!(env.is_default_instance(&bridge_name));
        assert!(env
            .axiom_deps(&bridge_name)
            .expect("bridge closure")
            .is_empty());
        let ExprKind::Pi(_, _, after_alpha) = bridge.type_.kind() else {
            panic!("bridge must quantify its carrier")
        };
        let ExprKind::Pi(binder, premise, _) = after_alpha.kind() else {
            panic!("bridge must require a dictionary")
        };
        assert_eq!(binder.info, BinderInfo::InstImplicit);
        assert_eq!(
            premise.get_app_fn(),
            &Expr::const_(
                Name::from_string(class),
                vec![Level::param(Name::from_string("u"))]
            )
        );
        assert_eq!(premise.get_app_args().as_slice(), &[&Expr::bvar(0)]);
        for carrier in ["Nat", "UInt8", "UInt16", "UInt32", "UInt64"] {
            let carrier_ty = Expr::const_(Name::from_string(carrier), vec![]);
            let instance_name = Name::from_string(&format!("inst{class}{carrier}"));
            let instance = Expr::const_(instance_name.clone(), vec![]);
            let expected = Expr::app(
                Expr::const_(Name::from_string(class), vec![Level::zero()]),
                carrier_ty.clone(),
            );
            tc.check_type(&instance, &expected)
                .expect("checked homogeneous dictionary");
            assert!(env
                .axiom_deps(&instance_name)
                .expect("instance closure")
                .is_empty());
            let through_bridge = Expr::app(
                Expr::app(
                    Expr::const_(bridge_name.clone(), vec![Level::zero()]),
                    carrier_ty,
                ),
                instance,
            );
            let direct = Expr::const_(Name::from_string(&format!("instH{class}{carrier}")), vec![]);
            assert!(tc.is_def_eq(&through_bridge, &direct), "{class} {carrier}");
        }
    }
    assert!(env
        .get_const(&Name::from_string("instShiftLeftBitVec"))
        .is_none());
    assert!(env
        .get_const(&Name::from_string("instShiftRightBitVec"))
        .is_none());
}
