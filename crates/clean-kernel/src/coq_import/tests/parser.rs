// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use crate::coq_import::{parse_declaration, Constr, GlobalDecl};

#[test]
fn coq_parse_normalized_definition_declaration() {
    let input = r#"
        (definition
          (name "Coq.Init.Logic.id")
          (levels (u))
          (type
            (prod
              (binder (name "A") (info implicit) (type (sort (type u))))
              (prod
                (binder (name "x") (type (rel 1)))
                (rel 1))))
          (value
            (lambda
              (binder (name "A") (info implicit) (type (sort (type u))))
              (lambda
                (binder (name "x") (type (rel 1)))
                (rel 1)))))
    "#;

    let decl = parse_declaration(input).expect("parse definition");
    let GlobalDecl::Constant(decl) = decl else {
        panic!("expected constant declaration");
    };
    assert_eq!(decl.name.as_dotted(), "Coq.Init.Logic.id");
    assert_eq!(decl.universe_params, vec!["u".to_string()]);
    assert!(matches!(decl.type_, Constr::Prod { .. }));
    assert!(matches!(decl.value, Some(Constr::Lambda { .. })));
}
