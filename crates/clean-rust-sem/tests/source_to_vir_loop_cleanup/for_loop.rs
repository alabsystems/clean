// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use clean_rust_sem::vir::Stmt;

use super::support::{
    anonymous_local_of_named_type, anonymous_mut_ref_local, for_discriminant_bool_local,
    for_loop_some_body_block, iterator_next_continuation_block, lowered_main,
};

#[test]
fn test_for_iterator_receiver_temp_drops_after_next_call() {
    let source = r#"
        fn main() -> u32 {
            let values: [u32; 3] = [1u32, 2u32, 3u32];
            for _item in &values {
            }
            0u32
        }
    "#;

    let body = lowered_main(source);
    let iter_ref = anonymous_mut_ref_local(&body);
    let next_cont = iterator_next_continuation_block(&body);

    match &body.blocks[next_cont as usize].terminator {
        clean_rust_sem::vir::Term::Drop {
            place: clean_rust_sem::Place::Local(drop_local),
            ..
        } if *drop_local == iter_ref => {}
        terminator => panic!(
            "for-loop lowering should drop the temporary `&mut iter` receiver on the `Iterator::next` continuation block, found {terminator:?} in {body:#?}"
        ),
    }
}

#[test]
fn test_for_discriminant_local_retired_before_body() {
    let source = r#"
        fn main() -> u32 {
            for _i in 0u32..3u32 {
            }
            0u32
        }
    "#;

    let body = lowered_main(source);
    let next_result = anonymous_local_of_named_type(&body, "Option");
    let discrim = for_discriminant_bool_local(&body, next_result);
    let some_block = for_loop_some_body_block(&body);

    let first_stmt = body.blocks[some_block as usize]
        .statements
        .first()
        .expect("body block should have at least one statement");
    match first_stmt {
        Stmt::StorageDead(local) => assert_eq!(
            *local, discrim,
            "StorageDead should target the discriminant Bool local: {body:#?}"
        ),
        other => panic!(
            "for-loop body block should retire the discriminant Bool local immediately \
             via StorageDead, found {other:?} in {body:#?}"
        ),
    }
}
