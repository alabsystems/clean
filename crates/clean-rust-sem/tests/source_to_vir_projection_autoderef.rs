// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use clean_rust_sem::{Body, Place, RustType, Rvalue, SourceProgram, Stmt};

fn lowered_main(source: &str) -> Body {
    let program = SourceProgram::parse(source).expect("source should parse");
    program
        .lower_to_vir()
        .expect("source should lower to VIR")
        .functions
        .get("main")
        .cloned()
        .expect("lowered program should contain `main`")
}

fn borrow_result_for_main(source: &str) -> clean_rust_sem::NllResult {
    let program = SourceProgram::parse(source).expect("source should parse");
    let mut analyses = program
        .check_borrows()
        .expect("source should lower and run NLL");
    analyses
        .remove("main")
        .expect("borrow analyses should contain `main`")
}

fn local_id(body: &Body, name: &str) -> u32 {
    body.locals
        .iter()
        .enumerate()
        .find_map(|(idx, decl)| (decl.name.as_deref() == Some(name)).then_some(idx as u32))
        .expect("named local should exist")
}

fn borrowed_place_for_local(body: &Body, local: u32) -> Place {
    body.blocks
        .iter()
        .flat_map(|bb| bb.statements.iter())
        .find_map(|stmt| match stmt {
            Stmt::Assign {
                place: Place::Local(temp),
                rvalue: Rvalue::Ref { place, .. },
            } if *temp == local => Some(place.clone()),
            _ => None,
        })
        .expect("borrow local should be initialized from a place borrow")
}

/// Wave 104: follow `Ref`/`Deref` indirection chains to recover the
/// *root* place that a borrow ultimately points to. Source-to-VIR
/// lowers `let rf: &u32 = &r2.value` as
///
/// ```text
/// tmp = &r2.value           // shape: Deref(Deref(Local(r2))).value
/// rf  = &*tmp               // shape: Deref(Local(tmp))
/// ```
///
/// `borrowed_place_for_local(rf)` returns the second-stage borrow
/// (`Deref(Local(tmp))`), but the structural shape the autoderef test
/// cares about lives on the *first-stage* borrow that initialised
/// `tmp`. This helper threads through any `Deref(Local(_))` borrows by
/// finding the underlying `Local(_)`'s own `Ref` source. It stops at
/// the first borrow whose inner place is not a bare `Deref(Local(_))`
/// chain.
fn root_borrow_for_local(body: &Body, local: u32) -> Place {
    let mut place = borrowed_place_for_local(body, local);
    loop {
        // Peel a `Deref(Local(inner))` indirection: rebind to inner's borrow.
        if let Place::Deref(inner) = &place {
            if let Place::Local(inner_local) = inner.as_ref() {
                // Find the assignment that initialised `inner_local`.
                if let Some(next) = body
                    .blocks
                    .iter()
                    .flat_map(|bb| bb.statements.iter())
                    .find_map(|stmt| match stmt {
                        Stmt::Assign {
                            place: Place::Local(temp),
                            rvalue: Rvalue::Ref { place, .. },
                        } if *temp == *inner_local => Some(place.clone()),
                        _ => None,
                    })
                {
                    place = next;
                    continue;
                }
            }
        }
        return place;
    }
}

#[test]
fn test_field_borrow_through_nested_shared_ref_autoderefs_to_referent() {
    let source = r#"
        struct Pair { value: u32 }

        fn main() -> u32 {
            let mut pair = Pair { value: 1u32 };
            let r1: &Pair = &pair;
            let r2: &&Pair = &r1;
            let rf: &u32 = &r2.value;
            pair.value = 2u32;
            *rf
        }
    "#;

    let body = lowered_main(source);
    let r2_local = local_id(&body, "r2");
    let rf_local = local_id(&body, "rf");
    // Wave 104: follow the borrow-chain through the intermediate temp
    // that source-to-VIR materialises for `&r2.value`. The autoderef
    // shape that this test checks lives on the *root* borrow (the one
    // that actually projects through `r2`), not on the surface-level
    // borrow that re-borrows the intermediate temp.
    let borrowed_place = root_borrow_for_local(&body, rf_local);

    assert!(
        matches!(
            &borrowed_place,
            Place::Field { base, field }
                if field == "value"
                    && matches!(
                        base.as_ref(),
                        Place::Deref(inner)
                            if matches!(
                                inner.as_ref(),
                                Place::Deref(root)
                                    if matches!(
                                        root.as_ref(),
                                        Place::Local(local) if *local == r2_local
                                    )
                            )
                    )
        ),
        "field borrow through `&&Pair` should dereference both reference layers, got {borrowed_place:?} in {body:#?}"
    );

    let result = borrow_result_for_main(source);
    assert!(
        result.errors.is_empty(),
        "projection autoderef should not introduce spurious NLL errors: {:?}",
        result.errors
    );
}

#[test]
fn test_index_borrow_through_nested_shared_ref_autoderefs_to_referent() {
    let source = r#"
        fn main() -> u32 {
            let data: [u32; 3] = [4u32, 5u32, 6u32];
            let r1: &[u32; 3] = &data;
            let r2: &&[u32; 3] = &r1;
            let rf: &u32 = &r2[1u32];
            *rf
        }
    "#;

    let body = lowered_main(source);
    let r2_local = local_id(&body, "r2");
    let rf_local = local_id(&body, "rf");
    let borrowed_place = root_borrow_for_local(&body, rf_local);

    assert!(
        matches!(
            &borrowed_place,
            Place::Index { base, .. }
                if matches!(
                    base.as_ref(),
                    Place::Deref(inner)
                        if matches!(
                            inner.as_ref(),
                            Place::Deref(root)
                                if matches!(
                                    root.as_ref(),
                                    Place::Local(local) if *local == r2_local
                                )
                        )
                )
        ),
        "index borrow through `&&[u32; 3]` should dereference both reference layers, got {borrowed_place:?} in {body:#?}"
    );

    let result = borrow_result_for_main(source);
    assert!(
        result.errors.is_empty(),
        "nested-reference index borrow should stay NLL-clean when no write occurs: {:?}",
        result.errors
    );
}

/// Wave 104 negative test: a *single* shared reference must NOT
/// produce two nested `Deref` layers. Exactly one `Deref` is correct.
/// This proves the autoderef walker is conservative — it only adds
/// layers while the place type is still a reference.
#[test]
fn test_field_borrow_through_single_shared_ref_has_exactly_one_deref() {
    let source = r#"
        struct Pair { value: u32 }

        fn main() -> u32 {
            let mut pair = Pair { value: 1u32 };
            let r1: &Pair = &pair;
            let rf: &u32 = &r1.value;
            pair.value = 2u32;
            *rf
        }
    "#;

    let body = lowered_main(source);
    let r1_local = local_id(&body, "r1");
    let rf_local = local_id(&body, "rf");
    let borrowed_place = root_borrow_for_local(&body, rf_local);

    // Expected: `Field { base: Deref(Local(r1)), field: "value" }` —
    // exactly one Deref, NOT two.
    let inner_is_local_r1 = matches!(
        &borrowed_place,
        Place::Field { base, field }
            if field == "value"
                && matches!(
                    base.as_ref(),
                    Place::Deref(inner)
                        if matches!(inner.as_ref(), Place::Local(local) if *local == r1_local)
                )
    );
    assert!(
        inner_is_local_r1,
        "single-reference field borrow must have exactly one Deref over `r1`, got {borrowed_place:?} in {body:#?}"
    );

    // And explicitly: there must NOT be a second Deref layer.
    let has_double_deref = matches!(
        &borrowed_place,
        Place::Field { base, .. }
            if matches!(
                base.as_ref(),
                Place::Deref(inner)
                    if matches!(inner.as_ref(), Place::Deref(_))
            )
    );
    assert!(
        !has_double_deref,
        "single-reference field borrow must NOT have a double Deref, got {borrowed_place:?}"
    );
}

#[test]
fn test_field_borrow_through_temporary_struct_materializes_projection_base() {
    let source = r#"
        struct Pair { value: u32 }

        fn main() -> u32 {
            let rf: &u32 = &(Pair { value: 1u32 }.value);
            *rf
        }
    "#;

    let body = lowered_main(source);
    let rf_local = local_id(&body, "rf");
    let borrowed_place = borrowed_place_for_local(&body, rf_local);
    let materialized_local = match &borrowed_place {
        Place::Field { base, field } if field == "value" => match base.as_ref() {
            Place::Local(local) => *local,
            other => {
                panic!("temporary field borrow should project from a temp local, got {other:?}")
            }
        },
        other => panic!("temporary field borrow should stay a field projection, got {other:?}"),
    };

    assert!(
        matches!(
            &body.locals[materialized_local as usize].ty,
            RustType::Named { name, .. } if name == "Pair"
        ),
        "temporary field borrow should materialize the struct base before projection: {body:#?}"
    );

    let result = borrow_result_for_main(source);
    assert!(
        result.errors.is_empty(),
        "temporary projection base materialization should stay NLL-clean: {:?}",
        result.errors
    );
}
