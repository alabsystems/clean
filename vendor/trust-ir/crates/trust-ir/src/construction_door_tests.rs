// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Plain-`Module` construction doors refuse; they never panic on a value their
//! signature admits ("A construction door refuses; it never panics on a value
//! its signature admits", `docs/SPEC_RATIFICATIONS.md`). D1a added total twins
//! beside the panicking spellings; D1b retyped the doors themselves and deleted
//! the twins, so there is one spelling of each. Test rung: evidence, never
//! proof. A table door's capacity arm (2^32 resident entries) is held by the
//! linted `impl` blocks in `lib.rs`, not by a test.

use super::*;
use std::panic::{AssertUnwindSafe, catch_unwind};

/// T5, kind (iii). `join_preds` interns the join; a DECODED predicate table
/// can hold a non-canonical node (an empty interval), and the join of that
/// node with itself is the node, which `intern_pred` cannot canonicalize.
/// Join's own fallback is toward `Top` ("every fallback is toward Top"), so
/// the merge weakens to `Top` instead of panicking on an invariant `expect`.
#[test]
fn join_preds_falls_back_to_top_and_never_panics() {
    let mut module = Module::new("decoded-predicates");
    module.predicates.push(Pred::Interval { lo: 5, hi: 3 });
    let malformed = PredId::new(0);
    let joined = catch_unwind(AssertUnwindSafe(|| {
        module.join_preds(Some(malformed), Some(malformed))
    }))
    .expect("a non-canonical node never panics the join")
    .expect("room for Top");
    assert_eq!(module.pred_table().pred(joined), Some(&Pred::Top));
}

fn struct_def(id: u32, name: &str) -> StructDef {
    StructDef {
        id: StructId::new(id),
        name: name.to_string(),
        fields: vec![FieldDef {
            name: "x".to_string(),
            ty: Ty::I64,
            offset: Some(0),
        }],
        size: Some(8),
        align: Some(8),
        repr: Default::default(),
        origin: None,
    }
}

fn enum_def(id: u32, name: &str) -> EnumDef {
    EnumDef {
        id: EnumId::new(id),
        name: name.to_string(),
        variants: vec![EnumVariant {
            name: "Only".to_string(),
            fields: vec![Ty::I64],
            field_names: Vec::new(),
        }],
        discriminants: Vec::new(),
        repr: None,
        layout: None,
        origin: None,
    }
}

/// T-B1, kind (i) half: on main before D1b, `allocate_struct_id` on a table
/// holding id `u32::MAX` panicked through `checked_add(1).expect(..)` (later
/// through the D1a twin's `panic!`). Now the door itself refuses by the one
/// fresh-id rule (`FreshIds::after`), and a colliding `add_*_def` leaves the
/// table unchanged. Mutation check: restoring the `expect` turns the
/// `catch_unwind` red; allocating `max + 1` by hand wraps, and the `Err`
/// assertions go red.
#[test]
fn the_struct_and_enum_allocators_refuse_never_panic() {
    let mut module = Module::new("decoded-defs");
    module.add_struct(struct_def(u32::MAX, "Max"));
    module.add_enum(enum_def(u32::MAX, "Max"));
    let struct_id = catch_unwind(AssertUnwindSafe(|| module.allocate_struct_id()))
        .expect("the struct allocator never panics");
    assert_eq!(struct_id, Err(IdSpaceExhausted::of::<StructId>()));
    let enum_id = catch_unwind(AssertUnwindSafe(|| module.allocate_enum_id()))
        .expect("the enum allocator never panics");
    assert_eq!(enum_id, Err(IdSpaceExhausted::of::<EnumId>()));
    let structs = module.structs.clone();
    let enums = module.enums.clone();
    // Same id, different content: step 3 needs a fresh id, and none exists.
    assert_eq!(
        module.add_struct_def(struct_def(u32::MAX, "Other")),
        Err(IdSpaceExhausted::of::<StructId>())
    );
    assert_eq!(
        module.add_enum_def(enum_def(u32::MAX, "Other")),
        Err(IdSpaceExhausted::of::<EnumId>())
    );
    assert_eq!(module.structs, structs, "the struct table is unchanged");
    assert_eq!(module.enums, enums, "the enum table is unchanged");
    // A structural duplicate needs no id and still dedups.
    assert_eq!(
        module.add_struct_def(struct_def(0, "Max")),
        Ok(StructId::new(u32::MAX))
    );
    assert_eq!(
        module.add_enum_def(enum_def(0, "Max")),
        Ok(EnumId::new(u32::MAX))
    );

    // Control: one past the HIGHEST id, sparse ids skipped, as before.
    let mut sparse = Module::new("sparse");
    sparse.add_struct(struct_def(3, "A"));
    sparse.add_struct(struct_def(7, "B"));
    assert_eq!(sparse.allocate_struct_id(), Ok(StructId::new(8)));
    assert_eq!(
        sparse.add_struct_def(struct_def(7, "C")),
        Ok(StructId::new(8))
    );
}

/// Kind (iii): the join's other arms are unchanged — a carried fact joined
/// with nothing is `Top`, a fact joined with itself is that fact, and two
/// intervals join to their hull. (Capacity cannot be reached without 2^32
/// resident predicates; the refusal is `intern_canonical_pred` over
/// `value::table_id`, held by the linted door block.)
#[test]
fn join_preds_keeps_its_lattice_arms() {
    let mut module = Module::new("joins");
    let interval = module
        .intern_pred(Pred::Interval { lo: 0, hi: 9 })
        .expect("room")
        .expect("canonical");
    let top = module.join_preds(Some(interval), None).expect("room");
    assert_eq!(module.pred_table().pred(top), Some(&Pred::Top));
    assert_eq!(
        module.join_preds(Some(interval), Some(interval)),
        Ok(interval)
    );
    let wider = module
        .intern_pred(Pred::Interval { lo: 5, hi: 20 })
        .expect("room")
        .expect("canonical");
    let joined = module
        .join_preds(Some(interval), Some(wider))
        .expect("room");
    assert_eq!(
        module.pred_table().pred(joined),
        Some(&Pred::Interval { lo: 0, hi: 20 })
    );
}

/// Kind (iii): the interning doors' `Option` keeps exactly one meaning, "not
/// canonicalizable"; a new row takes the next positional id and an equal row
/// returns the existing one (idempotent), through the exact enumeration
/// rather than a truncating index cast.
#[test]
fn interning_doors_return_the_existing_id_or_the_next_slot() {
    let mut module = Module::new("interning");
    assert_eq!(module.intern_file("a.rs"), Ok(0));
    assert_eq!(module.intern_file("b.rs"), Ok(1));
    assert_eq!(module.intern_file("a.rs"), Ok(0));
    assert_eq!(module.files.len(), 2);

    let unit = FuncTy::unrecorded(vec![], vec![], false);
    let first = module.intern_func_type(unit.clone()).expect("room");
    assert_eq!(module.intern_func_type(unit), Ok(first));
    assert_eq!(module.func_types.len(), 1);

    let range = module
        .intern_universe(Universe::IntRange { lo: 0, hi: 3 })
        .expect("room")
        .expect("canonical");
    assert_eq!(
        module.intern_universe(Universe::IntRange { lo: 0, hi: 3 }),
        Ok(Some(range))
    );
    // Not canonicalizable: `Ok(None)`, and nothing is pushed.
    let universes = module.universes.len();
    assert_eq!(
        module.intern_universe(Universe::Members(Vec::new())),
        Ok(None)
    );
    assert_eq!(module.universes.len(), universes);
    assert_eq!(
        module.intern_pred(Pred::Interval { lo: 5, hi: 3 }),
        Ok(None),
        "an empty interval has no canonical spelling"
    );

    assert_eq!(module.add_type(Ty::I8), Ok(TyId::new(0)));
    assert_eq!(
        module.add_type(Ty::I8),
        Ok(TyId::new(1)),
        "add_type appends"
    );
}
