// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0
//
// B3's second reader (D-2(b)): rustc's OWN discriminant assignment and
// discriminant type for each fieldless enum of `fieldless.rs`, printed by a
// program the same compiler builds without Trust. `b3_rustc.tsv` is its
// output:
//
//   rustc -Ztrust-verify=off -o b3probe b3probe.rs && ./b3probe > b3_rustc.tsv
#![feature(discriminant_kind)]
#![allow(dead_code)]
#[path = "fieldless.rs"]
mod subject;
use subject::*;
fn name<T: core::marker::DiscriminantKind>() -> &'static str {
    core::any::type_name::<<T as core::marker::DiscriminantKind>::Discriminant>()
}
fn main() {
    // `<enum name>\t<rustc's discriminant type>\t<discriminants in declaration order>`
    println!(
        "ContainmentMode\t{}\t{:?}",
        name::<ContainmentMode>(),
        [
            ContainmentMode::Containment as i128,
            ContainmentMode::Safety as i128,
            ContainmentMode::User as i128
        ]
    );
    println!(
        "Ordering3\t{}\t{:?}",
        name::<Ordering3>(),
        [
            Ordering3::Less as i128,
            Ordering3::Equal as i128,
            Ordering3::Greater as i128
        ]
    );
    println!(
        "Implicit\t{}\t{:?}",
        name::<Implicit>(),
        [
            Implicit::A as i128,
            Implicit::B as i128,
            Implicit::C as i128
        ]
    );
    println!(
        "Sparse\t{}\t{:?}",
        name::<Sparse>(),
        [Sparse::A as i128, Sparse::B as i128]
    );
    println!(
        "FpCategory\t{}\t{:?}",
        name::<FpCategory>(),
        [
            FpCategory::Nan as i128,
            FpCategory::Infinite as i128,
            FpCategory::Zero as i128,
            FpCategory::Subnormal as i128,
            FpCategory::Normal as i128
        ]
    );
    println!(
        "AtomicOrdering\t{}\t{:?}",
        name::<AtomicOrdering>(),
        [
            AtomicOrdering::Relaxed as i128,
            AtomicOrdering::Release as i128,
            AtomicOrdering::Acquire as i128,
            AtomicOrdering::AcqRel as i128,
            AtomicOrdering::SeqCst as i128
        ]
    );
}
