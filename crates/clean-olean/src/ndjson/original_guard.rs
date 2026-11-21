//! Check the four original arithmetic guards of ordinary Rust r01 against the
//! input bytes supplied by the compiler. The export is an untrusted proof producer.
//! The fixed identities below name Lean predicates over *any* wire. Each digest
//! covers the predicate and all kernel records in its dependency closure.
//! No compiler-capture digest or previously accepted verdict is an input.

use clean_kernel::{Expr, Level, Name, ReferenceKernel};

use super::{LEAN_FOUNDATIONAL_AXIOMS, reference_kernel_from_export};

const MODEL: [(&str, &str, &str); 4] = [
    (
        "RungCheckedModel.row0",
        "RungFirstGuard.original_word_entry",
        "22350133ed9cb8dfea1b685d42b8824002918fb70aaa807237ac95ea3e1c6987",
    ),
    (
        "RungCheckedModel.row3",
        "RungShiftGuards.original_left_shift",
        "97c7b3ec83f50a218daee7b55e9cf2292cedb66847663812aa9aca552f99ebdd",
    ),
    (
        "RungCheckedModel.row4",
        "RungShiftGuards.original_right_shift",
        "9c91f29efc777027d8b6cd3ca8f38b0dbd3bda123bcb8844caa3fc1712e0e639",
    ),
    (
        "RungCheckedModel.row6",
        "RungFinalAdd.original_final_add",
        "2f814a2ea3dc8cb4bc45042162fb44b08dee573b14ddd01396205d8c3f730e6a",
    ),
];

// Bind the foundational axioms allowed in proofs and the operations introduced
// by the shell itself. The four predicates also reach Nat and the List family.
const SUPPORT: [(&str, &str); 5] = [
    (
        "propext",
        "6d10bb454401db142418709af2d6ca39c6eb95ea71c37d0157889ee5cd0b5902",
    ),
    (
        "Classical.choice",
        "714d6167b62644086d122495b4efce56a186e576dd3493b7142221c40f646740",
    ),
    (
        "Quot.sound",
        "2fd450264087430f79b17b3a845cffbd623650a6d2ef05cb2114d56097fb7113",
    ),
    (
        "Eq.refl",
        "0cd9e6b9d690b7d912262600fd24a5f707c1f61ff7bdc288f8bf5bfcd5ca4353",
    ),
    (
        "List.append",
        "5b8664e6823402a72852e4772519ebe796a8ce2a5b5eaef0ce9bc98d639979a1",
    ),
];

fn constant(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

fn nat_list(name: &str) -> Expr {
    Expr::app(
        Expr::const_(Name::from_string(name), vec![Level::zero()]),
        constant("Nat"),
    )
}

fn quote_wire(bytes: &[u8]) -> Expr {
    let nil = nat_list("List.nil");
    let cons = nat_list("List.cons");
    let append = nat_list("List.append");
    // The chunked quotation keeps the syntax depth bounded. All reductions
    // use the authenticated Lean list operations and the original byte order.
    let mut chunks: Vec<_> = bytes
        .chunks(32)
        .map(|chunk| {
            chunk.iter().rev().fold(nil.clone(), |tail, &byte| {
                Expr::apps(cons.clone(), [Expr::nat_lit(u64::from(byte)), tail])
            })
        })
        .collect();
    while chunks.len() > 1 {
        chunks = chunks
            .chunks(2)
            .map(|pair| match pair {
                [left, right] => Expr::apps(append.clone(), [left.clone(), right.clone()]),
                _ => pair[0].clone(),
            })
            .collect();
    }
    chunks.pop().unwrap_or(nil)
}

fn authenticate(kernel: &ReferenceKernel, name: &str, expected: &str) -> Result<(), String> {
    let digest = kernel
        .environment()
        .closure_digest(&Name::from_string(name))
        .map_err(|err| format!("cannot bind {name}: {err}"))?;
    let actual: String = digest.iter().map(|byte| format!("{byte:02x}")).collect();
    if actual != expected {
        return Err(format!("different Lean model at {name}"));
    }
    Ok(())
}

fn check(source: &[u8], export: &[u8]) -> Result<(), String> {
    let (kernel, report) = reference_kernel_from_export(export, &LEAN_FOUNDATIONAL_AXIOMS)
        .map_err(|report| {
            format!(
                "reference checker declined original guard export: {:?}",
                report.refusals.first()
            )
        })?;
    if !report.meta.as_ref().is_some_and(|m| {
        m.lean_githash == "3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc"
            && m.lean_version == "4.30.0-rc2"
            && m.exporter_name == "lean4export"
            && m.exporter_version == "3.1.0"
            && m.format_version == "3.1.0"
    }) {
        return Err("unexpected original guard export world".into());
    }
    for (name, digest) in SUPPORT {
        authenticate(&kernel, name, digest)?;
    }
    for (predicate, _, digest) in MODEL {
        authenticate(&kernel, predicate, digest)?;
    }
    let wire = quote_wire(source);
    let list_nat = nat_list("List");
    let eq = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
    let refl = Expr::const_(
        Name::from_string("Eq.refl"),
        vec![Level::succ(Level::zero())],
    );
    let identity = Expr::apps(refl, [list_nat.clone(), wire.clone()]);
    let exact_wire = Expr::apps(eq, [list_nat, constant("OriginalWire.wire"), wire.clone()]);
    // A type mismatch can include both entire byte lists. Keep the refusal
    // attached to the failed claim without rendering its quoted operands.
    kernel
        .check_closed_term(&exact_wire, &identity)
        .map_err(|_| "original wire differs from compiler input".to_string())?;
    for (predicate, theorem, _) in MODEL {
        let goal = Expr::app(constant(predicate), wire.clone());
        kernel
            .check_closed_term(&goal, &constant(theorem))
            .map_err(|_| format!("original guard {theorem} does not prove its source predicate"))?;
    }
    Ok(())
}

/// Recheck the original division, both shifts, and final-add theorems on the
/// compiler's complete original wire. TrustIR separately binds their four
/// source rows and validates the resulting certificates.
///
/// # Errors
///
/// Refuses oversized inputs, an unaccepted export or different model, a
/// mismatched wire, and any theorem that does not prove its own concrete goal.
pub fn check_trust_ir_r01_source_model(source: &[u8], export: &[u8]) -> Result<(), String> {
    if source.is_empty() || source.len() > 16 * 1024 || export.is_empty() || export.len() > 28 << 20
    {
        return Err("incorrect original guard input size".into());
    }
    std::thread::scope(|scope| {
        std::thread::Builder::new()
            .name("r01-clean-source-model".into())
            .stack_size(512 << 20)
            .spawn_scoped(scope, || check(source, export))
            .map_err(|err| format!("cannot start original guard checker: {err}"))?
            .join()
            .map_err(|_| "original guard checker panicked".to_string())?
    })
}

#[cfg(test)]
mod tests {
    use super::check_trust_ir_r01_source_model;

    #[test]
    fn rejects_out_of_range_inputs_before_reading_the_export() {
        let source = vec![0; 16 * 1024 + 1];
        let export = vec![0; (28 << 20) + 1];
        for (wire, proof) in [
            (&[][..], &[0][..]),
            (&[0][..], &[][..]),
            (source.as_slice(), &[0][..]),
            (&[0][..], export.as_slice()),
        ] {
            assert_eq!(
                check_trust_ir_r01_source_model(wire, proof).unwrap_err(),
                "incorrect original guard input size"
            );
        }
    }
}
