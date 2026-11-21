// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
//! Independently expected byte data and CIC-checked producer quotation advice.
//!
//! The expected slice belongs to the subject owner. Content hashes choose names
//! only. Every supplied declaration, byte chunk, suffix link, terminal and full
//! root equation is checked by the original reference entry. No declaration
//! shape or expression walk substitutes for those judgments.

use super::{c, BoolBodyRefusal, BoolQuotationProposal};
use clean_kernel::{Declaration, Expr, Level, Name, ReferenceKernel};
use std::collections::BTreeSet;

const CHUNK_BYTES: usize = 256;
const BOUND_BYTES: &str = "SemR.DecodeCertificate.BoundBytes";

pub(super) struct ByteQuote {
    pub(super) concrete: Expr,
    pub(super) producer: Expr,
    pub(super) equation: Expr,
    pub(super) input: Expr,
    pub(super) nominal: Expr,
}

pub(super) struct ByteQuotePlan<'a> {
    bytes: &'a [u8],
    proposal: &'a BoolQuotationProposal,
    suffixes: Vec<Name>,
    chunk_exact: Vec<Name>,
    suffix_exact: Vec<Name>,
    root_exact: Name,
    bound: Name,
    all_names: Vec<Name>,
}

fn list_nat() -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("List"), vec![Level::zero()]),
        c("Nat"),
    )
}

fn nil_nat() -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("List.nil"), vec![Level::zero()]),
        c("Nat"),
    )
}

fn named(name: &Name) -> Expr {
    Expr::const_(name.clone(), vec![])
}

pub(super) fn append(left: Expr, right: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("List.append"), vec![Level::zero()]),
        [c("Nat"), left, right],
    )
}

fn flat(bytes: &[u8]) -> Expr {
    super::list(
        c("Nat"),
        bytes
            .iter()
            .map(|byte| Expr::nat_lit(u64::from(*byte)))
            .collect(),
    )
}

fn equation(left: Expr, right: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [list_nat(), left, right],
    )
}

fn reflexivity(value: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        ),
        [list_nat(), value],
    )
}

fn declaration_name(declaration: &Declaration) -> &Name {
    match declaration {
        Declaration::Definition { name, .. }
        | Declaration::Theorem { name, .. }
        | Declaration::Opaque { name, .. }
        | Declaration::Axiom { name, .. } => name,
    }
}

fn admit_definition(
    kernel: &mut ReferenceKernel,
    name: Name,
    value: Expr,
) -> Result<(), BoolBodyRefusal> {
    kernel
        .add_checked(Declaration::Definition {
            name,
            level_params: vec![],
            type_: list_nat(),
            value,
            is_reducible: true,
        })
        .map(|_| ())
        .map_err(BoolBodyRefusal::Quotation)
}

fn admit_equation(
    kernel: &mut ReferenceKernel,
    name: Name,
    left: Expr,
    right: Expr,
    proof: Expr,
) -> Result<(), BoolBodyRefusal> {
    kernel
        .add_checked(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: equation(left, right),
            value: proof,
        })
        .map(|_| ())
        .map_err(BoolBodyRefusal::Quotation)
}

impl<'a> ByteQuotePlan<'a> {
    pub(super) fn new(
        bytes: &'a [u8],
        proposal: &'a BoolQuotationProposal,
    ) -> Result<Self, BoolBodyRefusal> {
        let chunks = bytes.len().div_ceil(CHUNK_BYTES);
        if proposal.chunks.len() != chunks || proposal.suffixes.len() != chunks + 1 {
            return Err(BoolBodyRefusal::QuotationShape(format!(
                "{} expected chunks and {} suffixes, supplied {} chunks and {} suffixes",
                chunks,
                chunks + 1,
                proposal.chunks.len(),
                proposal.suffixes.len(),
            )));
        }
        let prefix = format!(
            "TrustCheckedBytes.v1.h{}.n{}",
            blake3::hash(bytes).to_hex(),
            bytes.len(),
        );
        let suffixes: Vec<_> = (0..=chunks)
            .map(|index| Name::from_string(&format!("{prefix}.suffix_{index}")))
            .collect();
        let chunk_exact: Vec<_> = (0..chunks)
            .map(|index| Name::from_string(&format!("{prefix}.chunk_exact_{index}")))
            .collect();
        let suffix_exact: Vec<_> = (0..=chunks)
            .map(|index| Name::from_string(&format!("{prefix}.suffix_exact_{index}")))
            .collect();
        let root_exact = Name::from_string(&format!("{prefix}.root_exact"));
        let bound = Name::from_string(&format!("{prefix}.input"));
        let all_names = suffixes
            .iter()
            .chain(&chunk_exact)
            .chain(&suffix_exact)
            .chain(std::iter::once(&root_exact))
            .chain(std::iter::once(&bound))
            .cloned()
            .chain(proposal.declarations.iter().map(declaration_name).cloned())
            .collect();
        Ok(Self {
            bytes,
            proposal,
            suffixes,
            chunk_exact,
            suffix_exact,
            root_exact,
            bound,
            all_names,
        })
    }

    /// Includes every expected-data, proof, opaque-input and advice declaration.
    /// The parent must also compare this inventory across the complete batch.
    pub(super) fn names(&self) -> impl Iterator<Item = &Name> {
        self.all_names.iter()
    }

    /// No existing or repeated name can be adopted, including advice names.
    /// Complete preflight precedes the first reference admission.
    pub(super) fn preflight(&self, kernel: &ReferenceKernel) -> Result<(), BoolBodyRefusal> {
        let mut seen = BTreeSet::new();
        let env = kernel.environment();
        for name in self.names() {
            if !seen.insert(name)
                || env.get_const(name).is_some()
                || env.get_inductive(name).is_some()
                || env.get_constructor(name).is_some()
                || env.get_recursor(name).is_some()
                || env.get_quot(name).is_some()
            {
                return Err(BoolBodyRefusal::QuotationNameCollision(name.to_string()));
            }
        }
        Ok(())
    }

    pub(super) fn admit(self, kernel: &mut ReferenceKernel) -> Result<ByteQuote, BoolBodyRefusal> {
        self.preflight(kernel)?;
        let chunks = self.chunk_exact.len();

        // Preserve the reader's original literal-prefix encoding. Its suffix
        // definitions do not use the producer's chunks or append expression.
        admit_definition(kernel, self.suffixes[chunks].clone(), nil_nat())?;
        for index in (0..chunks).rev() {
            let start = index * CHUNK_BYTES;
            let end = start.saturating_add(CHUNK_BYTES).min(self.bytes.len());
            let mut value = named(&self.suffixes[index + 1]);
            for &byte in self.bytes[start..end].iter().rev() {
                value = Expr::apps(
                    Expr::const_(Name::from_string("List.cons"), vec![Level::zero()]),
                    [c("Nat"), Expr::nat_lit(u64::from(byte)), value],
                );
            }
            admit_definition(kernel, self.suffixes[index].clone(), value)?;
        }

        // Supplied declaration order, values, types and references are advice.
        // Ax0 and every ordinary typing judgment remain the reference entry's.
        for declaration in &self.proposal.declarations {
            kernel
                .add_checked(declaration.clone())
                .map_err(BoolBodyRefusal::Quotation)?;
        }

        for index in 0..chunks {
            let start = index * CHUNK_BYTES;
            let end = start.saturating_add(CHUNK_BYTES).min(self.bytes.len());
            let expected = flat(&self.bytes[start..end]);
            admit_equation(
                kernel,
                self.chunk_exact[index].clone(),
                self.proposal.chunks[index].clone(),
                expected.clone(),
                reflexivity(expected),
            )?;
        }
        admit_equation(
            kernel,
            self.suffix_exact[chunks].clone(),
            self.proposal.suffixes[chunks].clone(),
            named(&self.suffixes[chunks]),
            reflexivity(nil_nat()),
        )?;
        for index in (0..chunks).rev() {
            let start = index * CHUNK_BYTES;
            let end = start.saturating_add(CHUNK_BYTES).min(self.bytes.len());
            let actual = self.proposal.suffixes[index].clone();
            let head = self.proposal.chunks[index].clone();
            let tail = self.proposal.suffixes[index + 1].clone();
            let expected_head = flat(&self.bytes[start..end]);
            let expected_tail = named(&self.suffixes[index + 1]);
            let expected = named(&self.suffixes[index]);
            let proof = Expr::apps(
                c("SemR.DecodeCertificate.suffix_exact"),
                [
                    actual.clone(),
                    head.clone(),
                    tail.clone(),
                    expected_head,
                    expected_tail,
                    expected.clone(),
                    reflexivity(append(head, tail)),
                    named(&self.chunk_exact[index]),
                    named(&self.suffix_exact[index + 1]),
                    reflexivity(expected.clone()),
                ],
            );
            admit_equation(
                kernel,
                self.suffix_exact[index].clone(),
                actual,
                expected,
                proof,
            )?;
        }

        let concrete = named(&self.suffixes[0]);
        let producer = self.proposal.bytes.clone();
        let chain = self.proposal.suffixes[0].clone();
        let proof = Expr::apps(
            c("SemR.DecodeCertificate.trans_exact"),
            [
                producer.clone(),
                chain.clone(),
                concrete.clone(),
                reflexivity(chain),
                named(&self.suffix_exact[0]),
            ],
        );
        admit_equation(
            kernel,
            self.root_exact.clone(),
            producer.clone(),
            concrete.clone(),
            proof,
        )?;

        kernel
            .add_checked(Declaration::Opaque {
                name: self.bound.clone(),
                level_params: vec![],
                type_: Expr::app(c(BOUND_BYTES), concrete.clone()),
                value: Expr::apps(
                    c("SemR.DecodeCertificate.BoundBytes.mk"),
                    [
                        concrete.clone(),
                        concrete.clone(),
                        reflexivity(concrete.clone()),
                    ],
                ),
            })
            .map_err(BoolBodyRefusal::Quotation)?;
        let input = named(&self.bound);
        Ok(ByteQuote {
            concrete,
            producer,
            equation: named(&self.root_exact),
            nominal: Expr::proj(Name::from_string(BOUND_BYTES), 0, input.clone()),
            input,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::{Environment, KernelEnvError, KernelTypeError, ReferenceRefusal};
    use std::process::Command;

    fn byte_reference() -> ReferenceKernel {
        let lean = crate::pinned_lean_binary().expect("explicit pinned Lean fixture is required");
        let lib = crate::pinned_lean_lib_path().expect("explicit pinned Lean fixture is required");
        let source = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("tests/fixtures/lean/v4.30.0-rc2/semr");
        let output = tempfile::tempdir().expect("own byte-binding fixture directory");
        for module in ["SemR", "SemRByteBinding"] {
            let name = format!("{module}.lean");
            std::fs::copy(source.join(&name), output.path().join(&name))
                .expect("copy original model and model-neutral byte binding");
            let result = Command::new(&lean)
                .current_dir(output.path())
                .env("LEAN_PATH", output.path())
                .args([
                    "--threads=1",
                    "--root",
                    ".",
                    "-o",
                    &format!("{module}.olean"),
                    &name,
                ])
                .output()
                .expect("run pinned genuine Lean on fixture source");
            assert!(
                result.status.success(),
                "genuine Lean refused {module}: {}{}",
                String::from_utf8_lossy(&result.stdout),
                String::from_utf8_lossy(&result.stderr)
            );
        }
        let mut env = Environment::for_lean_replay();
        crate::load_module_with_deps(
            &mut env,
            "SemRByteBinding",
            &[output.path().to_path_buf(), lib],
        )
        .expect("load genuine source declarations and opaque bodies");
        let roots: BTreeSet<_> = [
            BOUND_BYTES,
            "SemR.DecodeCertificate.from_bound",
            "SemR.DecodeCertificate.to_bound",
            "SemR.DecodeCertificate.suffix_exact",
            "SemR.DecodeCertificate.trans_exact",
            "SemR.DecodeCertificate.to_bound_from",
            "List.append",
        ]
        .into_iter()
        .map(Name::from_string)
        .collect();
        crate::reference_base_closed(&env, &roots, &crate::ClosedRecheckOptions::default())
            .expect("original reference entry")
            .into_kernel()
            .expect("genuinely completed byte-binding replay")
    }

    // An independently append-based untrusted proposal, matching the external
    // producer protocol. The reader never receives a producer encoding helper.
    fn append_proposal(bytes: &[u8]) -> BoolQuotationProposal {
        let prefix = format!(
            "AdviceByteTest.h{}.n{}",
            blake3::hash(bytes).to_hex(),
            bytes.len()
        );
        let chunk_names: Vec<_> = bytes
            .chunks(CHUNK_BYTES)
            .enumerate()
            .map(|(i, _)| Name::from_string(&format!("{prefix}.chunk_{i}")))
            .collect();
        let suffix_names: Vec<_> = (0..=chunk_names.len())
            .map(|i| Name::from_string(&format!("{prefix}.suffix_{i}")))
            .collect();
        let chunks: Vec<_> = chunk_names.iter().map(named).collect();
        let suffixes: Vec<_> = suffix_names.iter().map(named).collect();
        let mut declarations = Vec::new();
        let mut push = |name, value| {
            declarations.push(Declaration::Definition {
                name,
                level_params: vec![],
                type_: list_nat(),
                value,
                is_reducible: true,
            })
        };
        for (name, chunk) in chunk_names.iter().zip(bytes.chunks(CHUNK_BYTES)) {
            let value = chunk.iter().rfold(nil_nat(), |tail, byte| {
                Expr::apps(
                    Expr::const_(Name::from_string("List.cons"), vec![Level::zero()]),
                    [c("Nat"), Expr::nat_lit(u64::from(*byte)), tail],
                )
            });
            push(name.clone(), value);
        }
        push(suffix_names[chunk_names.len()].clone(), nil_nat());
        for i in (0..chunk_names.len()).rev() {
            push(
                suffix_names[i].clone(),
                append(chunks[i].clone(), suffixes[i + 1].clone()),
            );
        }
        BoolQuotationProposal {
            bytes: suffixes[0].clone(),
            declarations,
            chunks,
            suffixes,
        }
    }

    fn type_mismatch<T>(result: Result<T, ReferenceRefusal>) -> bool {
        matches!(
            result,
            Err(ReferenceRefusal::Kernel(KernelEnvError::TypeCheckFailed {
                source: KernelTypeError::TypeMismatch { .. },
                ..
            }))
        )
    }

    #[test]
    fn independent_append_chunks_preserve_boundaries_full_bytes_and_opaque_equation() {
        let mut kernel = byte_reference();
        for len in [0, 1, 255, 256, 257, 513] {
            let bytes: Vec<u8> = (0..len).map(|i| (i % 251) as u8).collect();
            let advice = append_proposal(&bytes);
            let plan = ByteQuotePlan::new(&bytes, &advice).expect("exact advice cardinalities");
            let before = kernel.env_digest();
            let quote = plan
                .admit(&mut kernel)
                .expect("checked independent encodings");
            assert_ne!(
                before,
                kernel.env_digest(),
                "actual extended context must be re-keyed"
            );
            kernel
                .check_closed_term(
                    &equation(quote.producer.clone(), quote.concrete.clone()),
                    &quote.equation,
                )
                .expect("complete producer/reader equation is an admitted theorem");
            let proof = reflexivity(quote.concrete.clone());
            kernel
                .check_closed_term(&equation(quote.concrete.clone(), flat(&bytes)), &proof)
                .expect("full independently flattened bytes, in order and exact length");
            if len == 513 {
                let mut swapped = bytes.clone();
                swapped.swap(255, 256);
                let truncated = bytes[..512].to_vec();
                let mut extended = bytes.clone();
                extended.push(0);
                for wrong in [swapped, truncated, extended] {
                    assert!(type_mismatch(kernel.check_closed_term(
                        &equation(quote.concrete.clone(), flat(&wrong)),
                        &proof,
                    )));
                }
            }
            kernel
                .check_closed_term(
                    &equation(quote.nominal, quote.concrete),
                    &Expr::proj(Name::from_string(BOUND_BYTES), 1, quote.input),
                )
                .expect("opaque equation has a checked constructor body");
            assert!(matches!(
                ByteQuotePlan::new(&bytes, &advice)
                    .unwrap()
                    .preflight(&kernel),
                Err(BoolBodyRefusal::QuotationNameCollision(_))
            ));
        }
    }

    #[test]
    fn malformed_chunk_order_length_terminal_link_and_returned_root_reach_cic() {
        let mut kernel = byte_reference();
        for mode in 0..5 {
            // Separate raw subjects avoid adopting declarations admitted before
            // a preceding refusal; the failed plan itself is never reused.
            let bytes: Vec<u8> = (0..513).map(|i| ((i + mode) % 251) as u8).collect();
            let mut advice = append_proposal(&bytes);
            match mode {
                0 => advice.chunks.swap(0, 1),
                1 => {
                    // Correct cardinality, but the final literal is truncated.
                    if let Declaration::Definition { value, .. } = &mut advice.declarations[2] {
                        *value = nil_nat();
                    }
                }
                2 => advice.suffixes[3] = advice.chunks[2].clone(),
                3 => {
                    // A well-typed suffix skips the middle chunk.
                    let wrong = append(advice.chunks[0].clone(), advice.suffixes[2].clone());
                    if let Declaration::Definition { value, .. } =
                        advice.declarations.last_mut().unwrap()
                    {
                        *value = wrong;
                    }
                }
                _ => advice.bytes = advice.suffixes[1].clone(),
            }
            let refusal = ByteQuotePlan::new(&bytes, &advice)
                .unwrap()
                .admit(&mut kernel);
            assert!(
                matches!(
                    refusal,
                    Err(BoolBodyRefusal::Quotation(ReferenceRefusal::Kernel(
                        KernelEnvError::TypeCheckFailed {
                            source: KernelTypeError::TypeMismatch { .. },
                            ..
                        }
                    )))
                ),
                "mode {mode} must reach genuine reference type mismatch"
            );
        }
    }

    #[test]
    fn malformed_shape_and_every_own_or_supplied_name_refuse_before_mutation() {
        let mut kernel = byte_reference();
        let bytes = [9, 8, 7];
        let mut advice = append_proposal(&bytes);
        advice.suffixes.pop();
        let before = kernel.env_digest();
        assert!(matches!(
            ByteQuotePlan::new(&bytes, &advice),
            Err(BoolBodyRefusal::QuotationShape(_))
        ));
        assert_eq!(before, kernel.env_digest());

        let advice = append_proposal(&bytes);
        let plan = ByteQuotePlan::new(&bytes, &advice).unwrap();
        let own_name = plan.names().next().unwrap().clone();
        admit_definition(&mut kernel, own_name, flat(&[0])).unwrap();
        let planted = kernel.env_digest();
        assert!(matches!(
            plan.admit(&mut kernel),
            Err(BoolBodyRefusal::QuotationNameCollision(_))
        ));
        assert_eq!(planted, kernel.env_digest());

        let other = [6, 5, 4];
        let advice = append_proposal(&other);
        let supplied = declaration_name(&advice.declarations[0]).clone();
        admit_definition(&mut kernel, supplied, flat(&[0])).unwrap();
        let planted = kernel.env_digest();
        assert!(matches!(
            ByteQuotePlan::new(&other, &advice)
                .unwrap()
                .admit(&mut kernel),
            Err(BoolBodyRefusal::QuotationNameCollision(_))
        ));
        assert_eq!(planted, kernel.env_digest());

        let other = [3, 2, 1];
        let mut advice = append_proposal(&other);
        advice.declarations.push(advice.declarations[0].clone());
        let before = kernel.env_digest();
        assert!(matches!(
            ByteQuotePlan::new(&other, &advice)
                .unwrap()
                .admit(&mut kernel),
            Err(BoolBodyRefusal::QuotationNameCollision(_))
        ));
        assert_eq!(before, kernel.env_digest());
    }
}
