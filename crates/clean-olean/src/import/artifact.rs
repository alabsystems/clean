// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The one reader of a multi-part `.olean` artifact for every re-check lane
//! (docs/DECISIONS.md R113).
//!
//! An artifact is a module's `.olean` and, when present, its `.olean.server`
//! and `.olean.private`. What pinned Lean (v4.30.0-rc2) reads of it:
//!
//! * an importer — `lean` on a file that imports it, and `leanchecker
//!   --fresh` — reads it through `ImportedModule.mainModule?`
//!   (`Environment.lean`): the `.olean.private` of a module-system artifact
//!   (its `.olean` says `isModule`) when the importer is not itself a `module`
//!   or imports it with `import all` (`leanchecker` imports every module that
//!   way: `globalLevel == .private`), and the `.olean` of any other artifact;
//!   it follows the imports of the same part (`goRec` over `mainModule?`);
//! * `leanchecker`'s default mode replays the LAST part it found
//!   (`replayFromImports`: the `.olean.private`, or the `.olean.server` when
//!   there is no private part), with no `isModule` check, and takes the
//!   checked module's imports from its `.olean`.
//!
//! Lean's `writeModule` makes every one of those readings the same module: each
//! part states one header, the exported and server levels hold a subset of the
//! private level's constants, and a name two parts hold is one record — or, in
//! a module-system artifact, an exported `axiom` stub of the private part's
//! value (`Lean.addDecl` exports every public theorem that way). It writes no
//! companion for a non-module artifact, which every importer reads through its
//! `.olean` alone. `PartSubset.lean` beside the `replay_forged` fixtures
//! re-derives that over a toolchain's `lib/lean` (v4.30.0-rc2: 2,302 artifacts,
//! 0 violations). [`check_artifact_parts`] is that rule, fail-closed: an
//! artifact that breaks it is refused, never read through whichever part a lane
//! happens to prefer. A part only restates another, or completes a
//! module-system artifact's stub with the value the authoritative part holds;
//! a non-module artifact's companion may only restate its `.olean` (R131: a
//! companion that completed the `.olean`'s stub gave the loader a definition
//! every importer reads as an axiom, and `leanchecker`'s default mode, which
//! replays the last part, a value the `.olean` stubs). Over an artifact the
//! rule admits, every reading above agrees, so the module is its AUTHORITATIVE
//! part — `.olean.private` for a module-system artifact, `.olean` otherwise —
//! and [`read_artifact`] returns that part's imports and names.
//!
//! The `.olean` loader (`load_artifact_parts`) runs the same rule before it
//! registers anything; the mathverse bridge, `per-constant-verify`'s index and
//! demand walk, and the import-closure walks (the `--incremental` cache key,
//! `verify-batch`'s order) read through [`read_artifact`].
//!
//! Where `leanchecker`'s default mode would accept an artifact Clean refuses —
//! a non-module artifact whose companions hold a complete, well-typed set its
//! `.olean` lacks, or complete its `.olean`'s stub with a well-typed value
//! (`ReplayStubPlainDep`) — the refusal is stricter than Lean, which is the
//! safe direction: `writeModule` never writes such an artifact.

use std::collections::BTreeMap;
use std::path::Path;

use super::load_parse::{
    parse_header_module, parse_header_module_incremental, parse_load_module,
    parse_load_module_incremental, LoadConstant, LoadModule,
};
use super::module_cache_direct::read_optional;
use super::{ExprInternCache, ImportError};
use crate::module::OLeanLevel;
use crate::module::ParsedImport;
use crate::ConstantKind;
use clean_kernel::env::ProofValueElision;
use clean_kernel::name::Name;

mod inventory;
pub use inventory::{
    ArtifactDeclaration, ArtifactDeclarationOrigin, ArtifactInventory, ArtifactInventoryError,
    ArtifactInventoryLimits,
};

/// How much of an artifact a reader needs.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum ArtifactDepth {
    /// Each part's header and declared names: the rule's header and placement
    /// halves. An index or an import walk needs no more.
    Names,
    /// Every record too: the rule's value half as well. A reader that uses a
    /// module's records needs this.
    Records,
}

/// What every re-check lane reads of one artifact (R113).
#[derive(Clone, Debug)]
#[non_exhaustive]
pub struct ArtifactRead {
    /// Whether the `.olean` says `isModule`.
    pub is_module: bool,
    /// The part every reading of the artifact agrees on: `.olean.private` for a
    /// module-system artifact, `.olean` otherwise.
    pub authoritative: OLeanLevel,
    /// The authoritative part's import list.
    pub imports: Vec<ParsedImport>,
    /// Exact structural import identities of the authoritative part.
    pub typed_imports: Vec<super::TypedImport>,
    /// Every present part has a valid Clean-format payload. This identifies
    /// an encoding, not the author or the authority of its declarations.
    /// The ordinary parser rejects a payload appended to a Lean-format part.
    pub clean_payload_parts: bool,
    /// The authoritative part's declared constant names (`constNames`).
    pub names: Vec<Name>,
    /// Separate strict Records inventory. Compatibility names and ownership
    /// remain unchanged; unavailable metadata never becomes an empty success.
    pub inventory: Option<Result<ArtifactInventory, ArtifactInventoryError>>,
}

/// Read the artifact whose `.olean` is `path` (labelled `module` in a refusal)
/// with the parsers the loader registers it with, and check it.
///
/// # Errors
///
/// [`ImportError::FileUnreadable`]/[`ImportError::Parse`] for a part that
/// cannot be read or parsed (a Clean payload trailer on a Lean-written part is
/// a parse refusal, `OleanError::PayloadOnLeanPart`), and every refusal of
/// [`check_artifact_parts`].
pub fn read_artifact(
    module: &str,
    path: &Path,
    depth: ArtifactDepth,
) -> Result<ArtifactRead, ImportError> {
    let base_bytes = std::fs::read(path)?;
    let server_bytes = read_optional(&path.with_extension("olean.server"))?;
    let private_bytes = read_optional(&path.with_extension("olean.private"))?;
    let (base, server, private) = match depth {
        ArtifactDepth::Names => (
            parse_header_module(base_bytes.clone())?,
            server_bytes
                .clone()
                .map(|b| parse_header_module_incremental(&base_bytes, None, b))
                .transpose()?,
            private_bytes
                .map(|b| parse_header_module_incremental(&base_bytes, server_bytes.as_deref(), b))
                .transpose()?,
        ),
        ArtifactDepth::Records => (
            parse_load_module(base_bytes.clone())?,
            server_bytes
                .clone()
                .map(|b| parse_load_module_incremental(&base_bytes, None, b))
                .transpose()?,
            private_bytes
                .map(|b| parse_load_module_incremental(&base_bytes, server_bytes.as_deref(), b))
                .transpose()?,
        ),
    };
    check_artifact_parts(module, &base, server.as_ref(), private.as_ref(), depth)?;
    let (authoritative, part) = if base.is_module {
        // `check_artifact_parts` proved the private part present.
        (OLeanLevel::Private, private.as_ref().unwrap_or(&base))
    } else {
        (OLeanLevel::Exported, &base)
    };
    let clean_payload_parts = [Some(&base), server.as_ref(), private.as_ref()]
        .into_iter()
        .flatten()
        .all(|part| part.clean_payload.is_some());
    Ok(ArtifactRead {
        is_module: base.is_module,
        authoritative,
        imports: part.imports.clone(),
        typed_imports: part.typed_imports.clone(),
        clean_payload_parts,
        names: part.const_names.clone(),
        inventory: (depth == ArtifactDepth::Records)
            .then(|| inventory::build(part, ArtifactInventoryLimits::default())),
    })
}

/// R113's artifact rule over the parts of `module`, in level order. Refuses:
///
/// 1. parts that state different headers: `isModule`, and for a module-system
///    artifact its import list (`ImportError::PartsDisagreeOnHeader`), or a
///    module-system artifact missing its `.olean.server` or `.olean.private`
///    (`ImportError::MissingModulePart`); a non-module artifact's companion
///    lists are not compared, as no reader follows them;
/// 2. at [`ArtifactDepth::Records`], two parts stating one name differently
///    (`ImportError::PartsDisagree`, artifact_ledger rule 4's comparison: the
///    same record, or — in a module-system artifact only, [`StubRule`] — an
///    earlier value-free stub of a later value), or one part stating a name
///    twice (`ImportError::DuplicateDeclaration`);
/// 3. a name a part declares that the authoritative part does not
///    (`ImportError::MisplacedDeclaration`).
///
/// The first refusal in that order is returned, so an artifact whose parts
/// both disagree on a value and misplace a name is named by the disagreement.
pub(crate) fn check_artifact_parts(
    module: &str,
    base: &LoadModule,
    server: Option<&LoadModule>,
    private: Option<&LoadModule>,
    depth: ArtifactDepth,
) -> Result<(), ImportError> {
    for part in [server, private].into_iter().flatten() {
        if base.is_module && part.typed_imports != base.typed_imports {
            return Err(ImportError::PartsDisagreeOnHeader {
                module: module.to_string(),
                what: "its imports",
            });
        }
        if part.is_module != base.is_module {
            return Err(ImportError::PartsDisagreeOnHeader {
                module: module.to_string(),
                what: "whether it is a module",
            });
        }
    }
    if base.is_module {
        for (part, name) in [(server, ".olean.server"), (private, ".olean.private")] {
            if part.is_none() {
                return Err(ImportError::MissingModulePart {
                    module: module.to_string(),
                    part: name,
                });
            }
        }
    }
    if depth == ArtifactDepth::Records {
        let stubs = if base.is_module {
            StubRule::CompletedByLaterPart
        } else {
            StubRule::Restated
        };
        check_one_record_per_name(module, &[Some(base), server, private], stubs)?;
    }
    refuse_misplaced_declarations(module, base, server, private, depth)
}

/// Whether an earlier part's value-free stub may stand for a later part's value
/// (rule 2 of [`check_artifact_parts`]).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum StubRule {
    /// A module-system artifact: `Lean.addDecl` exports a public theorem as an
    /// `axiom` of its type, and the `.olean.private`, the part an importer that
    /// is not a `module` reads, holds the theorem.
    CompletedByLaterPart,
    /// Any other artifact: every importer reads its `.olean` alone and
    /// `writeModule` writes it no companion, so a companion may only restate
    /// the `.olean` (R131).
    Restated,
}

/// Rule 2 of [`check_artifact_parts`].
fn check_one_record_per_name(
    module: &str,
    parts: &[Option<&LoadModule>; 3],
    stubs: StubRule,
) -> Result<(), ImportError> {
    let tables = parts
        .iter()
        .map(|part| {
            let mut table: BTreeMap<&Name, &LoadConstant> = BTreeMap::new();
            if let Some(part) = part {
                for c in &part.constants {
                    if table.insert(&c.kernel_name, c).is_some() {
                        return Err(ImportError::DuplicateDeclaration {
                            name: c.kernel_name.to_string(),
                            what: "declaration",
                        });
                    }
                }
            }
            Ok(table)
        })
        .collect::<Result<Vec<_>, _>>()?;
    let disagree = |name: &Name| ImportError::PartsDisagree {
        name: name.to_string(),
        module: module.to_string(),
    };
    for (i, earlier_part) in parts.iter().enumerate() {
        let Some(earlier_part) = earlier_part else {
            continue;
        };
        for (j, later_part) in parts.iter().enumerate().skip(i + 1) {
            let Some(later_part) = later_part else {
                continue;
            };
            for (name, earlier) in &tables[i] {
                let Some(later) = tables[j].get(name) else {
                    continue;
                };
                if !records_agree(earlier_part, earlier, later_part, later, stubs) {
                    return Err(disagree(name));
                }
            }
        }
    }
    Ok(())
}

/// Whether `earlier` (of `earlier_part`) and `later` (of `later_part`) state one
/// declaration: the same record, or — where `stubs` allows it — a value-free
/// stub of `later`'s value.
///
/// The parts of a Lean-written module share the objects of a record they both
/// hold (`PartSubset.lean`: every type and value pointer of 471,516 two-part
/// pairs), so equal raw records are decided without conversion; anything else
/// is converted and compared by artifact_ledger rule 4's comparison.
fn records_agree(
    earlier_part: &LoadModule,
    earlier: &LoadConstant,
    later_part: &LoadModule,
    later: &LoadConstant,
    stubs: StubRule,
) -> bool {
    let completable = stubs == StubRule::CompletedByLaterPart;
    if raw_same(earlier, later) || (completable && raw_stub_of(earlier, later)) {
        return true;
    }
    let convert = |part: &LoadModule, c: &LoadConstant| {
        let region = part.region();
        let mut intern = ExprInternCache::with_capacity(64);
        let mut memo = super::convert_expr_direct::RegionPtrCache::for_region();
        let converted = super::convert_direct::convert_load_constant(
            c,
            &region,
            &mut intern,
            &mut memo,
            ProofValueElision::None,
        );
        super::load_register::part_record(&converted, super::load_register::load_constant_safety(c))
    };
    match (convert(earlier_part, earlier), convert(later_part, later)) {
        (Some(a), Some(b)) if completable => super::artifact_ledger::records_agree(&a, &b),
        (Some(a), Some(b)) => super::artifact_ledger::records_same(&a, &b),
        // A record that does not convert cannot be shown to agree (rule 4).
        _ => false,
    }
}

/// Every raw field equal: the same record (object pointers included).
fn raw_same(a: &LoadConstant, b: &LoadConstant) -> bool {
    a.kernel_name == b.kernel_name
        && a.kind == b.kind
        && a.kernel_level_params == b.kernel_level_params
        && a.kernel_all == b.kernel_all
        && a.kernel_ctors == b.kernel_ctors
        && a.kernel_inductive == b.kernel_inductive
        && a.runtime_mutual == b.runtime_mutual
        && a.type_ptr == b.type_ptr
        && a.value_ptr == b.value_ptr
        && a.inductive_val == b.inductive_val
        && a.num_nested == b.num_nested
        && a.constructor_val == b.constructor_val
        && a.recursor_val == b.recursor_val
        && a.hints == b.hints
        && a.definition_safety == b.definition_safety
}

/// `stub` is the exported `axiom` of `full`'s value: no value, the same
/// universe parameters and the same type object.
fn raw_stub_of(stub: &LoadConstant, full: &LoadConstant) -> bool {
    stub.kind == ConstantKind::Axiom
        && stub.value_ptr == 0
        && full.value_ptr != 0
        && matches!(
            full.kind,
            ConstantKind::Definition | ConstantKind::Theorem | ConstantKind::Opaque
        )
        && stub.kernel_name == full.kernel_name
        && stub.kernel_level_params == full.kernel_level_params
        && stub.type_ptr == full.type_ptr
        && super::artifact_ledger::stub_safety_agrees(
            stub.definition_safety,
            &full.kind,
            full.definition_safety,
        )
}

/// The kernel constant names a part declares — its Lean-format records (or, at
/// [`ArtifactDepth::Names`], its `constNames`) and its Clean payload's, with
/// no name-based exclusions. Unsafe auxiliaries are still source records.
fn part_declared_names(
    part: &LoadModule,
    depth: ArtifactDepth,
) -> std::collections::BTreeSet<Name> {
    inventory::occurrences(part, depth)
        .map(|(name, _)| name.clone())
        .collect()
}

/// Rule 3 of [`check_artifact_parts`]: refuse a name the authoritative part
/// lacks, naming the first in sorted order.
fn refuse_misplaced_declarations(
    module: &str,
    base: &LoadModule,
    server: Option<&LoadModule>,
    private: Option<&LoadModule>,
    depth: ArtifactDepth,
) -> Result<(), ImportError> {
    let (authoritative, authoritative_label, checked): (&LoadModule, &'static str, [_; 2]) =
        if base.is_module {
            let Some(private) = private else {
                return Ok(());
            };
            (
                private,
                ".olean.private",
                [Some((".olean", base)), server.map(|s| (".olean.server", s))],
            )
        } else {
            (
                base,
                ".olean",
                [
                    server.map(|s| (".olean.server", s)),
                    private.map(|p| (".olean.private", p)),
                ],
            )
        };
    let authoritative_names = part_declared_names(authoritative, depth);
    for (part_label, part) in checked.into_iter().flatten() {
        for name in part_declared_names(part, depth) {
            if !authoritative_names.contains(&name) {
                return Err(ImportError::MisplacedDeclaration {
                    module: module.to_string(),
                    part: part_label,
                    authoritative: authoritative_label,
                    name: name.to_string(),
                });
            }
        }
    }
    Ok(())
}
