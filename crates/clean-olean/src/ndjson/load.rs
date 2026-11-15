// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! An export's declarations into an [`Environment`], in the `.olean`
//! loader's structural tier.
//!
//! The environment starts EMPTY: no Clean prelude, no quotient, nothing but
//! the native-reducer table that `Environment::for_lean_replay` also installs
//! (a reducer fires in `KernelTheory::Lean` only where that profile admits
//! it). Every declaration but a `quot` record goes through
//! `register_front_end_constants`, which is the `.olean` loader's own
//! registration, so the replay sees exactly what it sees for a Lean-built
//! `.olean`.
//!
//! The quotient enters only through `Environment::add_quot`, after the
//! export's `Eq` is resident: Lean's `add_quot` (`quot_consts::check_eq_type`)
//! requires an `Eq` of exactly the shape `Quot.lift`'s and `Quot.sound`'s
//! kernel-built types name, and `for_lean_replay`'s up-front quotient would
//! let a forged `Eq` choose what `Quot.sound` asserts. A `quot` record's
//! stored type must equal the kernel-built one (up to binder information and
//! the names of its universe parameters); Lean's replay ignores it, this
//! reader refuses a record that disagrees.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

use clean_kernel::env::{Declaration, Environment, KernelTheory};
use clean_kernel::expr::{Expr, ExprKind, UsedConstants};
use clean_kernel::inductive::{ConstructorVal, InductiveVal, RecursorRule, RecursorVal};
use clean_kernel::level::Level;
use clean_kernel::name::Name;

use super::decl::{ExportDeclaration, ExportHeader, ExportInductiveBlock};
use super::error::NdjsonError;
use super::levels::LevelTaint;
use super::source::ExportSource;
use super::world::ExportMeta;
use crate::import::{
    infer_recursor_arg_order, is_aux_recursor_suffix, register_front_end_constants,
    ConvertedConstant, ExprSharingStats,
};
use crate::module::{ConstantKind, DefinitionSafety, ParsedQuotKind, ReducibilityHintsData};

/// What one declared name is, for the per-declaration report.
#[derive(Debug, Clone)]
pub(crate) struct DeclaredEntry {
    pub(crate) name: Name,
    pub(crate) kind: &'static str,
    pub(crate) line: u64,
}

/// An export loaded into its replay environment.
pub(crate) struct LoadedExport {
    pub(crate) env: Environment,
    pub(crate) meta: ExportMeta,
    /// Every declared name, in the order the export declares them.
    pub(crate) declared: Vec<DeclaredEntry>,
    /// Declarations refused before the replay, with why (structural tier,
    /// quotient admission, unknown constants).
    pub(crate) refused: BTreeMap<Name, String>,
    /// `unsafe` and `partial` declarations, left out as Lean's replay leaves
    /// them out, with which.
    pub(crate) not_replayable: BTreeMap<Name, &'static str>,
    /// The constants each declaration's stored data mentions (an inductive
    /// family member: its whole block's).
    pub(crate) refs: BTreeMap<Name, BTreeSet<Name>>,
    /// The declared safe axioms.
    pub(crate) axioms: BTreeSet<Name>,
    /// The quotient names the export declares through `quot` records.
    pub(crate) quot_records: BTreeSet<Name>,
    /// The names stored otherwise than written (`names.rs`), with the
    /// written name.
    pub(crate) written_names: HashMap<Name, Name>,
    /// The first declaration over a level that keeps the export from being
    /// accepted (`levels.rs`), and how many there are.
    pub(crate) level_taint: (Option<LevelTaint>, usize),
}

impl LoadedExport {
    /// A stored name, rendered unambiguously as the export wrote it.
    pub(crate) fn shown(&self, name: &Name) -> String {
        shown(&self.written_names, name)
    }
}

fn shown(written_names: &HashMap<Name, Name>, name: &Name) -> String {
    written_names
        .get(name)
        .unwrap_or(name)
        .to_unambiguous_string()
}

/// The empty replay environment: Lean's kernel theory, no declarations.
fn replay_environment() -> Environment {
    let mut env = Environment::default();
    env.ensure_native_reducers();
    env.set_kernel_theory(KernelTheory::Lean);
    env
}

fn mentions(exprs: &[&Expr]) -> BTreeSet<Name> {
    let mut found: HashSet<Name> = HashSet::new();
    for e in exprs {
        e.used_constants_dag(UsedConstants::WithProjectionStructures, &mut found);
    }
    found.into_iter().collect()
}

fn other(
    name: &Name,
    decl: Declaration,
    hints: Option<ReducibilityHintsData>,
) -> ConvertedConstant {
    ConvertedConstant::Other(
        name.to_string(),
        Ok((decl, hints)),
        ExprSharingStats::default(),
    )
}

/// The inductive a recursor eliminates, read off its name as the `.olean`
/// loader reads it (`convert_recursor_val_partial`); the block replay compares
/// the stored recursor with the regenerated one, so a wrong reading refuses.
fn recursor_inductive(name: &Name) -> Name {
    let rendered = name.to_string();
    let stripped = rendered
        .strip_suffix(".rec")
        .or_else(|| rendered.strip_suffix(".recOn"))
        .or_else(|| rendered.strip_suffix(".casesOn"))
        .or_else(|| rendered.strip_suffix(".brecOn"))
        .or_else(|| {
            rendered
                .rsplit_once('.')
                .filter(|(_, suffix)| is_aux_recursor_suffix(suffix))
                .map(|(parent, _)| parent)
        })
        .unwrap_or(&rendered);
    Name::from_string(stripped)
}

struct Loader {
    meta: ExportMeta,
    converted: Vec<ConvertedConstant>,
    /// The block that declares `Eq`, registered before the quotient.
    eq_block: Vec<ConvertedConstant>,
    /// The export's own `axiom Quot.sound`, if it declares one: compared with
    /// the kernel's when the quotient is installed, registered as an ordinary
    /// axiom when it is not.
    quot_sound: Option<(ExportHeader, ConvertedConstant)>,
    marks: Vec<(Name, ConstantKind, DefinitionSafety)>,
    declared: Vec<DeclaredEntry>,
    not_replayable: BTreeMap<Name, &'static str>,
    refs: BTreeMap<Name, BTreeSet<Name>>,
    axioms: BTreeSet<Name>,
    quots: Vec<(ExportHeader, ParsedQuotKind)>,
}

impl Loader {
    fn declare(&mut self, name: &Name, kind: &'static str, line: u64) {
        self.declared.push(DeclaredEntry {
            name: name.clone(),
            kind,
            line,
        });
    }

    fn safety(&mut self, name: &Name, kind: ConstantKind, safety: DefinitionSafety) {
        match safety {
            DefinitionSafety::Unsafe => {
                self.not_replayable.insert(name.clone(), "unsafe");
            }
            DefinitionSafety::Partial => {
                self.not_replayable.insert(name.clone(), "partial");
            }
            _ => {}
        }
        self.marks.push((name.clone(), kind, safety));
    }

    fn unsafe_flag(is_unsafe: bool) -> DefinitionSafety {
        if is_unsafe {
            DefinitionSafety::Unsafe
        } else {
            DefinitionSafety::Safe
        }
    }

    fn add(&mut self, line: u64, decl: ExportDeclaration) {
        match decl {
            ExportDeclaration::Axiom { header, is_unsafe } => {
                let ExportHeader {
                    name,
                    level_params,
                    type_,
                } = header;
                self.declare(&name, "axiom", line);
                self.refs.insert(name.clone(), mentions(&[&type_]));
                if !is_unsafe {
                    self.axioms.insert(name.clone());
                }
                self.safety(&name, ConstantKind::Axiom, Self::unsafe_flag(is_unsafe));
                let header = ExportHeader {
                    name: name.clone(),
                    level_params: level_params.clone(),
                    type_: type_.clone(),
                };
                let decl = Declaration::Axiom {
                    name: name.clone(),
                    level_params,
                    type_,
                };
                let converted = other(&name, decl, None);
                if name == Name::from_string("Quot.sound") {
                    self.quot_sound = Some((header, converted));
                } else {
                    self.converted.push(converted);
                }
            }
            ExportDeclaration::Definition {
                header,
                value,
                hints,
                safety,
            } => {
                let ExportHeader {
                    name,
                    level_params,
                    type_,
                } = header;
                self.declare(&name, "def", line);
                self.refs.insert(name.clone(), mentions(&[&type_, &value]));
                self.safety(&name, ConstantKind::Definition, safety);
                let decl = Declaration::Definition {
                    name: name.clone(),
                    level_params,
                    type_,
                    value,
                    is_reducible: hints == ReducibilityHintsData::Abbrev,
                };
                self.converted.push(other(&name, decl, Some(hints)));
            }
            ExportDeclaration::Theorem { header, value } => {
                let ExportHeader {
                    name,
                    level_params,
                    type_,
                } = header;
                self.declare(&name, "thm", line);
                self.refs.insert(name.clone(), mentions(&[&type_, &value]));
                let decl = Declaration::Theorem {
                    name: name.clone(),
                    level_params,
                    type_,
                    value,
                };
                self.converted.push(other(&name, decl, None));
            }
            ExportDeclaration::Opaque {
                header,
                value,
                is_unsafe,
            } => {
                let ExportHeader {
                    name,
                    level_params,
                    type_,
                } = header;
                self.declare(&name, "opaque", line);
                self.refs.insert(name.clone(), mentions(&[&type_, &value]));
                self.safety(&name, ConstantKind::Opaque, Self::unsafe_flag(is_unsafe));
                let decl = Declaration::Opaque {
                    name: name.clone(),
                    level_params,
                    type_,
                    value,
                };
                self.converted.push(other(&name, decl, None));
            }
            ExportDeclaration::Quot { header, kind } => {
                self.declare(&header.name, "quot", line);
                self.refs
                    .insert(header.name.clone(), mentions(&[&header.type_]));
                self.quots.push((header, kind));
            }
            ExportDeclaration::Inductive(block) => self.add_block(line, block),
        }
    }

    fn add_block(&mut self, line: u64, block: ExportInductiveBlock) {
        let eq = Name::from_string("Eq");
        let is_eq_block = block.types.iter().any(|t| t.header.name == eq);
        let mut converted = Vec::new();
        self.convert_block(line, block, &mut converted);
        if is_eq_block {
            self.eq_block.extend(converted);
        } else {
            self.converted.extend(converted);
        }
    }

    fn convert_block(
        &mut self,
        line: u64,
        block: ExportInductiveBlock,
        out: &mut Vec<ConvertedConstant>,
    ) {
        let mut exprs: Vec<&Expr> = Vec::new();
        exprs.extend(block.types.iter().map(|t| &t.header.type_));
        exprs.extend(block.ctors.iter().map(|c| &c.header.type_));
        for rec in &block.recs {
            exprs.push(&rec.header.type_);
            exprs.extend(rec.rules.iter().map(|r| &r.rhs));
        }
        let members: BTreeSet<Name> = block
            .types
            .iter()
            .map(|t| t.header.name.clone())
            .chain(block.ctors.iter().map(|c| c.header.name.clone()))
            .chain(block.recs.iter().map(|r| r.header.name.clone()))
            .collect();
        let block_refs: BTreeSet<Name> = mentions(&exprs)
            .into_iter()
            .filter(|n| !members.contains(n))
            .collect();
        for name in &members {
            self.refs.insert(name.clone(), block_refs.clone());
        }
        for t in block.types {
            let name = t.header.name;
            self.declare(&name, "inductive", line);
            self.safety(
                &name,
                ConstantKind::Inductive,
                Self::unsafe_flag(t.is_unsafe),
            );
            let val = InductiveVal {
                name: name.clone(),
                level_params: t.header.level_params,
                type_: t.header.type_,
                num_params: t.num_params,
                num_indices: t.num_indices,
                all_names: t.all,
                constructor_names: t.ctors,
                is_recursive: t.is_rec,
                is_reflexive: t.is_reflexive,
                // Recomputed by the structural tier once the family is resident.
                is_large_elim: true,
                is_nested: t.num_nested > 0,
            };
            out.push(ConvertedConstant::Inductive(
                name.to_string(),
                Ok(val),
                ExprSharingStats::default(),
            ));
        }
        for c in block.ctors {
            let name = c.header.name;
            self.declare(&name, "constructor", line);
            self.safety(
                &name,
                ConstantKind::Constructor,
                Self::unsafe_flag(c.is_unsafe),
            );
            let val = ConstructorVal {
                name: name.clone(),
                inductive_name: c.induct,
                level_params: c.header.level_params,
                type_: c.header.type_,
                num_params: c.num_params,
                num_fields: c.num_fields,
                constructor_idx: c.cidx,
            };
            out.push(ConvertedConstant::Constructor(
                name.to_string(),
                Ok(val),
                ExprSharingStats::default(),
            ));
        }
        for r in block.recs {
            let name = r.header.name;
            self.declare(&name, "recursor", line);
            self.safety(
                &name,
                ConstantKind::Recursor,
                Self::unsafe_flag(r.is_unsafe),
            );
            let rendered = name.to_string();
            let val = RecursorVal {
                name: name.clone(),
                arg_order: infer_recursor_arg_order(&rendered),
                level_params: r.header.level_params,
                type_: r.header.type_,
                inductive_name: recursor_inductive(&name),
                num_params: r.num_params,
                num_indices: r.num_indices,
                num_motives: r.num_motives,
                num_minors: r.num_minors,
                rules: r
                    .rules
                    .into_iter()
                    .map(|rule| RecursorRule {
                        constructor_name: rule.ctor,
                        num_fields: rule.nfields,
                        // Computed by the structural tier from the resident
                        // constructor.
                        recursive_fields: Vec::new(),
                        rhs: rule.rhs,
                    })
                    .collect(),
                is_k: r.k,
            };
            let param_count = val.num_params;
            out.push(ConvertedConstant::Recursor(
                rendered,
                Ok((val, r.all, param_count)),
                ExprSharingStats::default(),
            ));
        }
    }
}

/// Load every declaration of `source`, or refuse/decline at the first reader
/// error.
pub(crate) fn load_export<S: ExportSource>(mut source: S) -> Result<LoadedExport, NdjsonError> {
    let mut loader = Loader {
        meta: source.meta().clone(),
        converted: Vec::new(),
        eq_block: Vec::new(),
        quot_sound: None,
        marks: Vec::new(),
        declared: Vec::new(),
        not_replayable: BTreeMap::new(),
        refs: BTreeMap::new(),
        axioms: BTreeSet::new(),
        quots: Vec::new(),
    };
    while let Some((line, decl)) = source.next_declaration()? {
        loader.add(line, decl);
    }
    let written_names = source.written_names();
    let level_taint = source.level_taint();
    let Loader {
        meta,
        mut converted,
        eq_block,
        quot_sound,
        marks,
        declared,
        not_replayable,
        refs,
        axioms,
        quots,
    } = loader;

    let mut env = replay_environment();
    let mut refused: BTreeMap<Name, String> = BTreeMap::new();
    let mut skipped = Vec::new();
    // `Eq` first: Lean's `add_quot` installs the quotient only over a
    // resident `Eq`, and every family whose fields name the quotient needs it
    // installed before the structural tier regenerates its recursors.
    skipped.extend(register_front_end_constants(&mut env, eq_block, Vec::new()).skipped_constants);
    let quot_records: BTreeSet<Name> = quots.iter().map(|(h, _)| h.name.clone()).collect();
    if quots.is_empty() {
        // No quotient: an `axiom Quot.sound` is an axiom like any other.
        converted.extend(quot_sound.map(|(_, c)| c));
    } else {
        super::quot::admit_quotient(
            &mut env,
            &quots,
            quot_sound.as_ref().map(|(h, _)| h),
            &mut refused,
        );
    }
    skipped.extend(register_front_end_constants(&mut env, converted, marks).skipped_constants);
    for skip in skipped {
        refused.insert(
            Name::from_string(&skip.name),
            format!("the structural tier refused it: {}", skip.reason),
        );
    }

    // A constant the export does not declare is unknown to Lean's replay
    // (`(kernel) unknown constant`). The replay environment holds nothing the
    // export did not declare except what `add_quot` installs with the
    // quotient: `Quot.sound`, which Lean declares in `Init.Core` and not in
    // `quotDecl`, so an export that uses it must declare it.
    let declared_names: BTreeSet<&Name> = declared.iter().map(|d| &d.name).collect();
    for (name, mentioned) in &refs {
        if let Some(unknown) = mentioned.iter().find(|m| !declared_names.contains(m)) {
            refused.entry(name.clone()).or_insert_with(|| {
                format!(
                    "(kernel) unknown constant '{}': the export does not declare it",
                    shown(&written_names, unknown)
                )
            });
        }
    }

    Ok(LoadedExport {
        env,
        meta,
        declared,
        refused,
        not_replayable,
        refs,
        axioms,
        quot_records,
        written_names,
        level_taint,
    })
}

/// Structural equality ignoring binder information, as Lean's `expr ==` does.
/// Iterative: a stored type is untrusted input of any depth.
pub(crate) fn same_modulo_binder_info(a: &Expr, b: &Expr) -> bool {
    let mut stack: Vec<(&Expr, &Expr)> = vec![(a, b)];
    while let Some((x, y)) = stack.pop() {
        match (x.kind(), y.kind()) {
            (ExprKind::Pi(_, t1, b1), ExprKind::Pi(_, t2, b2))
            | (ExprKind::Lam(_, t1, b1), ExprKind::Lam(_, t2, b2)) => {
                stack.push((t1, t2));
                stack.push((b1, b2));
            }
            (ExprKind::App(f1, a1), ExprKind::App(f2, a2)) => {
                stack.push((f1, f2));
                stack.push((a1, a2));
            }
            _ if x == y => {}
            _ => return false,
        }
    }
    true
}

/// `type_` with its universe parameters renamed, positionally, to `to`.
pub(crate) fn rename_level_params(type_: &Expr, from: &[Name], to: &[Name]) -> Expr {
    let levels: Vec<Level> = to.iter().cloned().map(Level::param).collect();
    type_.instantiate_level_params_direct(from, &levels)
}
