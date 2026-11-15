// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use crate::constant::ConstantG;
use crate::inst::*;
use crate::node::InstrNodeG;
// ObligationKind and ProofStatus are used via their Display impls in the Module Display
use crate::text_directives as directive;
use crate::ty::FuncTyG;
use core::fmt;

impl<X: crate::level::Extension> fmt::Display for crate::ModuleG<X> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "; TrustIr text format v1")?;
        // Roadmap WS4.2 (F-065): a module with fields the grammar cannot
        // carry is printed with a `; #lossy:` marker the parser REFUSES, so a
        // lossy dump can never be parsed back into a module that silently
        // lacks them. A tripwire, not integrity — see `crate::text_loss`.
        let losses = crate::text_loss::text_losses(self);
        if !losses.is_empty() {
            writeln!(
                f,
                "; {}: {}",
                directive::LOSSY,
                crate::text_loss::summarize(&losses)
            )?;
        }
        writeln!(f, "module {:?}", self.name)?;

        if let Some(ti) = &self.target_info {
            write!(
                f,
                "target {:?} {} {}",
                ti.triple, ti.pointer_size, ti.endianness
            )?;
            // ABI pinning (v20): emitted only when non-default so legacy
            // modules keep their historical text form; the parser defaults
            // absent trailers to None / NativeC.
            if let Some(abi) = &ti.abi {
                write!(f, " abi={abi:?}")?;
            }
            if ti.struct_passing != crate::StructPassingPolicy::default() {
                write!(f, " structpass={}", ti.struct_passing)?;
            }
            writeln!(f)?;
        }

        // WS4.5 (linkage half, F-065): module-level `global_asm!` blocks, one
        // `global_asm "<escaped>"` line per block in source order, after the
        // target and before every table. Before this the field had no text
        // spelling, so a module carrying it printed `#lossy` and was refused —
        // and before WS4.2 it was silently DROPPED, which laundered the
        // `GlobalAsmNotConsumable` codegen refusal. The block is opaque text;
        // the escape set is `write_escaped_string`'s, which
        // `Parser::read_quoted_string` inverts exactly (newlines, quotes,
        // backslashes and every control character).
        for block in &self.global_asm {
            write!(f, "global_asm ")?;
            write_escaped_string(f, block)?;
            writeln!(f)?;
        }

        // Debug-info source-file table; `SourceSpan::file` indexes it.
        for (i, path) in self.files.iter().enumerate() {
            writeln!(f, "file {i} {path:?}")?;
        }

        for sd in &self.structs {
            write!(f, "\nstruct @")?;
            write_symbol(f, &sd.name)?;
            write!(f, " {{ ")?;
            // WS4.5 (struct half): a field carries its NAME and, when the
            // producer gave one, its OFFSET — `name: ty @off`. Before this the
            // text was a bare type list, so `StructFieldNames` /
            // `StructFieldOffsets` made the whole module unrepresentable.
            // Canonical printing ALWAYS emits `name: ty` (the bare list stays
            // READABLE as the legacy spelling, meaning name "" and offset None,
            // but is never printed).
            for (i, field) in sd.fields.iter().enumerate() {
                if i > 0 {
                    write!(f, ", ")?;
                }
                // TOTAL over (name, offset), one spelling each:
                //   ("",   None)      -> `ty`            (the legacy form IS
                //                                         canonical here: there
                //                                         is nothing to carry)
                //   ("",   Some(off)) -> `: ty @off`     (empty name, so nothing
                //                                         before the colon)
                //   (name, _)         -> `name: ty [@off]`
                // An empty name must NOT go through `write_symbol`: it is not
                // bare-able, so that would print `""`, which `read_symbol`
                // refuses as `empty symbol` — the field would not round-trip.
                if field.name.is_empty() && field.offset.is_none() {
                    write!(f, "{}", field.ty)?;
                } else {
                    if !field.name.is_empty() {
                        write_symbol(f, &field.name)?;
                    }
                    write!(f, ": {}", field.ty)?;
                    if let Some(off) = field.offset {
                        write!(f, " @{off}")?;
                    }
                }
            }
            write!(f, " }}")?;
            if let Some(size) = sd.size {
                write!(f, " size={size}")?;
            }
            if let Some(align) = sd.align {
                write!(f, " align={align}")?;
            }
            // ABI repr, emitted only when non-default so Rust-repr structs keep
            // their existing text form; the parser defaults absent `repr` to Rust.
            if sd.repr != crate::ty::StructRepr::Rust {
                write!(f, " repr={}", sd.repr)?;
            }
            // v58 nominal identity key, emitted only when present so unkeyed
            // definitions keep their historical text form.
            if let Some(origin) = &sd.origin {
                write!(f, " origin={origin}")?;
            }
            // Explicit id trailer (`id=N`) so the original `StructId` survives a
            // text round trip even when ids are sparse/non-contiguous (finding
            // E). Emitted last so the human-readable `struct @Name { .. }`
            // prefix is unchanged; the parser reads it back into `StructId`.
            write!(f, " id={}", sd.id.index())?;
            writeln!(f)?;
        }

        for ed in &self.enums {
            write!(f, "\nenum @")?;
            write_symbol(f, &ed.name)?;
            // Optional tag-representation hint: `repr(u8)` etc., between the
            // name and the variant list.
            if let Some(repr) = ed.repr {
                write!(f, " repr({repr})")?;
            }
            write!(f, " {{ ")?;
            for (i, variant) in ed.variants.iter().enumerate() {
                if i > 0 {
                    write!(f, ", ")?;
                }
                write_symbol(f, &variant.name)?;
                // WS4.5: per-field source names. When the variant carries them
                // (`field_names` non-empty AND parallel to `fields` — the only
                // shape `validate_module` admits), EVERY field prints
                // `name: ty`, an empty name as `: ty`, mirroring the struct
                // half; a positional variant prints the bare type list. The
                // parser refuses a variant that mixes the two spellings, so
                // printer output keeps one spelling per construct. A
                // non-parallel list is not spelled at all: `text_losses`
                // reports `EnumFieldNames` and the module prints `#lossy`.
                let named = crate::text_loss::enum_variant_field_names_spellable(variant);
                if !variant.fields.is_empty() {
                    write!(f, "(")?;
                    for (j, ty) in variant.fields.iter().enumerate() {
                        if j > 0 {
                            write!(f, ", ")?;
                        }
                        if named {
                            let field_name = &variant.field_names[j];
                            if !field_name.is_empty() {
                                write_symbol(f, field_name)?;
                            }
                            write!(f, ": ")?;
                        }
                        write!(f, "{ty}")?;
                    }
                    write!(f, ")")?;
                }
                // Optional explicit discriminant: `Name = N` / `Name(ty) = N`.
                // Implicit (`None`/missing) entries print nothing, so the
                // all-implicit case keeps the historical text form.
                if let Some(disc) = ed.discriminants.get(i).copied().flatten() {
                    write!(f, " = {disc}")?;
                }
            }
            write!(f, " }}")?;
            // WS4.5 (enum half): the producer's concrete layout descriptor,
            // printed as a `layout(..)` clause between the variant list and
            // the id trailer. Before this, text was layout-agnostic for enums
            // and `EnumLayout` made the whole module unrepresentable — which
            // is what `trust-ir convert --from bin --to text` refused on the
            // rustc-derived battery fixtures.
            //
            // The clause is printed only when the descriptor is SPELLABLE.
            // `enum_layout_text_refusal` is the single authority: when it
            // refuses, `text_losses` reports `EnumLayout`, the module prints
            // `#lossy`, and the parser refuses the text — never a module with
            // a laundered layout.
            if let Some(layout) = &ed.layout
                && crate::text_loss::enum_layout_text_refusal(ed).is_none()
            {
                write!(f, " ")?;
                write_enum_layout(f, layout)?;
            }
            // v58 nominal identity key, emitted only when present.
            if let Some(origin) = &ed.origin {
                write!(f, " origin={origin}")?;
            }
            // Explicit id trailer (`id=N`) so the original `EnumId` survives a
            // text round trip even for sparse ids (finding E).
            writeln!(f, " id={}", ed.id.index())?;
        }

        for rd in &self.records {
            write!(f, "\nrecord @")?;
            write_symbol(f, &rd.name)?;
            write!(f, " {{ ")?;
            for (i, field) in rd.fields.iter().enumerate() {
                if i > 0 {
                    write!(f, ", ")?;
                }
                write_symbol(f, &field.name)?;
                write!(f, ": {}", field.ty)?;
            }
            // Explicit id trailer (`id=N`) so the original `RecordId` survives
            // a text round trip even for sparse ids (finding E).
            writeln!(f, " }} id={}", rd.id.index())?;
        }

        for (idx, ft) in self.func_types.iter().enumerate() {
            write!(f, "\nfuncty.{idx} = ")?;
            write_func_ty(f, ft)?;
            if let Some(abi) = &ft.abi {
                write!(f, " abi(")?;
                write_escaped_string(f, &abi.to_canonical_text())?;
                write!(f, ")")?;
            }
            writeln!(f)?;
        }

        // v41 cross-crate dependency list. Printed BEFORE every table that can
        // cite it, for the same reason universes precede predicates: an
        // `ImportId` is only meaningful against this exact ordering, so the
        // parser must have rebuilt the table before it reads a reference into
        // it.
        for (idx, imp) in self.imports.iter().enumerate() {
            write!(
                f,
                "\nimport import.{idx} = {:?} digest {:?} [",
                imp.name,
                imp.digest.algorithm.to_string()
            )?;
            for (i, byte) in imp.digest.bytes.iter().enumerate() {
                if i > 0 {
                    write!(f, ", ")?;
                }
                write!(f, "{byte}")?;
            }
            write!(f, "]")?;
            if let Some(producer) = &imp.producer {
                write!(f, " producer {producer}")?;
            }
            // v44: the identity scheme, spelled only when it is not the
            // legacy V2 (one spelling per construct: V2 is the omission).
            if !imp.scheme.is_v2() {
                write!(f, " scheme {}", imp.scheme)?;
            }
            writeln!(f)?;
        }

        // Typed value model (v30). Universes precede predicates because a
        // predicate may cite a `UnivId`, and both precede the `types` table
        // because a `Ty::Refine` cites a `PredId`. Table ORDER is identity
        // here — these tables are content-interned, so the index a `Refine`
        // carries is only meaningful against this exact ordering.
        for (idx, universe) in self.universes.iter().enumerate() {
            writeln!(f, "\nuniv univ.{idx} = {universe}")?;
        }

        for (idx, pred) in self.predicates.iter().enumerate() {
            writeln!(f, "\npred pred.{idx} = {pred}")?;
        }

        // Module `types` table. `Ty` aggregates (Array/Set/Sequence/FatPtr
        // slice) reference their element via `TyId` indices into this table, so
        // it MUST be serialized for those references to round-trip (finding A).
        // The binary codec already writes this table; the text form omitted it.
        for (idx, ty) in self.types.iter().enumerate() {
            writeln!(f, "\ntype ty.{idx} = {ty}")?;
        }

        // WS5.3b: the producer's completeness claim. `None` prints NOTHING
        // (no claim is the omission — one spelling per construct), so a
        // module without a claim keeps its exact text. Each `unlowered` row
        // spells `-` for an absent display path.
        match &self.completeness {
            None => {}
            Some(crate::ModuleCompleteness::Complete) => {
                writeln!(f, "\ncompleteness complete")?;
            }
            Some(crate::ModuleCompleteness::Partial(rows)) => {
                writeln!(f, "\ncompleteness partial")?;
                for row in rows {
                    write!(f, "unlowered {:?} ", row.symbol)?;
                    match &row.display_path {
                        Some(path) => write!(f, "{path:?}")?,
                        None => write!(f, "-")?,
                    }
                    writeln!(f, " {:?}", row.reason)?;
                }
            }
        }

        for desc in &self.tuple_layouts {
            write!(
                f,
                "\ntuple_layout ty.{} size={} align={} offsets=[",
                desc.tuple_type.index(),
                desc.size,
                desc.align
            )?;
            for (index, offset) in desc.field_offsets.iter().enumerate() {
                if index != 0 {
                    write!(f, ",")?;
                }
                write!(f, "{offset}")?;
            }
            writeln!(f, "]")?;
        }

        // Amendment D: the drop-glue table, one `drop_glue @func.N <ty>` line
        // per row in the module's (canonical, ascending-glue) order. An empty
        // table prints nothing, so a module without one keeps its text.
        for entry in &self.drop_glue {
            writeln!(f, "\ndrop_glue @func.{} {}", entry.glue.index(), entry.ty)?;
        }

        for desc in &self.closure_layouts {
            write!(
                f,
                "\nclosure_layout closure.{} size={} align={} offsets=[",
                desc.closure.index(),
                desc.size,
                desc.align
            )?;
            for (index, offset) in desc.capture_offsets.iter().enumerate() {
                if index != 0 {
                    write!(f, ",")?;
                }
                write!(f, "{offset}")?;
            }
            write!(f, "]")?;
            if let Some(origin) = &desc.origin {
                write!(f, " origin={origin}")?;
            }
            writeln!(f)?;
        }

        for ct in &self.closure_types {
            write!(f, "\nclosure_ty functy.{} {{ ", ct.func.index())?;
            for (i, cap) in ct.captures.iter().enumerate() {
                if i > 0 {
                    write!(f, ", ")?;
                }
                write!(f, "{cap}")?;
            }
            writeln!(f, " }}")?;
        }

        for global in &self.globals {
            write!(f, "\nglobal")?;
            if global.linkage != crate::Linkage::External {
                write!(f, " {}", global.linkage)?;
            }
            if let Some(tls) = global.tls {
                write!(f, " tls({tls})")?;
            }
            if global.mutable {
                write!(f, " mut")?;
            }
            if let Some(align) = global.align {
                write!(f, " align({align})")?;
            }
            if global.visibility != crate::Visibility::Default {
                write!(f, " visibility({})", global.visibility)?;
            }
            if let Some(section) = &global.section {
                write!(f, " section(")?;
                write_escaped_string(f, section)?;
                write!(f, ")")?;
            }
            if global.retained {
                write!(f, " retained")?;
            }
            write!(f, " @")?;
            write_symbol(f, &global.name)?;
            write!(f, " {}", global.ty)?;
            if let Some(init) = &global.initializer {
                write!(f, " = {init}")?;
            }
            writeln!(f)?;
        }

        for func in &self.functions {
            writeln!(f)?;
            write!(f, "{func}")?;
        }

        for po in &self.proof_obligations {
            write!(f, "\nobligation {} ", po.id.index())?;
            // WS4.4: the MODULE-TEXT spelling of the kind (`custom("<ns>",
            // "<name>")` for the payload-carrying kind); `Display` keeps the
            // diagnostic `custom:<ns>/<name>` form, which is not parseable.
            write_obligation_kind(f, &po.kind)?;
            write!(f, " {} {:?}", po.status, po.description)?;
            // Scope clause (B4): which function this obligation is a
            // pre/postcondition OF. Omitted (back-compat) when None.
            if let Some(func) = &po.function {
                write!(f, " function {}", func.index())?;
            }
            if let Some(formula) = &po.formula {
                // WS4.4: the one shared formula spelling, bindings included.
                // A binding-free formula prints exactly its pre-WS4.4 bytes.
                write!(f, " ")?;
                write_proof_formula(f, formula)?;
            }
            if let Some(source) = &po.source {
                write!(
                    f,
                    " source {:?} assertion {:?}",
                    source.source_id, source.assertion_id
                )?;
                if let Some(range) = &source.range {
                    write!(
                        f,
                        " range {} {} {} {} {}",
                        range.file,
                        range.start_line,
                        range.start_col,
                        range.end_line,
                        range.end_col
                    )?;
                }
                if let Some(public) = &source.public {
                    write!(
                        f,
                        " public {:?} digest {:?} [",
                        public.obligation_id,
                        public.semantic_digest.algorithm.to_string()
                    )?;
                    for (i, byte) in public.semantic_digest.bytes.iter().enumerate() {
                        if i > 0 {
                            write!(f, ", ")?;
                        }
                        write!(f, "{byte}")?;
                    }
                    write!(f, "]")?;
                }
            }
            // v34 site backref: `site f{F}/bb{B}#{I}` — the exact IR position
            // this obligation is ABOUT. Omitted (back-compat) when None.
            if let Some(site) = &po.site {
                write!(
                    f,
                    " site f{}/bb{}#{}",
                    site.function.index(),
                    site.block.index(),
                    site.inst_index
                )?;
            }
            // v46 temporal backref: `spec "<machine>" "<temporal>"` — the
            // named temporal property this obligation DISCHARGES. Omitted
            // when None (NOT RECORDED, never a wildcard).
            if let Some(spec) = &po.spec {
                write!(f, " spec {:?} {:?}", spec.machine, spec.temporal)?;
            }
            writeln!(f)?;
        }

        for cert in &self.proof_certificates {
            write!(
                f,
                "\ncertificate {} {:?} ",
                cert.obligation.index(),
                cert.prover,
            )?;
            write_proof_evidence(f, &cert.evidence)?;
            // WS4.4 (F-064): the v41 coverage projection. Omitted when `None`
            // (NOT RECORDED), so a certificate without one keeps its exact
            // pre-WS4.4 text.
            if let Some(assurance) = &cert.assurance {
                write!(f, " ")?;
                write_coverage_assurance(f, assurance)?;
            }
            writeln!(f)?;
        }

        for d in &self.obligation_diagnostics {
            write!(
                f,
                "\ndiagnostic {} {} {:?}",
                d.obligation.index(),
                d.severity,
                d.message,
            )?;
            if let Some(s) = &d.location {
                write!(f, " at {} {} {}", s.file, s.line, s.col)?;
            }
            if let Some(detail) = &d.detail {
                write!(f, " detail {detail:?}")?;
            }
            writeln!(f)?;
        }

        for sm in &self.spec_modules {
            write_spec_module(f, sm)?;
        }

        Ok(())
    }
}

/// Render a [`crate::spec::SpecModule`] in the canonical text format. The shape
/// mirrors the parser in `parser.rs::parse_spec_module` exactly so that
/// fmt→parse→fmt is a fixed point. All free-form text is quoted via `{:?}`.
/// The text of a level-S template (amendment S, `docs/formats.md`): the
/// header lines, then the module text at `X = TemplateRef`, where parameters
/// print `$n` and holes `?n`. `crate::parser::parse_template` reads it back;
/// the level-R parser refuses it by name.
impl fmt::Display for crate::template::Template {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use crate::template::{HoleKind, TemplateArg, TemplateParam, TypeContract};
        writeln!(f, "; TrustIr template text format v1")?;
        write!(f, "template ")?;
        write_escaped_string(f, &self.header.identity)?;
        writeln!(f)?;
        for (index, param) in self.header.params.iter().enumerate() {
            match param {
                TemplateParam::Type => writeln!(f, "param ${index} type")?,
                TemplateParam::Const { ty } => writeln!(f, "param ${index} const {ty}")?,
                TemplateParam::Host => writeln!(f, "param ${index} host")?,
            }
        }
        for (index, hole) in self.header.holes.iter().enumerate() {
            write!(f, "hole ?{index} ")?;
            match &hole.kind {
                HoleKind::Type { contract } => {
                    write!(f, "type ")?;
                    match contract {
                        TypeContract::Opaque => write!(f, "opaque")?,
                        TypeContract::Struct { fields } => {
                            write!(f, "struct {{")?;
                            for (i, ty) in fields.iter().enumerate() {
                                write!(f, "{}{ty}", if i == 0 { " " } else { ", " })?;
                            }
                            write!(f, " }}")?;
                        }
                        TypeContract::Enum {
                            variants,
                            discriminants,
                            repr,
                        } => {
                            write!(f, "enum {{")?;
                            for (i, fields) in variants.iter().enumerate() {
                                write!(f, "{}[", if i == 0 { " " } else { ", " })?;
                                for (j, ty) in fields.iter().enumerate() {
                                    write!(f, "{}{ty}", if j == 0 { "" } else { ", " })?;
                                }
                                write!(f, "]")?;
                            }
                            write!(f, " }} discriminants [")?;
                            for (i, discriminant) in discriminants.iter().enumerate() {
                                if i > 0 {
                                    write!(f, ", ")?;
                                }
                                match discriminant {
                                    None => write!(f, "none")?,
                                    Some(value) => write!(f, "{value}")?,
                                }
                            }
                            write!(f, "] repr ")?;
                            match repr {
                                None => write!(f, "none")?,
                                Some(repr) => write!(f, "{repr}")?,
                            }
                        }
                    }
                }
                HoleKind::Const { ty } => write!(f, "const {ty}")?,
                HoleKind::Callee { decl } => write!(f, "callee @func.{}", decl.index())?,
                HoleKind::Global { decl } => write!(f, "global @global.{}", decl.index())?,
            }
            write!(f, " key ")?;
            write_escaped_string(f, &hole.key.namespace)?;
            write!(f, " [")?;
            for (i, byte) in hole.key.bytes.iter().enumerate() {
                write!(f, "{}{byte}", if i == 0 { "" } else { ", " })?;
            }
            write!(f, "] args (")?;
            for (i, arg) in hole.args.iter().enumerate() {
                if i > 0 {
                    write!(f, ", ")?;
                }
                match arg {
                    TemplateArg::Type(ty) => write!(f, "{ty}")?,
                    TemplateArg::Const { value, ty } => write!(f, "const {ty} {value}")?,
                    TemplateArg::Host(param) => write!(f, "host ${}", param.index())?,
                }
            }
            writeln!(f, ")")?;
        }
        write!(f, "{}", self.module)
    }
}

fn write_spec_module(f: &mut fmt::Formatter<'_>, sm: &crate::spec::SpecModule) -> fmt::Result {
    use crate::spec::SpecOrigin;
    writeln!(f, "\nspec_module {:?} {{", sm.name)?;
    match &sm.origin {
        SpecOrigin::Embedded => writeln!(f, "  origin embedded")?,
        SpecOrigin::External(path) => writeln!(f, "  origin external {path:?}")?,
    }
    writeln!(f, "  enforcement {}", sm.enforcement.tag())?;
    // WS4.4: the v46 typed carrier (`SpecVar.sort`, `SpecInvariant.typed`,
    // `SpecModule.temporal`) in the shared sort / formula spelling. Each is
    // printed only when present, so an untyped machine keeps its exact text.
    for v in &sm.vars {
        write!(f, "  var {:?} : {:?}", v.name, v.ty)?;
        if let Some(sort) = &v.sort {
            write!(f, " sort ")?;
            write_clause_sort(f, sort)?;
        }
        writeln!(f)?;
    }
    for a in &sm.actions {
        writeln!(f, "  action {a:?}")?;
    }
    for inv in &sm.invariants {
        write!(f, "  invariant {:?} : {:?}", inv.name, inv.formula)?;
        if let Some(typed) = &inv.typed {
            write!(f, " typed ")?;
            write_proof_formula(f, typed)?;
        }
        writeln!(f)?;
    }
    for anchor in &sm.anchors {
        write!(
            f,
            "  anchor machine {:?} action {:?}",
            anchor.machine, anchor.action
        )?;
        if let Some(function) = anchor.function {
            write!(f, " function {}", function.index())?;
        }
        write!(f, " rust {:?} span {:?}", anchor.rust_symbol, anchor.span)?;
        if let Some(p) = &anchor.project {
            write!(f, " project {p:?}")?;
        }
        match anchor.projection_target {
            None => write!(f, " target none")?,
            Some(crate::spec::SpecProjectionTarget::Function(function)) => {
                write!(f, " target function {}", function.index())?;
            }
            Some(crate::spec::SpecProjectionTarget::TemporalFieldPathsV1) => {
                write!(f, " target temporal-field-paths-v1")?;
            }
            Some(crate::spec::SpecProjectionTarget::ExternalUnresolved) => {
                write!(f, " target external-unresolved")?;
            }
        }
        writeln!(f)?;
    }
    for w in &sm.waivers {
        writeln!(
            f,
            "  waiver machine {:?} action {:?} reason {:?}",
            w.machine, w.action, w.reason
        )?;
    }
    for p in &sm.proofs {
        write!(
            f,
            "  proof machine {:?} action {:?} name {:?} kind {:?}",
            p.machine,
            p.action,
            p.proof_name,
            p.kind.tag(),
        )?;
        // v46: a Clean theorem binding carries the kernel theorem name after
        // its kind tag; `kani` carries nothing more.
        if let crate::spec::ProofKind::CleanTheorem { name } = &p.kind {
            write!(f, " theorem {name:?}")?;
        }
        writeln!(f)?;
    }
    for property in &sm.temporal {
        write!(f, "  temporal {:?} ", property.name)?;
        write_temporal_form(f, &property.form)?;
        writeln!(f)?;
    }
    writeln!(f, "}}")?;
    Ok(())
}

/// WS4.4: one v46 [`crate::spec::TemporalForm`], read back by
/// `Parser::parse_temporal_form`.
///
/// ```text
/// always formula "smtlib2" "(>= x 0)" bind "x" int spec_var(0)
/// leads_to formula .. formula ..
/// weak_fair "Step" [formula ..]
/// ```
///
/// The fairness relation is optional (`None` = NOT RECORDED) and is omitted,
/// never spelled as an empty formula.
fn write_temporal_form(
    f: &mut fmt::Formatter<'_>,
    form: &crate::spec::TemporalForm,
) -> fmt::Result {
    use crate::spec::TemporalForm;
    match form {
        TemporalForm::Always(leaf) => {
            write!(f, "always ")?;
            write_proof_formula(f, leaf)
        }
        TemporalForm::Eventually(leaf) => {
            write!(f, "eventually ")?;
            write_proof_formula(f, leaf)
        }
        TemporalForm::LeadsTo(from, to) => {
            write!(f, "leads_to ")?;
            write_proof_formula(f, from)?;
            write!(f, " ")?;
            write_proof_formula(f, to)
        }
        TemporalForm::WeakFair { action, relation } => {
            write!(f, "weak_fair {action:?}")?;
            if let Some(relation) = relation {
                write!(f, " ")?;
                write_proof_formula(f, relation)?;
            }
            Ok(())
        }
        TemporalForm::StrongFair { action, relation } => {
            write!(f, "strong_fair {action:?}")?;
            if let Some(relation) = relation {
                write!(f, " ")?;
                write_proof_formula(f, relation)?;
            }
            Ok(())
        }
    }
}

/// WS4.4: the module-text spelling of an [`crate::proof::ObligationKind`],
/// read back by `Parser::parse_obligation_kind`.
///
/// Every fieldless kind is its `Display` token. `Custom` is the one kind
/// `Display` cannot serve: its diagnostic form `custom:<ns>/<name>` is not
/// injective (a `/` in the namespace moves the split) and not readable by the
/// identifier scanner, so module text spells it `custom("<ns>", "<name>")`,
/// both halves quoted. Namespace ADMISSION stays the validator's
/// (`UnpinnedCustomObligationNamespace`); the grammar carries any string.
fn write_obligation_kind(
    f: &mut fmt::Formatter<'_>,
    kind: &crate::proof::ObligationKind,
) -> fmt::Result {
    match kind {
        crate::proof::ObligationKind::Custom { namespace, name } => {
            write!(f, "custom({namespace:?}, {name:?})")
        }
        other => write!(f, "{other}"),
    }
}

/// WS4.4 (F-064): the ONE text spelling of a [`crate::proof::ProofFormula`],
/// shared by module obligations, `FunctionSummary` clauses (`#requires` /
/// `#ensures` / `#decreases`) and the v46 spec carrier.
///
/// ```text
/// formula "<schema>" "<payload>" [smtlib "<s>"] [sort "<s>"] [bind "<name>" <sort> <place>]*
/// ```
///
/// Bindings print in declaration order (they are a `Vec`, and order is part
/// of the formula's identity: it enters the v6 lineage and the obligation
/// content digest). An EMPTY binding list prints nothing and reads back as an
/// empty list — UNBINDABLE, never a wildcard — so a binding-free formula keeps
/// its exact pre-WS4.4 bytes.
pub(crate) fn write_proof_formula(
    f: &mut fmt::Formatter<'_>,
    formula: &crate::proof::ProofFormula,
) -> fmt::Result {
    // Exhaustive: a new `ProofFormula` field fails to compile here until it
    // is given a spelling (or a `TextLoss`).
    let crate::proof::ProofFormula {
        schema,
        payload,
        smtlib,
        sort,
        bindings,
    } = formula;
    write!(f, "formula {schema:?} {payload:?}")?;
    if let Some(smtlib) = smtlib {
        write!(f, " smtlib {smtlib:?}")?;
    }
    if let Some(sort) = sort {
        write!(f, " sort {sort:?}")?;
    }
    for (name, binding) in bindings {
        write!(f, " bind {name:?} ")?;
        write_clause_sort(f, &binding.sort)?;
        write!(f, " ")?;
        write_clause_place(f, &binding.place)?;
    }
    Ok(())
}

/// WS4.4: one [`crate::proof::ClauseSort`]:
///
/// ```text
/// bool | int | bv(<n>) | array(<sort>, <sort>) | float(<eb>, <sb>) | rm
///   | datatype("<name>", [("<ctor>", [("<field>", <sort>), ..]), ..])
/// ```
///
/// Recursive; the parser caps the nesting depth at
/// [`crate::text_loss::MAX_TEXT_CLAUSE_SORT_DEPTH`], and a deeper sort is a
/// reported [`crate::text_loss::TextLoss`] rather than a text its own reader
/// refuses.
pub(crate) fn write_clause_sort(
    f: &mut fmt::Formatter<'_>,
    sort: &crate::proof::ClauseSort,
) -> fmt::Result {
    use crate::proof::ClauseSort;
    match sort {
        ClauseSort::Bool => write!(f, "bool"),
        ClauseSort::Int => write!(f, "int"),
        ClauseSort::BitVec(width) => write!(f, "bv({width})"),
        ClauseSort::Array(index, element) => {
            write!(f, "array(")?;
            write_clause_sort(f, index)?;
            write!(f, ", ")?;
            write_clause_sort(f, element)?;
            write!(f, ")")
        }
        ClauseSort::Float { eb, sb } => write!(f, "float({eb}, {sb})"),
        ClauseSort::RoundingMode => write!(f, "rm"),
        ClauseSort::Datatype { name, constructors } => {
            write!(f, "datatype({name:?}, [")?;
            for (i, (ctor, fields)) in constructors.iter().enumerate() {
                if i > 0 {
                    write!(f, ", ")?;
                }
                write!(f, "({ctor:?}, [")?;
                for (j, (field, field_sort)) in fields.iter().enumerate() {
                    if j > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "({field:?}, ")?;
                    write_clause_sort(f, field_sort)?;
                    write!(f, ")")?;
                }
                write!(f, "])")?;
            }
            write!(f, "])")
        }
    }
}

/// WS4.4: one [`crate::proof::ClausePlace`]:
///
/// ```text
/// param(<i>) | result(<i>) | mut_exit(<i>) | world | unwind | value(%<v>)
///   | spec_var(<i>) | spec_var_next(<i>) | pointee_entry(<i>)
/// ```
///
/// The grammar spells every place wherever a formula appears; which places
/// are LEGAL where (e.g. `mut_exit` only on an `ensures` clause, a spec
/// variable only inside a `SpecModule`) is the validator's to decide, never
/// the parser's.
pub(crate) fn write_clause_place(
    f: &mut fmt::Formatter<'_>,
    place: &crate::proof::ClausePlace,
) -> fmt::Result {
    use crate::proof::ClausePlace;
    match place {
        ClausePlace::Param { index } => write!(f, "param({index})"),
        ClausePlace::ResultSlot { index } => write!(f, "result({index})"),
        ClausePlace::MutParamExit { index } => write!(f, "mut_exit({index})"),
        ClausePlace::World => write!(f, "world"),
        ClausePlace::Unwind => write!(f, "unwind"),
        ClausePlace::Value(value) => write!(f, "value(%{})", value.index()),
        ClausePlace::SpecVar { index } => write!(f, "spec_var({index})"),
        ClausePlace::SpecVarNext { index } => write!(f, "spec_var_next({index})"),
        ClausePlace::WorldPre => write!(f, "world_pre"),
        ClausePlace::WorldPost => write!(f, "world_post"),
        ClausePlace::ParamPointeeEntry { index } => write!(f, "pointee_entry({index})"),
    }
}

/// `"<alg>" [b0, b1, .., b31]` — the digest spelling the obligation `public`
/// identity and the `clean_cic` lineage already use.
fn write_proof_digest(
    f: &mut fmt::Formatter<'_>,
    digest: &crate::proof::ProofDigest,
) -> fmt::Result {
    write!(f, "{:?} [", digest.algorithm.to_string())?;
    for (i, byte) in digest.bytes.iter().enumerate() {
        if i > 0 {
            write!(f, ", ")?;
        }
        write!(f, "{byte}")?;
    }
    write!(f, "]")
}

/// `["a", "b"]`, each element Debug-quoted.
fn write_string_list(f: &mut fmt::Formatter<'_>, items: &[String]) -> fmt::Result {
    write!(f, "[")?;
    for (i, item) in items.iter().enumerate() {
        if i > 0 {
            write!(f, ", ")?;
        }
        write!(f, "{item:?}")?;
    }
    write!(f, "]")
}

/// `extern <import> "<symbol>" (none | obligation <id>)` — the cross-crate
/// reference spelling shared by `inherited .. extern ..` evidence and the
/// WS4.4 `; #backed-by:` summary directive.
fn write_extern_ref(f: &mut fmt::Formatter<'_>, reference: &crate::ExternRef) -> fmt::Result {
    write!(
        f,
        "extern {} {:?}",
        reference.module.index(),
        reference.symbol
    )?;
    match reference.obligation {
        None => write!(f, " none"),
        Some(obligation) => write!(f, " obligation {}", obligation.index()),
    }
}

/// WS4.4 (F-064): `assurance <bound> digest "<alg>" [bytes]`, where `<bound>`
/// is `unbounded | unwind(<d>) | model(<s>) | unrecorded`. The row is
/// non-authoritative (see [`crate::proof::CoverageAssurance`]); text carries
/// it so a text image says exactly what the binary one does.
fn write_coverage_assurance(
    f: &mut fmt::Formatter<'_>,
    assurance: &crate::proof::CoverageAssurance,
) -> fmt::Result {
    use crate::proof::CoverageBound;
    let crate::proof::CoverageAssurance {
        bound,
        request_digest,
    } = assurance;
    write!(f, "assurance ")?;
    match bound {
        CoverageBound::Unbounded => write!(f, "unbounded")?,
        CoverageBound::UnwindBounded { depth } => write!(f, "unwind({depth})")?,
        CoverageBound::ModelBounded { size } => write!(f, "model({size})")?,
        CoverageBound::Unrecorded => write!(f, "unrecorded")?,
    }
    write!(f, " digest ")?;
    write_proof_digest(f, request_digest)
}

/// WS4.4 (F-070): the `clean_cic` kernel re-check directive,
///
/// ```text
/// recheck module "<m>" anchor "<a>" theorems ["..", ..] axioms ["..", ..]
///   [binding env <digest> statement <digest> [origin <digest>]
///            [source "<decl>" <digest>] callees ["..", ..]
///            [island [<byte>, ..] <digest>]]
/// ```
///
/// Omitted when `None`, so a recheck-less certificate keeps its exact
/// historical text. The WS1.12a [`crate::proof::CertificateBinding`] rides the
/// same clause, as it rides the binary directive since v61
/// (`CERTIFICATE_BINDING_FORMAT_VERSION`, roadmap WS6.7(b)). So does its
/// WS1.13 [`crate::proof::IslandEnvironment`]: the opaque
/// declaration bytes in the `clean_cic` term's byte-list spelling, then the
/// digest AS STORED (never recomputed here — a validator recomputes it from
/// the bytes and refuses a mismatch, so text must not repair one).
fn write_kernel_recheck(
    f: &mut fmt::Formatter<'_>,
    recheck: &crate::proof::CleanCicKernelRecheck,
) -> fmt::Result {
    // Exhaustive: a new field fails to compile here until it is spelled.
    let crate::proof::CleanCicKernelRecheck {
        module,
        theorems,
        anchor,
        allowed_axioms,
        binding,
    } = recheck;
    write!(f, "recheck module {module:?} anchor {anchor:?} theorems ")?;
    write_string_list(f, theorems)?;
    write!(f, " axioms ")?;
    write_string_list(f, allowed_axioms)?;
    if let Some(binding) = binding {
        let crate::proof::CertificateBinding {
            environment_digest,
            statement_digest,
            origin_module,
            source,
            callees,
            environment,
        } = binding.as_ref();
        write!(f, " binding env ")?;
        write_proof_digest(f, environment_digest)?;
        write!(f, " statement ")?;
        write_proof_digest(f, statement_digest)?;
        if let Some(origin) = origin_module {
            write!(f, " origin ")?;
            write_proof_digest(f, origin)?;
        }
        if let Some(source) = source {
            write!(f, " source {:?} ", source.decl)?;
            write_proof_digest(f, &source.closure_digest)?;
        }
        write!(f, " callees ")?;
        write_string_list(f, callees)?;
        if let Some(island) = environment {
            let crate::proof::IslandEnvironment {
                declarations,
                digest,
            } = island;
            write!(f, " island [")?;
            for (i, byte) in declarations.iter().enumerate() {
                if i > 0 {
                    write!(f, ", ")?;
                }
                write!(f, "{byte}")?;
            }
            write!(f, "] ")?;
            write_proof_digest(f, digest)?;
        }
    }
    Ok(())
}

/// WS4.5 (enum half): one `EnumLayoutDescriptor` as the `layout(..)` clause
/// of an enum definition, read back by `Parser::parse_enum_layout`.
///
/// ```text
/// layout(direct tag@0 size=24 align=8 offsets=[[8], [8, 16], []])
/// layout(niche untagged=1 variants=0..=0 start=4294967041 lane=u32@0 size=4 align=4 offsets=[[], [0]])
/// layout(untagged size=24 align=8 offsets=[[0]])
/// ```
///
/// EVERY field of the descriptor is spelled. The descriptor is documented as
/// NORMATIVE where present, so a spelling that carried only the legacy
/// `payload_offset_bits` / `payload_size_bits` projection of
/// `Module::enum_layout_shape` would carry the DERIVED view and drop the
/// authority. The offset lists are per variant in declaration order and per
/// field within a variant, exactly as the binary codec writes them; the tag
/// WIDTH is not spelled because it is not a descriptor field (it comes from
/// the enum's canonical tag repr), while the niche lane's width IS one and is
/// spelled as `lane=<repr>@<offset>`.
fn write_enum_layout(
    f: &mut fmt::Formatter<'_>,
    layout: &crate::ty::EnumLayoutDescriptor,
) -> fmt::Result {
    use crate::ty::{EnumLayoutDescriptor, EnumTagEncoding};
    // Exhaustive: a new descriptor field fails to compile here until it has a
    // spelling (or `text_loss::enum_layout_text_refusal` starts refusing it).
    let EnumLayoutDescriptor {
        encoding,
        size,
        align,
        variant_field_offsets,
    } = layout;
    f.write_str("layout(")?;
    match encoding {
        EnumTagEncoding::Direct { tag_offset } => write!(f, "direct tag@{tag_offset}")?,
        EnumTagEncoding::Niche {
            untagged_variant,
            niche_variants_start,
            niche_variants_end,
            niche_start,
            niche_offset,
            niche_ty,
        } => write!(
            f,
            "niche untagged={untagged_variant} variants={niche_variants_start}..={niche_variants_end} \
             start={niche_start} lane={niche_ty}@{niche_offset}"
        )?,
        EnumTagEncoding::Untagged => f.write_str("untagged")?,
        EnumTagEncoding::SingleInhabited { variant } => write!(f, "single inhabited={variant}")?,
    }
    write!(f, " size={size} align={align} offsets=[")?;
    for (i, offsets) in variant_field_offsets.iter().enumerate() {
        if i > 0 {
            f.write_str(", ")?;
        }
        f.write_str("[")?;
        for (j, offset) in offsets.iter().enumerate() {
            if j > 0 {
                f.write_str(", ")?;
            }
            write!(f, "{offset}")?;
        }
        f.write_str("]")?;
    }
    f.write_str("])")
}

fn write_func_ty<X: crate::level::Extension>(
    f: &mut fmt::Formatter<'_>,
    ft: &FuncTyG<X>,
) -> fmt::Result {
    write!(f, "(")?;
    for (i, param) in ft.params.iter().enumerate() {
        if i > 0 {
            write!(f, ", ")?;
        }
        write!(f, "{param}")?;
    }
    if ft.is_vararg {
        if !ft.params.is_empty() {
            write!(f, ", ")?;
        }
        write!(f, "...")?;
    }
    write!(f, ") -> (")?;
    for (i, ret) in ft.returns.iter().enumerate() {
        if i > 0 {
            write!(f, ", ")?;
        }
        write!(f, "{ret}")?;
    }
    write!(f, ")")
}

impl<X: crate::level::Extension> fmt::Display for crate::FunctionG<X> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use crate::{CallingConv, Linkage};
        let ft_idx = self.ty.index();
        if self.linkage != Linkage::External {
            write!(f, "{} ", self.linkage)?;
        }
        if self.calling_conv != CallingConv::C {
            write!(f, "{} ", self.calling_conv)?;
        }
        write!(f, "fn @")?;
        write_symbol(f, &self.name)?;
        write!(f, "(functy.{ft_idx})")?;
        writeln!(f, " {{")?;

        // Producer provenance (v23). Same `; #...` comment-directive syntax as
        // proofs/attrs, so pre-v23 parsers skip it as an unknown directive
        // instead of failing. Known producers print their bare token; the
        // `Other` escape prints as a quoted (Debug-escaped) string.
        if let Some(producer) = &self.producer {
            writeln!(f, "    ; {}: {producer}", directive::PRODUCER)?;
        }

        // Codegen license (v41). Printed only when a claim is MADE: an absent
        // directive decodes to `None` ("no licensing claim"), which is a
        // different thing from an explicit `ungated`, so the two must not
        // share a spelling.
        if let Some(gate) = &self.body_gate {
            writeln!(f, "    ; {}: {gate}", directive::BODY_GATE)?;
        }

        // Human definition path (v41). Quoted, because a def-path routinely
        // carries `<`, `>`, `,` and spaces that no bare-token grammar admits.
        if let Some(path) = &self.display_path {
            writeln!(f, "    ; {}: {path:?}", directive::DISPLAY_PATH)?;
        }

        // Separate-compilation contract (v18 / v41), WS4.4 (F-064). One
        // contiguous block in a FIXED order — `#summary` (proved bit and
        // formal names), then one line per `requires`, `ensures` and
        // `decreases` clause, then at most one `#backed-by`, then at most one
        // `#effects` (v59, WS1.14) — so the parser
        // can refuse any other arrangement and printer output has one
        // spelling. Absent summary prints nothing (`None` is not an empty
        // summary: `Some(FunctionSummary::default())` prints the header line).
        if let Some(summary) = &self.summary {
            write_function_summary(f, summary)?;
        }

        // Symbol attributes (v45, WS3.10). Each is printed only when it
        // differs from the pre-v45 default, so a legacy function's text is
        // unchanged. The section is a quoted (Debug-escaped) string — the same
        // escaping `#display-path` uses, which `read_quoted_string` inverts
        // exactly — because an arbitrary section name may carry `"`, `\`,
        // `;` or a newline and must survive the text round trip INJECTIVELY.
        if let Some(section) = &self.section {
            writeln!(f, "    ; {}: {section:?}", directive::SECTION)?;
        }
        if self.visibility != crate::Visibility::Default {
            writeln!(f, "    ; {}: {}", directive::VISIBILITY, self.visibility)?;
        }
        if self.retained {
            writeln!(f, "    ; {}: true", directive::RETAINED)?;
        }

        // Function-level proof annotations (finding B). Mirrors the
        // instruction-node `; #proof:` comment syntax; the parser reads these
        // back into `Function.proofs` before the first block.
        if !self.proofs.is_empty() {
            write!(f, "    ; {}:", directive::PROOF)?;
            for (i, p) in self.proofs.iter().enumerate() {
                if i > 0 {
                    write!(f, ",")?;
                }
                write!(f, " {p}")?;
            }
            writeln!(f)?;
        }

        // Function- and parameter-level optimization attributes (finding B).
        write_func_attrs(f, &self.attrs)?;

        // Debug value names (v32) and the lexical scope tree (v33). Same
        // `; #...` comment-directive syntax, so older parsers skip them.
        // Rendered because a debug-info field nobody can SEE is a field nobody
        // can check: these two lines are how the producer's output gets
        // inspected against built MIR without a hex dump.
        if let Some(names) = &self.value_names {
            write!(f, "    ; {}:", directive::NAMES)?;
            for (i, (v, n)) in names.iter().enumerate() {
                if i > 0 {
                    write!(f, ",")?;
                }
                // Names are arbitrary producer strings, not identifiers.
                // Debug quoting keeps commas, whitespace, and control
                // characters from changing the directive grammar.
                write!(f, " %{}={n:?}", v.index())?;
            }
            writeln!(f)?;
        }
        if let Some(scopes) = &self.scopes {
            for (i, sc) in scopes.iter().enumerate() {
                write!(f, "    ; {}: {i}", directive::SCOPE)?;
                match sc.parent {
                    None => write!(f, " root")?,
                    Some(p) => write!(f, " parent={p}")?,
                }
                if let Some(span) = &sc.span {
                    write!(f, " at {} {} {}", span.file, span.line, span.col)?;
                }
                // WS4.19 inlining chain link: the call site, then the callee
                // display path with the same Debug quoting `#names` uses, so
                // a path containing whitespace or a quote cannot change the
                // directive grammar.
                if let Some(link) = &sc.inlined_at {
                    write!(
                        f,
                        " inlined-at {} {} {} callee {:?}",
                        link.span.file, link.span.line, link.span.col, link.callee
                    )?;
                }
                writeln!(f)?;
            }
        }
        // v35 semantic source-loop/place provenance. Unlike the debug lines
        // above, these directives carry proof-relevant identity and therefore
        // round-trip every digest and binding field exactly.
        if let Some(provenance) = &self.source_provenance {
            writeln!(
                f,
                "    ; {}: schema {} compiler {:?} semantic {:?} binding {:?}",
                directive::SOURCE_PROVENANCE,
                provenance.schema,
                provenance.compiler_source_digest.to_string(),
                provenance.semantic_body_digest.to_string(),
                provenance.binding_digest.to_string(),
            )?;
            for source_loop in &provenance.loops {
                writeln!(
                    f,
                    "    ; {}: {} hir {} header {}",
                    directive::SOURCE_LOOP,
                    source_loop.source_loop_id,
                    source_loop.hir_local_id,
                    source_loop.header.index(),
                )?;
                for binding in &source_loop.bindings {
                    let (place, index) = match binding.place {
                        crate::SourcePlace::FunctionParameter { index } => {
                            ("function-param", index)
                        }
                        crate::SourcePlace::LoopParameter { index } => ("loop-param", index),
                    };
                    writeln!(
                        f,
                        "    ; {}: loop {} name {:?} hir {} {} {}",
                        directive::SOURCE_BINDING,
                        source_loop.source_loop_id,
                        binding.name,
                        binding.hir_local_id,
                        place,
                        index,
                    )?;
                }
            }
        }

        for block in &self.blocks {
            write!(f, "{block}")?;
        }

        writeln!(f, "}}")
    }
}

/// WS4.4 (F-064): a [`crate::FunctionSummary`] as the function-header block
///
/// ```text
///     ; #summary: proved|unproved params ["a", "b"]
///     ; #requires: formula ..
///     ; #ensures: formula ..
///     ; #decreases: formula ..
///     ; #backed-by: extern <import> "<symbol>" (none | obligation <id>)
///     ; #effects: reads <set> writes <set> allocates <bool> frees <bool> may_unwind <bool> io <bool>
/// ```
///
/// where `<set>` is `nothing`, `everything` or `places [<place>, ..]` and a
/// `<place>` is `param(N)` or `global(N)` (v59, WS1.14). Read back by
/// `Parser::parse_function`, which refuses a clause line with no preceding
/// `#summary`, an out-of-order or non-contiguous block, a second `#backed-by`
/// or `#effects`, and a place list that is not the ONE spelling of its set.
fn write_function_summary(
    f: &mut fmt::Formatter<'_>,
    summary: &crate::FunctionSummary,
) -> fmt::Result {
    // Exhaustive: a new `FunctionSummary` field fails to compile here until
    // it is given a directive (or a `TextLoss`).
    let crate::FunctionSummary {
        requires,
        ensures,
        params,
        proved,
        decreases,
        backed_by,
        effects,
    } = summary;
    write!(
        f,
        "    ; {}: {} params ",
        directive::SUMMARY,
        if *proved { "proved" } else { "unproved" }
    )?;
    write_string_list(f, params)?;
    writeln!(f)?;
    for (word, clauses) in [
        (directive::REQUIRES, requires),
        (directive::ENSURES, ensures),
        (directive::DECREASES, decreases),
    ] {
        for clause in clauses {
            write!(f, "    ; {word}: ")?;
            write_proof_formula(f, clause)?;
            writeln!(f)?;
        }
    }
    if let Some(reference) = backed_by {
        write!(f, "    ; {}: ", directive::BACKED_BY)?;
        write_extern_ref(f, reference)?;
        writeln!(f)?;
    }
    // v59 (WS1.14): absent prints nothing — `None` is UNRECORDED, and
    // `Some(EffectSummary::pure())` prints its `nothing` / `false` line.
    if let Some(effects) = effects {
        write!(f, "    ; {}: ", directive::EFFECTS)?;
        write_effect_summary(f, effects)?;
        writeln!(f)?;
    }
    Ok(())
}

/// v59 (WS1.14): `reads <set> writes <set> allocates <bool> frees <bool>
/// may_unwind <bool> io <bool>` — every field, in declaration order, so the
/// line has one spelling (the `#effects` directive's payload).
fn write_effect_summary(f: &mut fmt::Formatter<'_>, effects: &crate::EffectSummary) -> fmt::Result {
    // Exhaustive: a new `EffectSummary` field fails to compile here until it
    // is given a spelling.
    let crate::EffectSummary {
        reads,
        writes,
        allocates,
        frees,
        may_unwind,
        io,
    } = effects;
    write!(f, "reads ")?;
    write_effect_set(f, reads)?;
    write!(f, " writes ")?;
    write_effect_set(f, writes)?;
    write!(
        f,
        " allocates {allocates} frees {frees} may_unwind {may_unwind} io {io}"
    )
}

/// v59 (WS1.14): `nothing` | `everything` | `places [param(N), global(N), ..]`.
/// A non-canonical `Places` list is printed as it is; the parser refuses it,
/// exactly as every other decoder does.
fn write_effect_set(f: &mut fmt::Formatter<'_>, set: &crate::EffectSet) -> fmt::Result {
    match set {
        crate::EffectSet::Nothing => write!(f, "nothing"),
        crate::EffectSet::Everything => write!(f, "everything"),
        crate::EffectSet::Places(places) => {
            write!(f, "places [")?;
            for (i, place) in places.iter().enumerate() {
                if i > 0 {
                    write!(f, ", ")?;
                }
                match place {
                    crate::EffectPlace::ParamPointee { index } => write!(f, "param({index})")?,
                    crate::EffectPlace::Global(global) => {
                        write!(f, "global({})", global.index())?;
                    }
                }
            }
            write!(f, "]")
        }
    }
}

/// Write `FuncAttrs` (and per-parameter `ParamAttrs`) as `;`-comment lines so
/// the text form carries the same optimization hints the binary codec does
/// (finding B). Empty attrs emit nothing.
fn write_func_attrs(f: &mut fmt::Formatter<'_>, attrs: &crate::FuncAttrs) -> fmt::Result {
    let func_flags = [
        (attrs.readonly, "readonly"),
        (attrs.readnone, "readnone"),
        (attrs.inlinehint, "inlinehint"),
        (attrs.cold, "cold"),
        // v41.
        (attrs.naked, "naked"),
    ];
    if func_flags.iter().any(|(set, _)| *set) {
        write!(f, "    ; {}:", directive::ATTRS)?;
        for (set, name) in func_flags {
            if set {
                write!(f, " {name}")?;
            }
        }
        writeln!(f)?;
    }
    // v41: target features, on their own line so a feature name can never be
    // mistaken for an attribute flag.
    if !attrs.target_features.is_empty() {
        write!(f, "    ; {}:", directive::TARGET_FEATURES)?;
        for (i, feature) in attrs.target_features.iter().enumerate() {
            if i > 0 {
                write!(f, ",")?;
            }
            write!(f, " {feature:?}")?;
        }
        writeln!(f)?;
    }
    // v45: the RETURN slot, printed with the same grammar as a parameter's
    // so one reader covers both.
    if !attrs.ret.is_empty() {
        write!(f, "    ; {}:", directive::RET_ATTRS)?;
        write_slot_attrs(f, &attrs.ret)?;
        writeln!(f)?;
    }
    for (i, pa) in attrs.params.iter().enumerate() {
        // Interior defaults are reconstructed by the reader's positional
        // resize. The final row also records the table's exact length, even
        // when it has no slot facts: an absent row is not a recorded default.
        if pa.is_empty() && i + 1 != attrs.params.len() {
            continue;
        }
        write!(f, "    ; {} {i}:", directive::PARAM_ATTRS)?;
        if let Some(n) = pa.dereferenceable {
            write!(f, " dereferenceable({n})")?;
        }
        if pa.nonnull {
            write!(f, " nonnull")?;
        }
        if let Some(n) = pa.align {
            write!(f, " align({n})")?;
        }
        if pa.noalias {
            write!(f, " noalias")?;
        }
        if pa.readonly {
            write!(f, " readonly")?;
        }
        if pa.byval {
            write!(f, " byval")?;
        }
        if pa.sret {
            write!(f, " sret")?;
        }
        write_slot_abi_facts(f, pa)?;
        writeln!(f)?;
    }
    Ok(())
}

/// The v45 per-slot ABI facts (`ext`, `pass`), shared by the parameter and
/// return-slot lines. An unrecorded fact prints NOTHING — the absent
/// spelling is what `None` means.
fn write_slot_abi_facts(f: &mut fmt::Formatter<'_>, pa: &crate::ParamAttrs) -> fmt::Result {
    if let Some(token) = pa.ext.token() {
        write!(f, " {token}")?;
    }
    match &pa.pass {
        None => {}
        Some(crate::PassMode::Cast { pieces }) => {
            write!(f, " pass=cast(")?;
            for (i, piece) in pieces.iter().enumerate() {
                if i > 0 {
                    write!(f, ", ")?;
                }
                write!(f, "{piece}")?;
            }
            write!(f, ")")?;
        }
        Some(crate::PassMode::Indirect { on_stack }) => {
            write!(f, " pass=indirect({on_stack})")?;
        }
        Some(mode) => write!(f, " pass={}", mode.token())?,
    }
    Ok(())
}

/// Every attribute of one slot, in the `#param_attrs` order. Used for the
/// return slot, which has no positional index of its own.
fn write_slot_attrs(f: &mut fmt::Formatter<'_>, pa: &crate::ParamAttrs) -> fmt::Result {
    if let Some(n) = pa.dereferenceable {
        write!(f, " dereferenceable({n})")?;
    }
    if pa.nonnull {
        write!(f, " nonnull")?;
    }
    if let Some(n) = pa.align {
        write!(f, " align({n})")?;
    }
    if pa.noalias {
        write!(f, " noalias")?;
    }
    if pa.readonly {
        write!(f, " readonly")?;
    }
    if pa.byval {
        write!(f, " byval")?;
    }
    if pa.sret {
        write!(f, " sret")?;
    }
    write_slot_abi_facts(f, pa)
}

impl<X: crate::level::Extension> fmt::Display for crate::BlockG<X> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "bb{}", self.id.index())?;
        if !self.params.is_empty() {
            write!(f, "(")?;
            for (i, (val, ty)) in self.params.iter().enumerate() {
                if i > 0 {
                    write!(f, ", ")?;
                }
                write!(f, "%{}: {ty}", val.index())?;
            }
            write!(f, ")")?;
        }
        writeln!(f, ":")?;

        for node in &self.body {
            write!(f, "    ")?;
            write_instr_node(f, node)?;
            writeln!(f)?;
        }

        Ok(())
    }
}

fn write_instr_node<X: crate::level::Extension>(
    f: &mut fmt::Formatter<'_>,
    node: &InstrNodeG<X>,
) -> fmt::Result {
    if !node.results.is_empty() {
        for (i, r) in node.results.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "%{}", r.index())?;
        }
        write!(f, " = ")?;
    }

    write_inst(f, &node.inst)?;

    if !node.proofs.is_empty() {
        write!(f, "  ; {}:", directive::PROOF)?;
        for (i, p) in node.proofs.iter().enumerate() {
            if i > 0 {
                write!(f, ",")?;
            }
            write!(f, " {p}")?;
        }
    }

    // Per-call-site proof context (B5): the assumes/establishes obligation ids
    // a Call/CallIndirect carries. Emitted as a trailing comment clause so it
    // round-trips through text (finding C).
    if let Some(ctx) = &node.proof_context {
        write!(f, "  ; {}: assumes[", directive::PROOF_CTX)?;
        for (i, id) in ctx.assumes.iter().enumerate() {
            if i > 0 {
                write!(f, ",")?;
            }
            write!(f, "{}", id.index())?;
        }
        write!(f, "] establishes[")?;
        for (i, id) in ctx.establishes.iter().enumerate() {
            if i > 0 {
                write!(f, ",")?;
            }
            write!(f, "{}", id.index())?;
        }
        write!(f, "]")?;
    }

    // Source span (debug info): the file-table index, then the line (1-based,
    // as `lookup_char_pos` reports it) and the column (0-BASED — the producer
    // stores `CharPos.0` verbatim, so a `#loc` column is one less than the
    // 1-based column a debugger or `llvm-dwarfdump` prints). Emitted as a
    // trailing `;`-comment clause so it round-trips through text and older
    // parsers skip it (back-compat). The file index refers to the module
    // `file <i> "<path>"` table. Only emitted when the node carries a span, so
    // span-less nodes are byte-identical.
    if let Some(span) = &node.span {
        write!(
            f,
            "  ; {}: {} {} {}",
            directive::LOC,
            span.file,
            span.line,
            span.col
        )?;
    }
    // Lexical scope index (v33), into the enclosing function's `; #scope:` table.
    if let Some(scope) = node.scope {
        write!(f, "  ; {}: {scope}", directive::SCOPE)?;
    }

    Ok(())
}

fn val(id: &crate::value::ValueId) -> u32 {
    id.index()
}

/// The `, KIND` (plan item P, v52) and `, panic @func.E at LOC` (amendment
/// P, v54) clauses after an assert's condition; an `Unspecified` kind and an
/// absent site write nothing.
fn write_assert_kind_and_site(
    f: &mut fmt::Formatter<'_>,
    kind: &crate::inst::AssertKind,
    site: Option<&crate::inst::PanicSite>,
) -> fmt::Result {
    match kind {
        crate::inst::AssertKind::Unspecified => {}
        crate::inst::AssertKind::Overflow(op) => write!(f, ", overflow {}", op.name())?,
        crate::inst::AssertKind::BoundsCheck { index: a, len: b }
        | crate::inst::AssertKind::MisalignedPtr {
            required: a,
            found: b,
        } => write!(f, ", {} %{}, %{}", kind.keyword(), val(a), val(b))?,
        _ => write!(f, ", {}", kind.keyword())?,
    }
    if let Some(site) = site {
        write!(f, ", panic @func.{} at ", site.entry.index())?;
        match site.location {
            crate::inst::PanicLocation::Global(global) => write!(f, "@global.{}", global.index())?,
            crate::inst::PanicLocation::Value(value) => write!(f, "%{}", val(&value))?,
        }
    }
    Ok(())
}

fn write_inst<X: crate::level::Extension>(
    f: &mut fmt::Formatter<'_>,
    inst: &InstG<X>,
) -> fmt::Result {
    match inst {
        InstG::SeqMapAddK { ty, seq, k } => {
            write!(f, "seq_map_add_k {ty} %{}, {k}", val(seq))
        }
        InstG::SeqMapNot { ty, seq } => {
            write!(f, "seq_map_not {ty} %{}", val(seq))
        }
        InstG::SeqMap { ty, seq, fwd } => {
            write!(f, "seq_map {ty} %{}, @func.{}", val(seq), fwd.index())
        }
        InstG::BinOp { op, ty, lhs, rhs } => {
            write!(f, "{op} {ty} %{}, %{}", val(lhs), val(rhs))
        }
        InstG::UnOp { op, ty, operand } => {
            write!(f, "{op} {ty} %{}", val(operand))
        }
        InstG::Overflow { op, ty, lhs, rhs } => {
            write!(f, "{op} {ty} %{}, %{}", val(lhs), val(rhs))
        }
        InstG::ICmp { op, ty, lhs, rhs } => {
            write!(f, "icmp {op} {ty} %{}, %{}", val(lhs), val(rhs))
        }
        InstG::FCmp { op, ty, lhs, rhs } => {
            write!(f, "fcmp {op} {ty} %{}, %{}", val(lhs), val(rhs))
        }
        InstG::Cast {
            op,
            src_ty,
            dst_ty,
            operand,
        } => {
            write!(f, "{op} {src_ty} %{} to {dst_ty}", val(operand))
        }
        InstG::Load {
            ty,
            ptr,
            volatile,
            align,
        } => {
            if *volatile {
                write!(f, "volatile ")?;
            }
            write!(f, "load {ty}, ptr %{}", val(ptr))?;
            if let Some(a) = align {
                write!(f, ", align {a}")?;
            }
            Ok(())
        }
        InstG::Store {
            ty,
            ptr,
            value,
            volatile,
            align,
        } => {
            if *volatile {
                write!(f, "volatile ")?;
            }
            write!(f, "store {ty} %{}, ptr %{}", val(value), val(ptr))?;
            if let Some(a) = align {
                write!(f, ", align {a}")?;
            }
            Ok(())
        }
        InstG::Drop { ty, ptr } => write!(f, "drop {ty}, %{}", val(ptr)),
        InstG::Alloca { ty, count, align } => {
            write!(f, "alloca {ty}")?;
            if let Some(c) = count {
                write!(f, ", %{}", val(c))?;
            }
            if let Some(a) = align {
                write!(f, ", align {a}")?;
            }
            Ok(())
        }
        InstG::HeapAlloc {
            ty,
            count,
            align,
            origin,
        } => {
            let origin = match origin {
                AllocOrigin::RustHeap => "rust_heap",
                AllocOrigin::SwiftHeap => "swift_heap",
                AllocOrigin::CMalloc => "c_malloc",
                AllocOrigin::CleanHeap => "clean_heap",
            };
            write!(f, "heap_alloc {origin} {ty}")?;
            if let Some(c) = count {
                write!(f, ", %{}", val(c))?;
            }
            if let Some(a) = align {
                write!(f, ", align {a}")?;
            }
            Ok(())
        }
        InstG::GEP {
            pointee_ty,
            base,
            indices,
            inbounds,
        } => {
            let ib = if *inbounds { " inbounds" } else { "" };
            write!(f, "gep{ib} {pointee_ty}, ptr %{}", val(base))?;
            for idx in indices {
                write!(f, ", %{}", val(idx))?;
            }
            Ok(())
        }
        InstG::PtrData { ptr_ty, ptr } => {
            write!(f, "ptr_data {ptr_ty} %{}", val(ptr))
        }
        InstG::PtrMetadata {
            ptr_ty,
            metadata_ty,
            ptr,
        } => {
            write!(f, "ptr_metadata {ptr_ty} %{} to {metadata_ty}", val(ptr))
        }
        InstG::PtrFromParts {
            ptr_ty,
            metadata_ty,
            data,
            metadata,
        } => {
            write!(
                f,
                "ptr_from_parts {ptr_ty} ptr %{}, {metadata_ty} %{}",
                val(data),
                val(metadata)
            )
        }
        InstG::AtomicLoad { ty, ptr, ordering } => {
            write!(f, "atomic_load {ordering} {ty}, ptr %{}", val(ptr))
        }
        InstG::AtomicStore {
            ty,
            ptr,
            value,
            ordering,
        } => write!(
            f,
            "atomic_store {ordering} {ty} %{}, ptr %{}",
            val(value),
            val(ptr)
        ),
        InstG::AtomicRMW {
            op,
            ty,
            ptr,
            value,
            ordering,
        } => write!(
            f,
            "atomicrmw {op} {ordering} {ty} ptr %{}, %{}",
            val(ptr),
            val(value)
        ),
        InstG::CmpXchg {
            ty,
            ptr,
            expected,
            desired,
            success,
            failure,
            weak,
        } => write!(
            f,
            // Trust (crystal D3): LLVM's spelling, `cmpxchg weak`. A strong compare-exchange
            // prints exactly as it always has.
            "cmpxchg {}{ty} ptr %{}, %{}, %{} {success} {failure}",
            if *weak { "weak " } else { "" },
            val(ptr),
            val(expected),
            val(desired),
        ),
        InstG::Fence { ordering } => write!(f, "fence {ordering}"),
        // WS3.20 bulk memory. The `overlap` flag rides after the opcode like
        // `gep inbounds`, so the memmove form is one word longer, never a
        // different opcode.
        InstG::MemCopy {
            dst,
            src,
            bytes,
            overlap,
        } => {
            let ov = if *overlap { " overlap" } else { "" };
            write!(
                f,
                "memcopy{ov} ptr %{}, ptr %{}, %{}",
                val(dst),
                val(src),
                val(bytes)
            )
        }
        InstG::MemSet { dst, byte, bytes } => {
            write!(
                f,
                "memset ptr %{}, %{}, %{}",
                val(dst),
                val(byte),
                val(bytes)
            )
        }
        InstG::Br { target, args } => {
            write!(f, "br bb{}", target.index())?;
            write_block_args(f, args)
        }
        InstG::CondBr {
            cond,
            then_target,
            then_args,
            else_target,
            else_args,
        } => {
            write!(f, "condbr %{}, bb{}", val(cond), then_target.index())?;
            write_block_args(f, then_args)?;
            write!(f, ", bb{}", else_target.index())?;
            write_block_args(f, else_args)
        }
        InstG::Switch {
            value,
            default,
            default_args,
            cases,
            exhaustive_enum_unreachable,
        } => {
            write!(f, "switch %{} [", val(value))?;
            for case in cases {
                write!(f, " {}: bb{}", case.value, case.target.index())?;
                write_block_args(f, &case.args)?;
            }
            write!(f, " default: bb{}", default.index())?;
            write_block_args(f, default_args)?;
            write!(f, " ]")?;
            // WS4.5: the producer's exhaustiveness hint (binary v15), spelled
            // only when set so every switch without it keeps its text.
            if *exhaustive_enum_unreachable {
                write!(f, " exhaustive")?;
            }
            Ok(())
        }
        InstG::Call { callee, args } | InstG::CallCannotUnwind { callee, args } => {
            let opcode = if matches!(inst, InstG::CallCannotUnwind { .. }) {
                "call_cannot_unwind"
            } else {
                "call"
            };
            write!(f, "{opcode} @func.{}", callee.index())?;
            write!(f, "(")?;
            for (i, a) in args.iter().enumerate() {
                if i > 0 {
                    write!(f, ", ")?;
                }
                write!(f, "%{}", val(a))?;
            }
            write!(f, ")")
        }
        InstG::CallIndirect {
            callee,
            sig,
            args,
            calling_conv,
        }
        | InstG::CallIndirectCannotUnwind {
            callee,
            sig,
            args,
            calling_conv,
        } => {
            let opcode = if matches!(inst, InstG::CallIndirectCannotUnwind { .. }) {
                "call_indirect_cannot_unwind"
            } else {
                "call_indirect"
            };
            write!(f, "{opcode} %{}(functy.{})(", val(callee), sig.index())?;
            for (i, a) in args.iter().enumerate() {
                if i > 0 {
                    write!(f, ", ")?;
                }
                write!(f, "%{}", val(a))?;
            }
            write!(f, ")")?;
            // Emit the callee ABI only when non-default, so existing text is stable.
            if *calling_conv != crate::CallingConv::default() {
                write!(f, " cc={calling_conv}")?;
            }
            Ok(())
        }
        InstG::Return { values } => {
            write!(f, "ret")?;
            for (i, v) in values.iter().enumerate() {
                if i > 0 {
                    write!(f, ",")?;
                }
                write!(f, " %{}", val(v))?;
            }
            Ok(())
        }
        // WS3.5: `make_aggregate TY [variant N] (%a, %b)`. The variant clause
        // is present exactly for a `Ty::Enum` (the validator enforces that),
        // so its absence is the non-enum spelling, never a defaulted 0.
        InstG::MakeAggregate {
            ty,
            variant,
            fields,
        } => {
            write!(f, "make_aggregate {ty}")?;
            if let Some(variant) = variant {
                write!(f, " variant {variant}")?;
            }
            write!(f, " (")?;
            for (i, field) in fields.iter().enumerate() {
                if i > 0 {
                    write!(f, ", ")?;
                }
                write!(f, "%{}", val(field))?;
            }
            write!(f, ")")
        }
        InstG::MakeClosure { ty, func, captures } => {
            write!(f, "make_closure closure.{} @func.{} (", ty.0, func.0)?;
            for (i, capture) in captures.iter().enumerate() {
                if i > 0 {
                    write!(f, ", ")?;
                }
                write!(f, "%{}", val(capture))?;
            }
            write!(f, ")")
        }
        InstG::ArraySplat { ty, value } => write!(f, "array_splat {ty} %{}", val(value)),
        InstG::ExtractField {
            ty,
            aggregate,
            field,
        } => write!(f, "extractfield {ty} %{}, {field}", val(aggregate)),
        InstG::InsertField {
            ty,
            aggregate,
            field,
            value,
        } => write!(
            f,
            "insertfield {ty} %{}, {field}, %{}",
            val(aggregate),
            val(value)
        ),
        InstG::ExtractElement { ty, array, index } => {
            write!(f, "extractelement {ty} %{}, %{}", val(array), val(index))
        }
        InstG::InsertElement {
            ty,
            array,
            index,
            value,
        } => write!(
            f,
            "insertelement {ty} %{}, %{}, %{}",
            val(array),
            val(index),
            val(value)
        ),
        InstG::Const { ty, value: c } => write!(f, "const {ty} {c}"),
        InstG::NullPtr => write!(f, "null ptr"),
        InstG::GlobalAddr { global } => write!(f, "global_addr @global.{}", global.index()),
        InstG::Undef { ty } => write!(f, "undef {ty}"),
        InstG::Assume { cond } => write!(f, "assume %{}", val(cond)),
        InstG::Assert { cond, kind, site } => {
            write!(f, "assert %{}", val(cond))?;
            write_assert_kind_and_site(f, kind, site.as_ref())
        }
        InstG::Unreachable => write!(f, "unreachable"),
        InstG::Copy { ty, operand } => write!(f, "copy {ty} %{}", val(operand)),
        InstG::Select {
            ty,
            cond,
            then_val,
            else_val,
        } => write!(
            f,
            "select {ty} %{}, %{}, %{}",
            val(cond),
            val(then_val),
            val(else_val)
        ),
        // Borrow instructions
        InstG::Borrow { ptr } => write!(f, "borrow %{}", val(ptr)),
        InstG::BorrowMut { ptr } => write!(f, "borrow_mut %{}", val(ptr)),
        InstG::EndBorrow { borrow_ptr } => write!(f, "end_borrow %{}", val(borrow_ptr)),
        // ARC instructions
        InstG::Retain { ptr } => write!(f, "retain %{}", val(ptr)),
        InstG::Release { ptr } => write!(f, "release %{}", val(ptr)),
        InstG::IsUnique { ptr } => write!(f, "is_unique %{}", val(ptr)),
        // Heap deallocation
        InstG::Dealloc { ptr } => write!(f, "dealloc %{}", val(ptr)),
        // Binding frames (typed SSA frames for quantifier lowering)
        InstG::OpenFrame { def } => {
            write!(f, "open_frame #{} {:?} {{", def.id.index(), def.name)?;
            for (i, slot) in def.slots.iter().enumerate() {
                if i > 0 {
                    write!(f, ", ")?;
                }
                write!(f, "{}: {}", slot.name, slot.ty)?;
            }
            write!(f, "}}")
        }
        InstG::BindSlot { frame, slot, value } => {
            write!(f, "bind_slot %{}, {}, %{}", val(frame), slot, val(value))
        }
        InstG::LoadSlot { frame, slot, ty } => {
            write!(f, "load_slot {} %{}, {}", ty, val(frame), slot)
        }
        InstG::CloseFrame { frame } => write!(f, "close_frame %{}", val(frame)),
        // Coroutine suspend: `coro_suspend %frame, <state_slot>, <next_state>, %value`
        InstG::CoroSuspend {
            frame,
            state_slot,
            next_state,
            value,
        } => write!(
            f,
            "coro_suspend %{}, {}, {}, %{}",
            val(frame),
            state_slot,
            next_state,
            val(value)
        ),
        // Exception handling.
        // `invoke @func.N(%a, ..) to bb<normal>(%n, ..) unwind bb<unwind>`
        InstG::Invoke {
            callee,
            args,
            normal_dest,
            normal_args,
            unwind_dest,
        } => {
            write!(f, "invoke @func.{}(", callee.index())?;
            for (i, a) in args.iter().enumerate() {
                if i > 0 {
                    write!(f, ", ")?;
                }
                write!(f, "%{}", val(a))?;
            }
            write!(f, ") to bb{}(", normal_dest.index())?;
            for (i, a) in normal_args.iter().enumerate() {
                if i > 0 {
                    write!(f, ", ")?;
                }
                write!(f, "%{}", val(a))?;
            }
            write!(f, ") unwind bb{}", unwind_dest.index())
        }
        // Amendment D, Part 2: `invoke_indirect %f(functy.K)(%a, ..) [cc=X]
        // to bbN(%n, ..) unwind bbM` -- `call_indirect`'s spelling (the
        // convention only when non-default), then `invoke`'s successors.
        InstG::InvokeIndirect {
            callee,
            sig,
            args,
            calling_conv,
            normal_dest,
            normal_args,
            unwind_dest,
        } => {
            write!(
                f,
                "invoke_indirect %{}(functy.{})(",
                val(callee),
                sig.index()
            )?;
            for (i, a) in args.iter().enumerate() {
                if i > 0 {
                    write!(f, ", ")?;
                }
                write!(f, "%{}", val(a))?;
            }
            write!(f, ")")?;
            if *calling_conv != crate::CallingConv::default() {
                write!(f, " cc={calling_conv}")?;
            }
            write!(f, " to bb{}(", normal_dest.index())?;
            for (i, a) in normal_args.iter().enumerate() {
                if i > 0 {
                    write!(f, ", ")?;
                }
                write!(f, "%{}", val(a))?;
            }
            write!(f, ") unwind bb{}", unwind_dest.index())
        }
        // `assert_invoke %c[, KIND], panic @func.E at LOC to bbN(..) unwind bbM`
        InstG::AssertInvoke {
            cond,
            kind,
            site,
            normal_dest,
            normal_args,
            unwind_dest,
        } => {
            write!(f, "assert_invoke %{}", val(cond))?;
            write_assert_kind_and_site(f, kind, Some(site))?;
            write!(f, " to bb{}(", normal_dest.index())?;
            for (i, a) in normal_args.iter().enumerate() {
                if i > 0 {
                    write!(f, ", ")?;
                }
                write!(f, "%{}", val(a))?;
            }
            write!(f, ") unwind bb{}", unwind_dest.index())
        }
        // Amendment D: `drop_invoke <ty>, %p to bbN(%a, ..) unwind bbM`.
        InstG::DropInvoke {
            ty,
            ptr,
            normal_dest,
            normal_args,
            unwind_dest,
        } => {
            write!(
                f,
                "drop_invoke {ty}, %{} to bb{}(",
                val(ptr),
                normal_dest.index()
            )?;
            for (i, a) in normal_args.iter().enumerate() {
                if i > 0 {
                    write!(f, ", ")?;
                }
                write!(f, "%{}", val(a))?;
            }
            write!(f, ") unwind bb{}", unwind_dest.index())
        }
        // `landingpad [cleanup] catch <i0>, <i1>, ..`
        InstG::LandingPad {
            is_cleanup,
            catch_type_indices,
        } => {
            write!(f, "landingpad")?;
            if *is_cleanup {
                write!(f, " cleanup")?;
            }
            if !catch_type_indices.is_empty() {
                write!(f, " catch")?;
                for (i, idx) in catch_type_indices.iter().enumerate() {
                    if i > 0 {
                        write!(f, ",")?;
                    }
                    write!(f, " {idx}")?;
                }
            }
            Ok(())
        }
        // `resume %exn`
        InstG::Resume { exn } => write!(f, "resume %{}", val(exn)),
        // Dialect op: `dialect_op <dialect>.<op>(%0, %1) -> (i32, bool) [attr=val] v<version>`
        InstG::DialectOp(op) => write_dialect_op(f, op),
    }
}

fn write_dialect_op(f: &mut fmt::Formatter<'_>, op: &crate::dialect::DialectInst) -> fmt::Result {
    write!(f, "dialect_op {}.{}", op.dialect, op.op)?;
    write!(f, "(")?;
    for (i, v) in op.operands.iter().enumerate() {
        if i > 0 {
            write!(f, ", ")?;
        }
        write!(f, "%{}", val(v))?;
    }
    write!(f, ")")?;
    if !op.result_tys.is_empty() {
        write!(f, " -> ")?;
        if op.result_tys.len() == 1 {
            write!(f, "{}", op.result_tys[0])?;
        } else {
            write!(f, "(")?;
            for (i, t) in op.result_tys.iter().enumerate() {
                if i > 0 {
                    write!(f, ", ")?;
                }
                write!(f, "{}", t)?;
            }
            write!(f, ")")?;
        }
    }
    for entry in &op.attrs {
        write!(f, " [{}=", entry.name)?;
        write_attr_value(f, &entry.value)?;
        write!(f, "]")?;
    }
    if op.version != 1 {
        write!(f, " v{}", op.version)?;
    }
    Ok(())
}

fn write_attr_value(f: &mut fmt::Formatter<'_>, v: &crate::dialect::AttrValue) -> fmt::Result {
    use crate::dialect::AttrValue;
    match v {
        AttrValue::I64(x) => write!(f, "i64:{}", x),
        AttrValue::U64(x) => write!(f, "u64:{}", x),
        // F64 attrs must round-trip every bit pattern, including NaN and ±inf
        // (finding F). The bare `f64:NaN`/`f64:inf` spellings are not parseable
        // by `read_f64`, so non-finite values are emitted as an exact bit
        // pattern (`f64:bits(<u64>)`); finite values keep the readable
        // shortest-round-trip decimal that always contains `.` or `e`.
        AttrValue::F64(x) => {
            if x.is_finite() {
                write!(f, "f64:")?;
                write_constant_float(f, *x)
            } else {
                write!(f, "f64:bits({})", x.to_bits())
            }
        }
        AttrValue::Bool(x) => write!(f, "bool:{}", x),
        // Strings are emitted with our own escape scheme (NOT Rust `{:?}`,
        // which spells control chars as `\u{..}` that the parser cannot
        // decode). `write_escaped_string` round-trips every char including
        // `\r`, `\0`, and other control characters (finding F).
        AttrValue::Str(s) => {
            write!(f, "str:")?;
            write_escaped_string(f, s)
        }
        AttrValue::Bytes(b) => {
            write!(f, "bytes:{}:", b.len())?;
            for byte in b {
                write!(f, "{:02x}", byte)?;
            }
            Ok(())
        }
        AttrValue::Ty(t) => write!(f, "ty:{}", t),
    }
}

/// WS4.3: write a definition-site SYMBOL — bare when the parser's
/// bare-identifier alphabet reads it back, otherwise as a quoted, escaped
/// string that `Parser::read_symbol` decodes.
///
/// ONE SPELLING PER CONSTRUCT (SPEC §3): a bare-able name is ALWAYS printed
/// bare, and the parser refuses its quoted spelling, so printer output and
/// parse are a bijection. This is also what keeps the change golden-stable —
/// every corpus name is already in the bare alphabet, so existing goldens are
/// byte-identical.
///
/// Keeping the bare form for bare-able names is what makes this change
/// golden-stable: every module whose names were already spellable prints
/// byte-identically, so no existing golden moves. Only names that previously
/// made the whole module REFUSE text encoding gain a spelling.
fn write_symbol(f: &mut fmt::Formatter<'_>, name: &str) -> fmt::Result {
    if crate::text_loss::is_bare_ident(name) {
        write!(f, "{name}")
    } else {
        write_escaped_string(f, name)
    }
}

/// Write `s` as a double-quoted string with an escape scheme the text parser's
/// `read_quoted_string` fully decodes: `\\`, `\"`, `\n`, `\t`, `\r`, `\0`, and
/// `\u{HEX}` for any other control character. Unlike Rust's `{:?}`, every
/// emitted escape round-trips back to the original `char` (finding F).
fn write_escaped_string(f: &mut fmt::Formatter<'_>, s: &str) -> fmt::Result {
    write!(f, "\"")?;
    for ch in s.chars() {
        match ch {
            '\\' => write!(f, "\\\\")?,
            '"' => write!(f, "\\\"")?,
            '\n' => write!(f, "\\n")?,
            '\t' => write!(f, "\\t")?,
            '\r' => write!(f, "\\r")?,
            '\0' => write!(f, "\\0")?,
            c if c.is_control() => write!(f, "\\u{{{:x}}}", c as u32)?,
            c => write!(f, "{c}")?,
        }
    }
    write!(f, "\"")
}

fn write_block_args(f: &mut fmt::Formatter<'_>, args: &[crate::value::ValueId]) -> fmt::Result {
    if !args.is_empty() {
        write!(f, "(")?;
        for (i, a) in args.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            write!(f, "%{}", val(a))?;
        }
        write!(f, ")")?;
    }
    Ok(())
}

/// Pretty-print a `Constant::Float` payload in the text IR.
///
/// Invariant (required by the text-round-trip property — issues #45 and #47):
/// the emitted token must be re-parseable *as a float*, not as an integer.
/// Concretely:
///
/// - Finite floats are emitted via `{:?}`, which Rust guarantees is the
///   shortest decimal string that round-trips back to the same `f64` and
///   always contains either a decimal point (`42.0`, `-0.0`) or an
///   exponent (`1e300`, `-1.5e-10`). Because the string always contains
///   `.` or `e`, `parse_number` takes the float branch and never the i128
///   branch, eliminating the display/parse ambiguity.
/// - The special values `+inf`, `-inf`, and `NaN` cannot be written as a
///   bare decimal literal. We emit explicit tokens that the parser also
///   accepts (`inf`, `-inf`, `NaN`). Rust's default `{:?}` spells these
///   identically — we only force `-inf` so sign is preserved.
fn write_constant_float(f: &mut fmt::Formatter<'_>, v: f64) -> fmt::Result {
    if v.is_nan() {
        write!(f, "NaN")
    } else if v.is_infinite() {
        if v.is_sign_negative() {
            write!(f, "-inf")
        } else {
            write!(f, "inf")
        }
    } else {
        // Finite. `{:?}` always yields a form containing `.` or `e`.
        write!(f, "{:?}", v)
    }
}

fn write_proof_evidence(
    f: &mut fmt::Formatter<'_>,
    evidence: &crate::proof::ProofEvidence,
) -> fmt::Result {
    use crate::proof::ProofEvidence;
    match evidence {
        ProofEvidence::Trusted(reason) => write!(f, "trusted {:?}", reason),
        ProofEvidence::KaniHarness(name) => write!(f, "kani {:?}", name),
        ProofEvidence::LeanProof(term) => write!(f, "lean {:?}", term),
        ProofEvidence::SmtProof(data) => {
            write!(f, "smt [")?;
            for (i, byte) in data.iter().enumerate() {
                if i > 0 {
                    write!(f, ", ")?;
                }
                write!(f, "{byte}")?;
            }
            write!(f, "]")
        }
        ProofEvidence::GammaCrownBound {
            epsilon,
            verified_layers,
        } => {
            write!(f, "gamma_crown {epsilon} {verified_layers}")
        }
        ProofEvidence::TranslationValidation {
            rule_name,
            smt_hash,
        } => {
            write!(f, "translation_validation {:?} [", rule_name)?;
            for (i, byte) in smt_hash.iter().enumerate() {
                if i > 0 {
                    write!(f, ", ")?;
                }
                write!(f, "{byte}")?;
            }
            write!(f, "]")
        }
        ProofEvidence::InheritedFromCallee {
            callee,
            obligation,
            external,
        } => {
            write!(f, "inherited {} {}", callee.index(), obligation.index())?;
            // v41. Carried in the TEXT form deliberately: this is proof
            // AUTHORITY, and dropping it would turn a cross-crate inheritance
            // into a local one on a text round trip — silently, and in the
            // permissive direction.
            if let Some(reference) = external {
                write!(f, " ")?;
                write_extern_ref(f, reference)?;
            }
            Ok(())
        }
        ProofEvidence::CleanCic {
            term,
            context,
            lineage,
            // WS4.4 (F-070): carried as a trailing `recheck ..` clause below.
            kernel_recheck,
        } => {
            write!(f, "clean_cic [")?;
            for (i, byte) in term.iter().enumerate() {
                if i > 0 {
                    write!(f, ", ")?;
                }
                write!(f, "{byte}")?;
            }
            write!(f, "] [")?;
            for (i, byte) in context.iter().enumerate() {
                if i > 0 {
                    write!(f, ", ")?;
                }
                write!(f, "{byte}")?;
            }
            let alg = match lineage.algorithm {
                crate::proof::ProofDigestAlgorithm::Sha256 => "sha256",
                crate::proof::ProofDigestAlgorithm::TrustIrStableV1 => "trust_ir-stable-v1",
            };
            write!(f, "] {alg:?} [")?;
            for (i, byte) in lineage.bytes.iter().enumerate() {
                if i > 0 {
                    write!(f, ", ")?;
                }
                write!(f, "{byte}")?;
            }
            write!(f, "]")?;
            if let Some(recheck) = kernel_recheck {
                write!(f, " ")?;
                write_kernel_recheck(f, recheck)?;
            }
            Ok(())
        }
    }
}

impl<X: crate::level::Extension> fmt::Display for crate::ConstantG<X> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ConstantG::Int(v) => write!(f, "{v}"),
            // v24: prints the TRUE unsigned value (the point of the 128-bit-
            // faithful carrier). Canonicality (value > i128::MAX) means the
            // parser reads the literal back into the same variant by VALUE —
            // `parse(display(x)) == x` holds with no type context.
            ConstantG::U128(v) => write!(f, "{v}"),
            // v25 Bytes: hex payload keeps the text form injective and
            // parser-trivial for EVERY byte value (no escape grammar); the
            // utf8 claim is spelled in the token so it round-trips.
            ConstantG::Bytes { data, utf8 } => {
                write!(f, "{}<", if *utf8 { "utf8bytes" } else { "bytes" })?;
                for b in data {
                    write!(f, "{b:02x}")?;
                }
                write!(f, ">")
            }
            // Float literals must always be unambiguously distinguishable
            // from integer literals in the text form, otherwise the parser
            // reads `Constant::Float(42.0)` back as `Constant::Int(42)` (see
            // issue #45). `{:?}` on f64 emits the shortest decimal that
            // round-trips and always contains either `.` or `e`, so it is
            // a canonical, lossless, parser-friendly representation for
            // every finite f64 (whole-valued floats emit `.0`, very-large
            // magnitudes emit scientific notation like `1e300`, addressing
            // issue #47). Non-finite values use explicit tokens that the
            // parser also recognizes.
            ConstantG::Float(v) => write_constant_float(f, *v),
            ConstantG::Bool(b) => write!(f, "{b}"),
            ConstantG::Aggregate(elems) => {
                write!(f, "{{ ")?;
                for (i, e) in elems.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{e}")?;
                }
                write!(f, " }}")
            }
            ConstantG::Array(elems) => {
                write!(f, "array[ ")?;
                for (i, e) in elems.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{e}")?;
                }
                write!(f, " ]")
            }
            // v50: `LEN` copies of one element, written ONCE — the text is as
            // long as the element, whatever the length.
            ConstantG::Splat { elem, len } => write!(f, "splat[ {elem}; {len} ]"),
            ConstantG::Vector(elems) => {
                write!(f, "vec[ ")?;
                for (i, e) in elems.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{e}")?;
                }
                write!(f, " ]")
            }
            ConstantG::Sequence(elems) => {
                write!(f, "seq[ ")?;
                for (i, e) in elems.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{e}")?;
                }
                write!(f, " ]")
            }
            ConstantG::Set(elems) => {
                write!(f, "set{{ ")?;
                for (i, e) in elems.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{e}")?;
                }
                write!(f, " }}")
            }
            ConstantG::Record(fields) => {
                write!(f, "record{{ ")?;
                for (i, (name, val)) in fields.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{name} = {val}")?;
                }
                write!(f, " }}")
            }
            ConstantG::Closure { func, captures } => {
                if captures.is_empty() {
                    write!(f, "closure<func.{}>{{ }}", func.index())
                } else {
                    write!(f, "closure<func.{}>{{ ", func.index())?;
                    for (i, c) in captures.iter().enumerate() {
                        if i > 0 {
                            write!(f, ", ")?;
                        }
                        write!(f, "{c}")?;
                    }
                    write!(f, " }}")
                }
            }
            ConstantG::FnDef(func) => write!(f, "fndef<func.{}>", func.index()),
            ConstantG::SymbolAddr { symbol, addend } => {
                if *addend == 0 {
                    write!(f, "symaddr<{symbol}>")
                } else {
                    write!(f, "symaddr<{symbol} + {addend}>")
                }
            }
            ConstantG::PhantomData => write!(f, "phantomdata"),
            // Crystal lane (E3b, v49): an unwritten struct/tuple lane, legal only as a direct element
            // of an `Inst::Const` aggregate (the validator's placement rule).
            ConstantG::Uninit => write!(f, "uninit"),
            ConstantG::Ext(e) => e.fmt_ext(f),
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::constant::Constant;
    use crate::inst::*;
    use crate::node::InstrNode;
    use crate::proof::ProofAnnotation;
    use crate::ty::{FieldDef, FuncTy, StructDef, Ty};
    use crate::value::{BlockId, FuncId, StructId, ValueId};
    use crate::{Block, Function, Module};

    fn v(n: u32) -> ValueId {
        ValueId::new(n)
    }

    fn b(n: u32) -> BlockId {
        BlockId::new(n)
    }

    /// Build a simple add function: fn add(i64, i64) -> i64 { a + b }
    fn build_add_module() -> Module {
        let mut module = Module::new("test");
        let ft_id = module
            .add_func_type(FuncTy {
                params: vec![Ty::I64, Ty::I64],
                returns: vec![Ty::I64],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");

        let mut func = Function::new(FuncId::new(0), "add", ft_id, b(0));
        let mut block = Block::new(b(0));
        // %0, %1 are params
        block.params.push((v(0), Ty::I64));
        block.params.push((v(1), Ty::I64));
        // %2 = add i64 %0, %1
        block.body.push(
            InstrNode::new(Inst::BinOp {
                op: BinOp::Add,
                ty: Ty::I64,
                lhs: v(0),
                rhs: v(1),
            })
            .with_result(v(2)),
        );
        // ret %2
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![v(2)] }));
        func.blocks.push(block);
        module
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");
        module
    }

    #[test]
    fn display_module_header() {
        let module = build_add_module();
        let output = format!("{}", module);
        assert!(output.contains("; TrustIr text format v1"));
        assert!(output.contains("module \"test\""));
    }

    #[test]
    fn display_function_name_and_type() {
        let module = build_add_module();
        let output = format!("{}", module);
        assert!(output.contains("fn @add(functy.0)"));
    }

    #[test]
    fn display_block_with_params() {
        let module = build_add_module();
        let output = format!("{}", module);
        assert!(output.contains("bb0(%0: i64, %1: i64):"));
    }

    #[test]
    fn display_add_instruction() {
        let module = build_add_module();
        let output = format!("{}", module);
        assert!(output.contains("%2 = add i64 %0, %1"));
    }

    #[test]
    fn display_ret_instruction() {
        let module = build_add_module();
        let output = format!("{}", module);
        assert!(output.contains("ret %2"));
    }

    #[test]
    fn display_struct_def() {
        let mut module = Module::new("structs");
        module.add_struct(StructDef {
            id: StructId::new(0),
            name: "Point".to_string(),
            fields: vec![
                FieldDef {
                    name: "x".to_string(),
                    ty: Ty::F64,
                    offset: Some(0),
                },
                FieldDef {
                    name: "y".to_string(),
                    ty: Ty::F64,
                    offset: Some(8),
                },
            ],
            size: Some(16),
            align: Some(8),

            repr: Default::default(),
            origin: None,
        });
        let output = format!("{}", module);
        assert!(output.contains("struct @Point"));
        // WS4.5: fields carry `name: ty` and, when present, ` @offset`.
        assert!(output.contains("x: f64 @0, y: f64 @8"), "{output}");
        assert!(output.contains("size=16"));
        assert!(output.contains("align=8"));
        // Explicit id trailer preserves the StructId across a text round trip.
        assert!(output.contains("id=0"));
    }

    #[test]
    fn display_const_instruction() {
        let mut module = Module::new("consts");
        let ft = module
            .add_func_type(FuncTy {
                params: vec![],
                returns: vec![Ty::I32],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut func = Function::new(FuncId::new(0), "get42", ft, b(0));
        let mut block = Block::new(b(0));
        block.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(42),
            })
            .with_result(v(0)),
        );
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![v(0)] }));
        func.blocks.push(block);
        module
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");

        let output = format!("{}", module);
        assert!(output.contains("const i32 42"));
    }

    #[test]
    fn display_load_store() {
        let mut module = Module::new("mem");
        let ft = module
            .add_func_type(FuncTy {
                params: vec![Ty::Ptr],
                returns: vec![],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut func = Function::new(FuncId::new(0), "mem_ops", ft, b(0));
        let mut block = Block::new(b(0));
        block.params.push((v(0), Ty::Ptr));
        // %1 = load i32, ptr %0
        block.body.push(
            InstrNode::new(Inst::Load {
                ty: Ty::I32,
                ptr: v(0),
                volatile: false,
                align: None,
            })
            .with_result(v(1)),
        );
        // store i32 %1, ptr %0
        block.body.push(InstrNode::new(Inst::Store {
            ty: Ty::I32,
            ptr: v(0),
            value: v(1),
            volatile: false,
            align: None,
        }));
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        func.blocks.push(block);
        module
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");

        let output = format!("{}", module);
        assert!(output.contains("load i32, ptr %0"));
        assert!(output.contains("store i32 %1, ptr %0"));
    }

    #[test]
    fn display_alloca() {
        let mut module = Module::new("alloca_test");
        let ft = module
            .add_func_type(FuncTy {
                params: vec![],
                returns: vec![],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut func = Function::new(FuncId::new(0), "f", ft, b(0));
        let mut block = Block::new(b(0));
        block.body.push(
            InstrNode::new(Inst::Alloca {
                ty: Ty::I32,
                count: None,
                align: None,
            })
            .with_result(v(0)),
        );
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        func.blocks.push(block);
        module
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");

        let output = format!("{}", module);
        assert!(output.contains("alloca i32"));
    }

    #[test]
    fn display_gep() {
        let mut module = Module::new("gep_test");
        let ft = module
            .add_func_type(FuncTy {
                params: vec![Ty::Ptr],
                returns: vec![],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut func = Function::new(FuncId::new(0), "f", ft, b(0));
        let mut block = Block::new(b(0));
        block.params.push((v(0), Ty::Ptr));
        block.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(0),
            })
            .with_result(v(1)),
        );
        block.body.push(
            InstrNode::new(Inst::GEP {
                pointee_ty: Ty::I32,
                base: v(0),
                indices: vec![v(1)],
                inbounds: false,
            })
            .with_result(v(2)),
        );
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        func.blocks.push(block);
        module
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");

        let output = format!("{}", module);
        assert!(output.contains("gep i32, ptr %0, %1"));
    }

    #[test]
    fn display_branch_instructions() {
        let mut module = Module::new("branches");
        let ft = module
            .add_func_type(FuncTy {
                params: vec![Ty::Bool],
                returns: vec![Ty::I32],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut func = Function::new(FuncId::new(0), "branch", ft, b(0));

        // bb0: entry
        let mut bb0 = Block::new(b(0));
        bb0.params.push((v(0), Ty::Bool));
        bb0.body.push(InstrNode::new(Inst::CondBr {
            cond: v(0),
            then_target: b(1),
            then_args: vec![],
            else_target: b(2),
            else_args: vec![],
        }));
        func.blocks.push(bb0);

        // bb1: then
        let mut bb1 = Block::new(b(1));
        bb1.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(1),
            })
            .with_result(v(1)),
        );
        bb1.body.push(InstrNode::new(Inst::Br {
            target: b(3),
            args: vec![v(1)],
        }));
        func.blocks.push(bb1);

        // bb2: else
        let mut bb2 = Block::new(b(2));
        bb2.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I32,
                value: Constant::Int(0),
            })
            .with_result(v(2)),
        );
        bb2.body.push(InstrNode::new(Inst::Br {
            target: b(3),
            args: vec![v(2)],
        }));
        func.blocks.push(bb2);

        // bb3: merge
        let mut bb3 = Block::new(b(3));
        bb3.params.push((v(3), Ty::I32));
        bb3.body
            .push(InstrNode::new(Inst::Return { values: vec![v(3)] }));
        func.blocks.push(bb3);

        module
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");

        let output = format!("{}", module);
        assert!(output.contains("condbr %0, bb1, bb2"));
        assert!(output.contains("br bb3(%1)"));
        assert!(output.contains("br bb3(%2)"));
        assert!(output.contains("bb3(%3: i32):"));
    }

    #[test]
    fn display_call() {
        let mut module = Module::new("call_test");
        let ft = module
            .add_func_type(FuncTy {
                params: vec![Ty::I32, Ty::I32],
                returns: vec![Ty::I32],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut func = Function::new(FuncId::new(0), "caller", ft, b(0));
        let mut block = Block::new(b(0));
        block.params.push((v(0), Ty::I32));
        block.params.push((v(1), Ty::I32));
        block.body.push(
            InstrNode::new(Inst::Call {
                callee: FuncId::new(1),
                args: vec![v(0), v(1)],
            })
            .with_result(v(2)),
        );
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![v(2)] }));
        func.blocks.push(block);
        module
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");

        let output = format!("{}", module);
        assert!(output.contains("call @func.1(%0, %1)"));
    }

    #[test]
    fn display_cast() {
        let mut module = Module::new("cast_test");
        let ft = module
            .add_func_type(FuncTy {
                params: vec![Ty::I32],
                returns: vec![Ty::I64],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut func = Function::new(FuncId::new(0), "widen", ft, b(0));
        let mut block = Block::new(b(0));
        block.params.push((v(0), Ty::I32));
        block.body.push(
            InstrNode::new(Inst::Cast {
                op: CastOp::SExt,
                src_ty: Ty::I32,
                dst_ty: Ty::I64,
                operand: v(0),
            })
            .with_result(v(1)),
        );
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![v(1)] }));
        func.blocks.push(block);
        module
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");

        let output = format!("{}", module);
        assert!(output.contains("sext i32 %0 to i64"));
    }

    #[test]
    fn display_icmp() {
        let mut module = Module::new("icmp_test");
        let ft = module
            .add_func_type(FuncTy {
                params: vec![Ty::I32, Ty::I32],
                returns: vec![Ty::Bool],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut func = Function::new(FuncId::new(0), "cmp", ft, b(0));
        let mut block = Block::new(b(0));
        block.params.push((v(0), Ty::I32));
        block.params.push((v(1), Ty::I32));
        block.body.push(
            InstrNode::new(Inst::ICmp {
                op: ICmpOp::Slt,
                ty: Ty::I32,
                lhs: v(0),
                rhs: v(1),
            })
            .with_result(v(2)),
        );
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![v(2)] }));
        func.blocks.push(block);
        module
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");

        let output = format!("{}", module);
        assert!(output.contains("icmp slt i32 %0, %1"));
    }

    #[test]
    fn display_proof_annotation() {
        let mut module = Module::new("proofs");
        let ft = module
            .add_func_type(FuncTy {
                params: vec![Ty::Ptr],
                returns: vec![Ty::I32],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut func = Function::new(FuncId::new(0), "safe_load", ft, b(0));
        let mut block = Block::new(b(0));
        block.params.push((v(0), Ty::Ptr));
        block.body.push(
            InstrNode::new(Inst::Load {
                ty: Ty::I32,
                ptr: v(0),
                volatile: false,
                align: None,
            })
            .with_result(v(1))
            .with_proof(ProofAnnotation::InBounds)
            .with_proof(ProofAnnotation::NotNull),
        );
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![v(1)] }));
        func.blocks.push(block);
        module
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");

        let output = format!("{}", module);
        assert!(output.contains("#proof:"));
        assert!(output.contains("in_bounds"));
        assert!(output.contains("not_null"));
    }

    #[test]
    fn display_null_ptr() {
        let mut module = Module::new("null");
        let ft = module
            .add_func_type(FuncTy {
                params: vec![],
                returns: vec![Ty::Ptr],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut func = Function::new(FuncId::new(0), "get_null", ft, b(0));
        let mut block = Block::new(b(0));
        block
            .body
            .push(InstrNode::new(Inst::NullPtr).with_result(v(0)));
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![v(0)] }));
        func.blocks.push(block);
        module
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");

        let output = format!("{}", module);
        assert!(output.contains("null ptr"));
    }

    #[test]
    fn display_unreachable() {
        let mut module = Module::new("unr");
        let ft = module
            .add_func_type(FuncTy {
                params: vec![],
                returns: vec![],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut func = Function::new(FuncId::new(0), "panic", ft, b(0));
        let mut block = Block::new(b(0));
        block.body.push(InstrNode::new(Inst::Unreachable));
        func.blocks.push(block);
        module
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");

        let output = format!("{}", module);
        assert!(output.contains("unreachable"));
    }

    #[test]
    fn display_atomic_operations() {
        let mut module = Module::new("atomics");
        let ft = module
            .add_func_type(FuncTy {
                params: vec![Ty::Ptr],
                returns: vec![],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut func = Function::new(FuncId::new(0), "atomic_ops", ft, b(0));
        let mut block = Block::new(b(0));
        block.params.push((v(0), Ty::Ptr));
        block.body.push(
            InstrNode::new(Inst::AtomicLoad {
                ty: Ty::I64,
                ptr: v(0),
                ordering: Ordering::Acquire,
            })
            .with_result(v(1)),
        );
        block.body.push(InstrNode::new(Inst::AtomicStore {
            ty: Ty::I64,
            ptr: v(0),
            value: v(1),
            ordering: Ordering::Release,
        }));
        block.body.push(InstrNode::new(Inst::Fence {
            ordering: Ordering::SeqCst,
        }));
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        func.blocks.push(block);
        module
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");

        let output = format!("{}", module);
        assert!(output.contains("atomic_load acquire i64, ptr %0"));
        assert!(output.contains("atomic_store release i64 %1, ptr %0"));
        assert!(output.contains("fence seq_cst"));
    }

    #[test]
    fn display_switch() {
        let mut module = Module::new("switch");
        let ft = module
            .add_func_type(FuncTy {
                params: vec![Ty::I32],
                returns: vec![],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut func = Function::new(FuncId::new(0), "sw", ft, b(0));
        let mut bb0 = Block::new(b(0));
        bb0.params.push((v(0), Ty::I32));
        bb0.body.push(InstrNode::new(Inst::Switch {
            value: v(0),
            default: b(2),
            default_args: vec![],
            cases: vec![SwitchCase {
                value: Constant::Int(1),
                target: b(1),
                args: vec![],
            }],
            exhaustive_enum_unreachable: false,
        }));
        func.blocks.push(bb0);
        let mut bb1 = Block::new(b(1));
        bb1.body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        func.blocks.push(bb1);
        let mut bb2 = Block::new(b(2));
        bb2.body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        func.blocks.push(bb2);
        module
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");

        let output = format!("{}", module);
        assert!(output.contains("switch %0"));
        assert!(output.contains("1: bb1"));
        assert!(output.contains("default: bb2"));
    }

    #[test]
    fn display_multiple_functions() {
        let mut module = Module::new("multi");
        let ft = module
            .add_func_type(FuncTy {
                params: vec![],
                returns: vec![],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        for i in 0..3 {
            let mut func = Function::new(FuncId::new(i), format!("func_{i}"), ft, b(0));
            let mut block = Block::new(b(0));
            block
                .body
                .push(InstrNode::new(Inst::Return { values: vec![] }));
            func.blocks.push(block);
            module
                .try_add_function(func)
                .expect("Module::try_add_function: test fixture");
        }
        let output = format!("{}", module);
        assert!(output.contains("fn @func_0"));
        assert!(output.contains("fn @func_1"));
        assert!(output.contains("fn @func_2"));
    }

    #[test]
    fn display_overflow_instruction() {
        let mut module = Module::new("overflow");
        let ft = module
            .add_func_type(FuncTy {
                params: vec![Ty::I32, Ty::I32],
                returns: vec![Ty::I32, Ty::Bool],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut func = Function::new(FuncId::new(0), "checked_add", ft, b(0));
        let mut block = Block::new(b(0));
        block.params.push((v(0), Ty::I32));
        block.params.push((v(1), Ty::I32));
        let node = InstrNode::new(Inst::Overflow {
            op: OverflowOp::AddOverflow,
            ty: Ty::I32,
            lhs: v(0),
            rhs: v(1),
        })
        .with_result(v(2))
        .with_result(v(3));
        block.body.push(node);
        block.body.push(InstrNode::new(Inst::Return {
            values: vec![v(2), v(3)],
        }));
        func.blocks.push(block);
        module
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");

        let output = format!("{}", module);
        assert!(output.contains("add.overflow i32 %0, %1"));
        assert!(output.contains("%2, %3 ="));
    }

    #[test]
    fn display_select() {
        let mut module = Module::new("select");
        let ft = module
            .add_func_type(FuncTy {
                params: vec![Ty::Bool, Ty::I32, Ty::I32],
                returns: vec![Ty::I32],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut func = Function::new(FuncId::new(0), "sel", ft, b(0));
        let mut block = Block::new(b(0));
        block.params.push((v(0), Ty::Bool));
        block.params.push((v(1), Ty::I32));
        block.params.push((v(2), Ty::I32));
        block.body.push(
            InstrNode::new(Inst::Select {
                ty: Ty::I32,
                cond: v(0),
                then_val: v(1),
                else_val: v(2),
            })
            .with_result(v(3)),
        );
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![v(3)] }));
        func.blocks.push(block);
        module
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");

        let output = format!("{}", module);
        assert!(output.contains("select i32 %0, %1, %2"));
    }

    // --- NEW DISPLAY TESTS ---

    #[test]
    fn display_copy_instruction() {
        let mut module = Module::new("copy_test");
        let ft = module
            .add_func_type(FuncTy {
                params: vec![Ty::I32],
                returns: vec![Ty::I32],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut func = Function::new(FuncId::new(0), "cp", ft, b(0));
        let mut block = Block::new(b(0));
        block.params.push((v(0), Ty::I32));
        block.body.push(
            InstrNode::new(Inst::Copy {
                ty: Ty::I32,
                operand: v(0),
            })
            .with_result(v(1)),
        );
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![v(1)] }));
        func.blocks.push(block);
        module
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");

        let output = format!("{}", module);
        assert!(output.contains("copy i32 %0"));
    }

    #[test]
    fn display_undef_instruction() {
        let mut module = Module::new("undef_test");
        let ft = module
            .add_func_type(FuncTy {
                params: vec![],
                returns: vec![Ty::I64],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut func = Function::new(FuncId::new(0), "f", ft, b(0));
        let mut block = Block::new(b(0));
        block
            .body
            .push(InstrNode::new(Inst::Undef { ty: Ty::I64 }).with_result(v(0)));
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![v(0)] }));
        func.blocks.push(block);
        module
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");

        let output = format!("{}", module);
        assert!(output.contains("undef i64"));
    }

    #[test]
    fn display_assume_instruction() {
        let mut module = Module::new("assume_test");
        let ft = module
            .add_func_type(FuncTy {
                params: vec![Ty::Bool],
                returns: vec![],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut func = Function::new(FuncId::new(0), "f", ft, b(0));
        let mut block = Block::new(b(0));
        block.params.push((v(0), Ty::Bool));
        block.body.push(InstrNode::new(Inst::Assume { cond: v(0) }));
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        func.blocks.push(block);
        module
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");

        let output = format!("{}", module);
        assert!(output.contains("assume %0"));
    }

    #[test]
    fn display_assert_instruction() {
        let mut module = Module::new("assert_test");
        let ft = module
            .add_func_type(FuncTy {
                params: vec![Ty::Bool],
                returns: vec![],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut func = Function::new(FuncId::new(0), "f", ft, b(0));
        let mut block = Block::new(b(0));
        block.params.push((v(0), Ty::Bool));
        block.body.push(InstrNode::new(Inst::Assert {
            cond: v(0),
            kind: crate::inst::AssertKind::Unspecified,
            site: None,
        }));
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        func.blocks.push(block);
        module
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");

        let output = format!("{}", module);
        assert!(output.contains("assert %0"));
    }

    #[test]
    fn display_fcmp_instruction() {
        let mut module = Module::new("fcmp_test");
        let ft = module
            .add_func_type(FuncTy {
                params: vec![Ty::F64, Ty::F64],
                returns: vec![Ty::Bool],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut func = Function::new(FuncId::new(0), "fcmp_f", ft, b(0));
        let mut block = Block::new(b(0));
        block.params.push((v(0), Ty::F64));
        block.params.push((v(1), Ty::F64));
        block.body.push(
            InstrNode::new(Inst::FCmp {
                op: FCmpOp::OEq,
                ty: Ty::F64,
                lhs: v(0),
                rhs: v(1),
            })
            .with_result(v(2)),
        );
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![v(2)] }));
        func.blocks.push(block);
        module
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");

        let output = format!("{}", module);
        assert!(output.contains("fcmp oeq f64 %0, %1"));
    }

    #[test]
    fn display_cmpxchg_instruction() {
        let mut module = Module::new("cmpxchg_test");
        let ft = module
            .add_func_type(FuncTy {
                params: vec![Ty::Ptr, Ty::I64, Ty::I64],
                returns: vec![],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut func = Function::new(FuncId::new(0), "cas", ft, b(0));
        let mut block = Block::new(b(0));
        block.params.push((v(0), Ty::Ptr));
        block.params.push((v(1), Ty::I64));
        block.params.push((v(2), Ty::I64));
        block.body.push(
            InstrNode::new(Inst::CmpXchg {
                ty: Ty::I64,
                ptr: v(0),
                expected: v(1),
                desired: v(2),
                success: Ordering::SeqCst,
                failure: Ordering::Acquire,
                weak: false,
            })
            .with_result(v(3)),
        );
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        func.blocks.push(block);
        module
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");

        let output = format!("{}", module);
        assert!(output.contains("cmpxchg i64 ptr %0, %1, %2 seq_cst acquire"));
    }

    #[test]
    fn display_atomicrmw_instruction() {
        let mut module = Module::new("rmw_test");
        let ft = module
            .add_func_type(FuncTy {
                params: vec![Ty::Ptr, Ty::I64],
                returns: vec![Ty::I64],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut func = Function::new(FuncId::new(0), "rmw", ft, b(0));
        let mut block = Block::new(b(0));
        block.params.push((v(0), Ty::Ptr));
        block.params.push((v(1), Ty::I64));
        block.body.push(
            InstrNode::new(Inst::AtomicRMW {
                op: AtomicRMWOp::Add,
                ty: Ty::I64,
                ptr: v(0),
                value: v(1),
                ordering: Ordering::AcqRel,
            })
            .with_result(v(2)),
        );
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![v(2)] }));
        func.blocks.push(block);
        module
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");

        let output = format!("{}", module);
        assert!(output.contains("atomicrmw add acq_rel i64 ptr %0, %1"));
    }

    #[test]
    fn display_call_indirect_instruction() {
        let mut module = Module::new("calli_test");
        let ft_callee = module
            .add_func_type(FuncTy {
                params: vec![Ty::I32],
                returns: vec![Ty::I32],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let ft = module
            .add_func_type(FuncTy {
                params: vec![Ty::Ptr, Ty::I32],
                returns: vec![Ty::I32],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut func = Function::new(FuncId::new(0), "indirect", ft, b(0));
        let mut block = Block::new(b(0));
        block.params.push((v(0), Ty::Ptr));
        block.params.push((v(1), Ty::I32));
        block.body.push(
            InstrNode::new(Inst::CallIndirect {
                callee: v(0),
                sig: ft_callee,
                args: vec![v(1)],

                calling_conv: crate::CallingConv::C,
            })
            .with_result(v(2)),
        );
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![v(2)] }));
        func.blocks.push(block);
        module
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");

        let output = format!("{}", module);
        assert!(output.contains("call_indirect %0(functy.0)(%1)"));
    }

    #[test]
    fn display_extract_element_instruction() {
        let mut module = Module::new("ee_test");
        let ft = module
            .add_func_type(FuncTy {
                params: vec![Ty::Ptr, Ty::I64],
                returns: vec![Ty::I32],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut func = Function::new(FuncId::new(0), "ee", ft, b(0));
        let mut block = Block::new(b(0));
        block.params.push((v(0), Ty::Ptr));
        block.params.push((v(1), Ty::I64));
        block.body.push(
            InstrNode::new(Inst::ExtractElement {
                ty: Ty::I32,
                array: v(0),
                index: v(1),
            })
            .with_result(v(2)),
        );
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![v(2)] }));
        func.blocks.push(block);
        module
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");

        let output = format!("{}", module);
        assert!(output.contains("extractelement i32 %0, %1"));
    }

    #[test]
    fn display_insert_element_instruction() {
        let mut module = Module::new("ie_test");
        let ft = module
            .add_func_type(FuncTy {
                params: vec![Ty::Ptr, Ty::I64, Ty::I32],
                returns: vec![Ty::Ptr],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut func = Function::new(FuncId::new(0), "ie", ft, b(0));
        let mut block = Block::new(b(0));
        block.params.push((v(0), Ty::Ptr));
        block.params.push((v(1), Ty::I64));
        block.params.push((v(2), Ty::I32));
        block.body.push(
            InstrNode::new(Inst::InsertElement {
                ty: Ty::I32,
                array: v(0),
                index: v(1),
                value: v(2),
            })
            .with_result(v(3)),
        );
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![v(3)] }));
        func.blocks.push(block);
        module
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");

        let output = format!("{}", module);
        assert!(output.contains("insertelement i32 %0, %1, %2"));
    }

    #[test]
    fn display_insert_field_instruction() {
        let mut module = Module::new("if_test");
        let sid = StructId::new(0);
        module.add_struct(StructDef {
            id: sid,
            name: "S".to_string(),
            fields: vec![FieldDef {
                name: "x".to_string(),
                ty: Ty::I32,
                offset: Some(0),
            }],
            size: Some(4),
            align: Some(4),

            repr: Default::default(),
            origin: None,
        });
        let ft = module
            .add_func_type(FuncTy {
                params: vec![Ty::Struct(sid), Ty::I32],
                returns: vec![Ty::Struct(sid)],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut func = Function::new(FuncId::new(0), "set_field", ft, b(0));
        let mut block = Block::new(b(0));
        block.params.push((v(0), Ty::Struct(sid)));
        block.params.push((v(1), Ty::I32));
        block.body.push(
            InstrNode::new(Inst::InsertField {
                ty: Ty::Struct(sid),
                aggregate: v(0),
                field: 0,
                value: v(1),
            })
            .with_result(v(2)),
        );
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![v(2)] }));
        func.blocks.push(block);
        module
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");

        let output = format!("{}", module);
        assert!(output.contains("insertfield struct.0 %0, 0, %1"));
    }

    #[test]
    fn display_float_binops() {
        let mut module = Module::new("fbinops");
        let ft = module
            .add_func_type(FuncTy {
                params: vec![Ty::F64, Ty::F64],
                returns: vec![Ty::F64],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut func = Function::new(FuncId::new(0), "float_ops", ft, b(0));
        let mut block = Block::new(b(0));
        block.params.push((v(0), Ty::F64));
        block.params.push((v(1), Ty::F64));

        // fadd
        block.body.push(
            InstrNode::new(Inst::BinOp {
                op: BinOp::FAdd,
                ty: Ty::F64,
                lhs: v(0),
                rhs: v(1),
            })
            .with_result(v(2)),
        );
        // fsub
        block.body.push(
            InstrNode::new(Inst::BinOp {
                op: BinOp::FSub,
                ty: Ty::F64,
                lhs: v(0),
                rhs: v(1),
            })
            .with_result(v(3)),
        );
        // fmul
        block.body.push(
            InstrNode::new(Inst::BinOp {
                op: BinOp::FMul,
                ty: Ty::F64,
                lhs: v(0),
                rhs: v(1),
            })
            .with_result(v(4)),
        );
        // fdiv
        block.body.push(
            InstrNode::new(Inst::BinOp {
                op: BinOp::FDiv,
                ty: Ty::F64,
                lhs: v(0),
                rhs: v(1),
            })
            .with_result(v(5)),
        );
        // frem
        block.body.push(
            InstrNode::new(Inst::BinOp {
                op: BinOp::FRem,
                ty: Ty::F64,
                lhs: v(0),
                rhs: v(1),
            })
            .with_result(v(6)),
        );
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![v(2)] }));
        func.blocks.push(block);
        module
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");

        let output = format!("{}", module);
        assert!(output.contains("fadd f64 %0, %1"));
        assert!(output.contains("fsub f64 %0, %1"));
        assert!(output.contains("fmul f64 %0, %1"));
        assert!(output.contains("fdiv f64 %0, %1"));
        assert!(output.contains("frem f64 %0, %1"));
    }

    #[test]
    fn display_unop_fneg_and_not() {
        let mut module = Module::new("unops");
        let ft = module
            .add_func_type(FuncTy {
                params: vec![Ty::F64, Ty::I32],
                returns: vec![],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut func = Function::new(FuncId::new(0), "unary_ops", ft, b(0));
        let mut block = Block::new(b(0));
        block.params.push((v(0), Ty::F64));
        block.params.push((v(1), Ty::I32));
        block.body.push(
            InstrNode::new(Inst::UnOp {
                op: UnOp::FNeg,
                ty: Ty::F64,
                operand: v(0),
            })
            .with_result(v(2)),
        );
        block.body.push(
            InstrNode::new(Inst::UnOp {
                op: UnOp::Not,
                ty: Ty::I32,
                operand: v(1),
            })
            .with_result(v(3)),
        );
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        func.blocks.push(block);
        module
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");

        let output = format!("{}", module);
        assert!(output.contains("fneg f64 %0"));
        assert!(output.contains("not i32 %1"));
    }

    #[test]
    fn display_all_cast_ops() {
        let mut module = Module::new("casts");
        let ft = module
            .add_func_type(FuncTy {
                params: vec![Ty::I64, Ty::F64, Ty::Ptr],
                returns: vec![],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut func = Function::new(FuncId::new(0), "all_casts", ft, b(0));
        let mut block = Block::new(b(0));
        block.params.push((v(0), Ty::I64));
        block.params.push((v(1), Ty::F64));
        block.params.push((v(2), Ty::Ptr));

        let cast_specs: Vec<(CastOp, Ty, Ty, u32, &str)> = vec![
            (CastOp::Trunc, Ty::I64, Ty::I32, 0, "trunc i64 %0 to i32"),
            (CastOp::ZExt, Ty::I32, Ty::I64, 0, "zext i32 %0 to i64"),
            (
                CastOp::FPTrunc,
                Ty::F64,
                Ty::F32,
                1,
                "fptrunc f64 %1 to f32",
            ),
            (CastOp::FPExt, Ty::F32, Ty::F64, 1, "fpext f32 %1 to f64"),
            (CastOp::FPToUI, Ty::F64, Ty::I64, 1, "fptoui f64 %1 to i64"),
            (CastOp::FPToSI, Ty::F64, Ty::I64, 1, "fptosi f64 %1 to i64"),
            (CastOp::UIToFP, Ty::I64, Ty::F64, 0, "uitofp i64 %0 to f64"),
            (CastOp::SIToFP, Ty::I64, Ty::F64, 0, "sitofp i64 %0 to f64"),
            (
                CastOp::PtrToInt,
                Ty::Ptr,
                Ty::I64,
                2,
                "ptrtoint ptr %2 to i64",
            ),
            (
                CastOp::IntToPtr,
                Ty::I64,
                Ty::Ptr,
                0,
                "inttoptr i64 %0 to ptr",
            ),
            (
                CastOp::Bitcast,
                Ty::I64,
                Ty::F64,
                0,
                "bitcast i64 %0 to f64",
            ),
        ];

        for (result_id, (op, src_ty, dst_ty, operand_idx, _)) in (3u32..).zip(cast_specs.iter()) {
            block.body.push(
                InstrNode::new(Inst::Cast {
                    op: *op,
                    src_ty: src_ty.clone(),
                    dst_ty: dst_ty.clone(),
                    operand: v(*operand_idx),
                })
                .with_result(v(result_id)),
            );
        }
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        func.blocks.push(block);
        module
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");

        let output = format!("{}", module);
        for (_, _, _, _, expected) in &cast_specs {
            assert!(
                output.contains(expected),
                "missing display for cast: {expected}\nfull output:\n{output}"
            );
        }
    }

    #[test]
    fn display_alloca_with_count() {
        let mut module = Module::new("alloca_count");
        let ft = module
            .add_func_type(FuncTy {
                params: vec![],
                returns: vec![],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut func = Function::new(FuncId::new(0), "f", ft, b(0));
        let mut block = Block::new(b(0));
        block.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(10),
            })
            .with_result(v(0)),
        );
        block.body.push(
            InstrNode::new(Inst::Alloca {
                ty: Ty::I32,
                count: Some(v(0)),
                align: None,
            })
            .with_result(v(1)),
        );
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        func.blocks.push(block);
        module
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");

        let output = format!("{}", module);
        assert!(output.contains("alloca i32, %0"));
    }

    #[test]
    fn display_constant_bool() {
        let mut module = Module::new("cbool");
        let ft = module
            .add_func_type(FuncTy {
                params: vec![],
                returns: vec![Ty::Bool],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut func = Function::new(FuncId::new(0), "f", ft, b(0));
        let mut block = Block::new(b(0));
        block.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::Bool,
                value: Constant::Bool(true),
            })
            .with_result(v(0)),
        );
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![v(0)] }));
        func.blocks.push(block);
        module
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");

        let output = format!("{}", module);
        assert!(output.contains("const bool true"));
    }

    #[test]
    fn display_constant_float() {
        let mut module = Module::new("cfloat");
        let ft = module
            .add_func_type(FuncTy {
                params: vec![],
                returns: vec![Ty::F64],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut func = Function::new(FuncId::new(0), "f", ft, b(0));
        let mut block = Block::new(b(0));
        block.body.push(
            InstrNode::new(Inst::Const {
                ty: Ty::F64,
                value: Constant::Float(1.25),
            })
            .with_result(v(0)),
        );
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![v(0)] }));
        func.blocks.push(block);
        module
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");

        let output = format!("{}", module);
        assert!(output.contains("const f64 1.25"));
    }

    #[test]
    fn display_constant_aggregate() {
        let agg = Constant::Aggregate(vec![Constant::Int(1), Constant::Int(2), Constant::Int(3)]);
        let output = format!("{}", agg);
        assert_eq!(output, "{ 1, 2, 3 }");
    }

    #[test]
    fn display_constant_nested_aggregate() {
        let inner = Constant::Aggregate(vec![Constant::Int(10), Constant::Int(20)]);
        let outer = Constant::Aggregate(vec![inner, Constant::Bool(false)]);
        let output = format!("{}", outer);
        assert_eq!(output, "{ { 10, 20 }, false }");
    }

    #[test]
    fn display_constant_large_integer() {
        let large = Constant::Int(i128::MAX);
        let output = format!("{}", large);
        assert_eq!(output, format!("{}", i128::MAX));
    }

    #[test]
    fn display_constant_negative_float() {
        let neg = Constant::Float(-2.5);
        let output = format!("{}", neg);
        assert!(output.contains("-2.5"));
    }

    // --- NEW: issue #45 / #47 display invariants ---

    /// Every finite `Constant::Float` display must contain either a
    /// decimal point or an exponent marker. Otherwise the parser reads
    /// it back as `Constant::Int`. Regression for issues #45 and #47.
    #[test]
    fn display_constant_float_always_has_decimal_or_exponent() {
        let cases: &[f64] = &[
            0.0,
            -0.0,
            1.0,
            -1.0,
            42.0,
            -43075.0,
            i64::MAX as f64,
            i64::MIN as f64,
            1.25,
            -2.5,
            0.5,
            1e300,
            -1e300,
            1e-300,
            -1e-300,
            1.5e38,
            -3.5e38,
            f64::MIN_POSITIVE,
            f64::MAX,
            f64::MIN,
            f64::EPSILON,
        ];
        for &v in cases {
            let out = format!("{}", Constant::Float(v));
            assert!(
                out.contains('.') || out.contains('e') || out.contains('E'),
                "Constant::Float({v}) displayed as {out:?} — lacks '.' or exponent, \
                 would be misparsed as Constant::Int"
            );
        }
    }

    /// Whole-valued `Constant::Float` must render with a trailing `.0`
    /// (or scientific notation). Regression for issue #45.
    #[test]
    fn display_constant_float_whole_valued_has_decimal() {
        assert_eq!(format!("{}", Constant::Float(0.0)), "0.0");
        assert_eq!(format!("{}", Constant::Float(-0.0)), "-0.0");
        assert_eq!(format!("{}", Constant::Float(1.0)), "1.0");
        assert_eq!(format!("{}", Constant::Float(-1.0)), "-1.0");
        assert_eq!(format!("{}", Constant::Float(42.0)), "42.0");
        assert_eq!(format!("{}", Constant::Float(-43075.0)), "-43075.0");
    }

    /// Large-magnitude finite floats render in a form the parser
    /// accepts (decimal point or exponent). Regression for issue #47.
    #[test]
    fn display_constant_float_large_magnitude() {
        // The exact textual form is platform-independent because `{:?}`
        // on f64 is the shortest-round-trip decimal: Rust guarantees it
        // matches across targets.
        assert_eq!(format!("{}", Constant::Float(1e300)), "1e300");
        assert_eq!(format!("{}", Constant::Float(-1e300)), "-1e300");
        assert_eq!(format!("{}", Constant::Float(1e-300)), "1e-300");
    }

    /// Non-finite floats use explicit parser-friendly tokens.
    #[test]
    fn display_constant_float_non_finite() {
        assert_eq!(format!("{}", Constant::Float(f64::INFINITY)), "inf");
        assert_eq!(format!("{}", Constant::Float(f64::NEG_INFINITY)), "-inf");
        assert_eq!(format!("{}", Constant::Float(f64::NAN)), "NaN");
    }

    #[test]
    fn display_all_fcmp_ops() {
        let ops_and_names = [
            (FCmpOp::OEq, "oeq"),
            (FCmpOp::ONe, "one"),
            (FCmpOp::OLt, "olt"),
            (FCmpOp::OLe, "ole"),
            (FCmpOp::OGt, "ogt"),
            (FCmpOp::OGe, "oge"),
            (FCmpOp::UEq, "ueq"),
            (FCmpOp::UNe, "une"),
            (FCmpOp::ULt, "ult"),
            (FCmpOp::ULe, "ule"),
            (FCmpOp::UGt, "ugt"),
            (FCmpOp::UGe, "uge"),
        ];
        for (op, name) in &ops_and_names {
            let mut module = Module::new("fcmp_ops");
            let ft = module
                .add_func_type(FuncTy {
                    params: vec![Ty::F64, Ty::F64],
                    returns: vec![Ty::Bool],
                    abi: None,
                    is_vararg: false,
                })
                .expect("Module::add_func_type: test fixture");
            let mut func = Function::new(FuncId::new(0), "f", ft, b(0));
            let mut block = Block::new(b(0));
            block.params.push((v(0), Ty::F64));
            block.params.push((v(1), Ty::F64));
            block.body.push(
                InstrNode::new(Inst::FCmp {
                    op: *op,
                    ty: Ty::F64,
                    lhs: v(0),
                    rhs: v(1),
                })
                .with_result(v(2)),
            );
            block
                .body
                .push(InstrNode::new(Inst::Return { values: vec![v(2)] }));
            func.blocks.push(block);
            module
                .try_add_function(func)
                .expect("Module::try_add_function: test fixture");

            let output = format!("{}", module);
            let expected = format!("fcmp {} f64 %0, %1", name);
            assert!(
                output.contains(&expected),
                "missing fcmp op {name}\noutput:\n{output}"
            );
        }
    }

    #[test]
    fn display_all_icmp_ops() {
        let ops_and_names = [
            (ICmpOp::Eq, "eq"),
            (ICmpOp::Ne, "ne"),
            (ICmpOp::Ult, "ult"),
            (ICmpOp::Ule, "ule"),
            (ICmpOp::Ugt, "ugt"),
            (ICmpOp::Uge, "uge"),
            (ICmpOp::Slt, "slt"),
            (ICmpOp::Sle, "sle"),
            (ICmpOp::Sgt, "sgt"),
            (ICmpOp::Sge, "sge"),
        ];
        for (op, name) in &ops_and_names {
            let mut module = Module::new("icmp_ops");
            let ft = module
                .add_func_type(FuncTy {
                    params: vec![Ty::I32, Ty::I32],
                    returns: vec![Ty::Bool],
                    abi: None,
                    is_vararg: false,
                })
                .expect("Module::add_func_type: test fixture");
            let mut func = Function::new(FuncId::new(0), "f", ft, b(0));
            let mut block = Block::new(b(0));
            block.params.push((v(0), Ty::I32));
            block.params.push((v(1), Ty::I32));
            block.body.push(
                InstrNode::new(Inst::ICmp {
                    op: *op,
                    ty: Ty::I32,
                    lhs: v(0),
                    rhs: v(1),
                })
                .with_result(v(2)),
            );
            block
                .body
                .push(InstrNode::new(Inst::Return { values: vec![v(2)] }));
            func.blocks.push(block);
            module
                .try_add_function(func)
                .expect("Module::try_add_function: test fixture");

            let output = format!("{}", module);
            let expected = format!("icmp {} i32 %0, %1", name);
            assert!(
                output.contains(&expected),
                "missing icmp op {name}\noutput:\n{output}"
            );
        }
    }

    #[test]
    fn display_all_binop_names() {
        let ops_and_names: Vec<(BinOp, &str)> = vec![
            (BinOp::Add, "add"),
            (BinOp::Sub, "sub"),
            (BinOp::Mul, "mul"),
            (BinOp::UDiv, "udiv"),
            (BinOp::SDiv, "sdiv"),
            (BinOp::URem, "urem"),
            (BinOp::SRem, "srem"),
            (BinOp::And, "and"),
            (BinOp::Or, "or"),
            (BinOp::Xor, "xor"),
            (BinOp::Shl, "shl"),
            (BinOp::LShr, "lshr"),
            (BinOp::AShr, "ashr"),
        ];
        for (op, name) in &ops_and_names {
            let mut module = Module::new("binops");
            let ft = module
                .add_func_type(FuncTy {
                    params: vec![Ty::I64, Ty::I64],
                    returns: vec![Ty::I64],
                    abi: None,
                    is_vararg: false,
                })
                .expect("Module::add_func_type: test fixture");
            let mut func = Function::new(FuncId::new(0), "f", ft, b(0));
            let mut block = Block::new(b(0));
            block.params.push((v(0), Ty::I64));
            block.params.push((v(1), Ty::I64));
            block.body.push(
                InstrNode::new(Inst::BinOp {
                    op: *op,
                    ty: Ty::I64,
                    lhs: v(0),
                    rhs: v(1),
                })
                .with_result(v(2)),
            );
            block
                .body
                .push(InstrNode::new(Inst::Return { values: vec![v(2)] }));
            func.blocks.push(block);
            module
                .try_add_function(func)
                .expect("Module::try_add_function: test fixture");

            let output = format!("{}", module);
            let expected = format!("{} i64 %0, %1", name);
            assert!(
                output.contains(&expected),
                "missing binop {name}\noutput:\n{output}"
            );
        }
    }

    #[test]
    fn display_all_overflow_ops() {
        let ops_and_names = [
            (OverflowOp::AddOverflow, "add.overflow"),
            (OverflowOp::SubOverflow, "sub.overflow"),
            (OverflowOp::MulOverflow, "mul.overflow"),
        ];
        for (op, name) in &ops_and_names {
            let mut module = Module::new("overflow_ops");
            let ft = module
                .add_func_type(FuncTy {
                    params: vec![Ty::I32, Ty::I32],
                    returns: vec![],
                    abi: None,
                    is_vararg: false,
                })
                .expect("Module::add_func_type: test fixture");
            let mut func = Function::new(FuncId::new(0), "f", ft, b(0));
            let mut block = Block::new(b(0));
            block.params.push((v(0), Ty::I32));
            block.params.push((v(1), Ty::I32));
            block.body.push(
                InstrNode::new(Inst::Overflow {
                    op: *op,
                    ty: Ty::I32,
                    lhs: v(0),
                    rhs: v(1),
                })
                .with_result(v(2))
                .with_result(v(3)),
            );
            block
                .body
                .push(InstrNode::new(Inst::Return { values: vec![] }));
            func.blocks.push(block);
            module
                .try_add_function(func)
                .expect("Module::try_add_function: test fixture");

            let output = format!("{}", module);
            let expected = format!("{} i32 %0, %1", name);
            assert!(
                output.contains(&expected),
                "missing overflow op {name}\noutput:\n{output}"
            );
        }
    }

    #[test]
    fn display_all_atomicrmw_ops() {
        let ops_and_names = [
            (AtomicRMWOp::Xchg, "xchg"),
            (AtomicRMWOp::Add, "add"),
            (AtomicRMWOp::Sub, "sub"),
            (AtomicRMWOp::And, "and"),
            (AtomicRMWOp::Or, "or"),
            (AtomicRMWOp::Xor, "xor"),
            (AtomicRMWOp::Max, "max"),
            (AtomicRMWOp::Min, "min"),
            (AtomicRMWOp::UMax, "umax"),
            (AtomicRMWOp::UMin, "umin"),
        ];
        for (op, name) in &ops_and_names {
            let mut module = Module::new("rmw_ops");
            let ft = module
                .add_func_type(FuncTy {
                    params: vec![Ty::Ptr, Ty::I64],
                    returns: vec![Ty::I64],
                    abi: None,
                    is_vararg: false,
                })
                .expect("Module::add_func_type: test fixture");
            let mut func = Function::new(FuncId::new(0), "f", ft, b(0));
            let mut block = Block::new(b(0));
            block.params.push((v(0), Ty::Ptr));
            block.params.push((v(1), Ty::I64));
            block.body.push(
                InstrNode::new(Inst::AtomicRMW {
                    op: *op,
                    ty: Ty::I64,
                    ptr: v(0),
                    value: v(1),
                    ordering: Ordering::SeqCst,
                })
                .with_result(v(2)),
            );
            block
                .body
                .push(InstrNode::new(Inst::Return { values: vec![v(2)] }));
            func.blocks.push(block);
            module
                .try_add_function(func)
                .expect("Module::try_add_function: test fixture");

            let output = format!("{}", module);
            let expected = format!("atomicrmw {} seq_cst i64 ptr %0, %1", name);
            assert!(
                output.contains(&expected),
                "missing rmw op {name}\noutput:\n{output}"
            );
        }
    }

    #[test]
    fn display_all_ordering_names() {
        let orderings = [
            (Ordering::Relaxed, "relaxed"),
            (Ordering::Acquire, "acquire"),
            (Ordering::Release, "release"),
            (Ordering::AcqRel, "acq_rel"),
            (Ordering::SeqCst, "seq_cst"),
        ];
        for (ordering, name) in &orderings {
            let mut module = Module::new("ordering");
            let ft = module
                .add_func_type(FuncTy {
                    params: vec![],
                    returns: vec![],
                    abi: None,
                    is_vararg: false,
                })
                .expect("Module::add_func_type: test fixture");
            let mut func = Function::new(FuncId::new(0), "f", ft, b(0));
            let mut block = Block::new(b(0));
            block.body.push(InstrNode::new(Inst::Fence {
                ordering: *ordering,
            }));
            block
                .body
                .push(InstrNode::new(Inst::Return { values: vec![] }));
            func.blocks.push(block);
            module
                .try_add_function(func)
                .expect("Module::try_add_function: test fixture");

            let output = format!("{}", module);
            let expected = format!("fence {}", name);
            assert!(
                output.contains(&expected),
                "missing ordering {name}\noutput:\n{output}"
            );
        }
    }

    #[test]
    fn display_empty_return() {
        let mut module = Module::new("empty_ret");
        let ft = module
            .add_func_type(FuncTy {
                params: vec![],
                returns: vec![],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut func = Function::new(FuncId::new(0), "f", ft, b(0));
        let mut block = Block::new(b(0));
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        func.blocks.push(block);
        module
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");

        let output = format!("{}", module);
        // "ret" with no values
        assert!(output.contains("    ret\n"));
    }

    #[test]
    fn display_multi_value_return() {
        let mut module = Module::new("multi_ret");
        let ft = module
            .add_func_type(FuncTy {
                params: vec![Ty::I32, Ty::I64],
                returns: vec![Ty::I32, Ty::I64],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut func = Function::new(FuncId::new(0), "f", ft, b(0));
        let mut block = Block::new(b(0));
        block.params.push((v(0), Ty::I32));
        block.params.push((v(1), Ty::I64));
        block.body.push(InstrNode::new(Inst::Return {
            values: vec![v(0), v(1)],
        }));
        func.blocks.push(block);
        module
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");

        let output = format!("{}", module);
        assert!(output.contains("ret %0, %1"));
    }

    #[test]
    fn display_switch_multiple_cases() {
        let mut module = Module::new("switch_multi");
        let ft = module
            .add_func_type(FuncTy {
                params: vec![Ty::I32],
                returns: vec![],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut func = Function::new(FuncId::new(0), "sw", ft, b(0));
        let mut bb0 = Block::new(b(0));
        bb0.params.push((v(0), Ty::I32));
        bb0.body.push(InstrNode::new(Inst::Switch {
            value: v(0),
            default: b(3),
            default_args: vec![],
            cases: vec![
                SwitchCase {
                    value: Constant::Int(0),
                    target: b(1),
                    args: vec![],
                },
                SwitchCase {
                    value: Constant::Int(1),
                    target: b(2),
                    args: vec![],
                },
            ],
            exhaustive_enum_unreachable: false,
        }));
        func.blocks.push(bb0);

        for i in 1..=3 {
            let mut bb = Block::new(b(i));
            bb.body
                .push(InstrNode::new(Inst::Return { values: vec![] }));
            func.blocks.push(bb);
        }
        module
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");

        let output = format!("{}", module);
        assert!(output.contains("switch %0"));
        assert!(output.contains("0: bb1"));
        assert!(output.contains("1: bb2"));
        assert!(output.contains("default: bb3"));
    }

    #[test]
    fn display_block_without_params() {
        let mut module = Module::new("no_params");
        let ft = module
            .add_func_type(FuncTy {
                params: vec![],
                returns: vec![],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut func = Function::new(FuncId::new(0), "f", ft, b(0));
        let mut block = Block::new(b(0));
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        func.blocks.push(block);
        module
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");

        let output = format!("{}", module);
        // Should be "bb0:" without parentheses
        assert!(output.contains("bb0:"));
        assert!(!output.contains("bb0("));
    }

    #[test]
    fn display_dealloc_instruction() {
        let mut module = Module::new("dealloc_test");
        let ft = module
            .add_func_type(FuncTy {
                params: vec![Ty::Ptr],
                returns: vec![],
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        let mut func = Function::new(FuncId::new(0), "free_ptr", ft, b(0));
        let mut block = Block::new(b(0));
        block.params.push((v(0), Ty::Ptr));
        block.body.push(InstrNode::new(Inst::Dealloc { ptr: v(0) }));
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        func.blocks.push(block);
        module
            .try_add_function(func)
            .expect("Module::try_add_function: test fixture");

        let output = format!("{}", module);
        assert!(output.contains("dealloc %0"));
    }

    #[test]
    fn display_struct_no_size_no_align() {
        let mut module = Module::new("struct_minimal");
        module.add_struct(StructDef {
            id: StructId::new(0),
            name: "Minimal".to_string(),
            fields: vec![FieldDef {
                name: "x".to_string(),
                ty: Ty::I32,
                offset: None,
            }],
            size: None,
            align: None,

            repr: Default::default(),
            origin: None,
        });

        let output = format!("{}", module);
        // WS4.5: the field name is carried; no offset was given, so none prints.
        assert!(
            output.contains("struct @Minimal { x: i32 } id=0"),
            "{output}"
        );
        assert!(!output.contains("size="));
        assert!(!output.contains("align="));
    }
}
