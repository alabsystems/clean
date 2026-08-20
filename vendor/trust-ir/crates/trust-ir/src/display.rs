// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use crate::constant::Constant;
use crate::inst::*;
use crate::node::InstrNode;
// ObligationKind and ProofStatus are used via their Display impls in the Module Display
use crate::ty::FuncTy;
use crate::{Block, Function, Module};
use core::fmt;

impl fmt::Display for Module {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "; TrustIr text format v1")?;
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

        // Debug-info source-file table; `SourceSpan::file` indexes it.
        for (i, path) in self.files.iter().enumerate() {
            writeln!(f, "file {i} {path:?}")?;
        }

        for sd in &self.structs {
            write!(f, "\nstruct @{} {{ ", sd.name)?;
            for (i, field) in sd.fields.iter().enumerate() {
                if i > 0 {
                    write!(f, ", ")?;
                }
                write!(f, "{}", field.ty)?;
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
            // Explicit id trailer (`id=N`) so the original `StructId` survives a
            // text round trip even when ids are sparse/non-contiguous (finding
            // E). Emitted last so the human-readable `struct @Name { .. }`
            // prefix is unchanged; the parser reads it back into `StructId`.
            write!(f, " id={}", sd.id.index())?;
            writeln!(f)?;
        }

        for ed in &self.enums {
            write!(f, "\nenum @{}", ed.name)?;
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
                write!(f, "{}", variant.name)?;
                if !variant.fields.is_empty() {
                    write!(f, "(")?;
                    for (j, ty) in variant.fields.iter().enumerate() {
                        if j > 0 {
                            write!(f, ", ")?;
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
            // Explicit id trailer (`id=N`) so the original `EnumId` survives a
            // text round trip even for sparse ids (finding E).
            writeln!(f, " }} id={}", ed.id.index())?;
        }

        for rd in &self.records {
            write!(f, "\nrecord @{} {{ ", rd.name)?;
            for (i, field) in rd.fields.iter().enumerate() {
                if i > 0 {
                    write!(f, ", ")?;
                }
                write!(f, "{}: {}", field.name, field.ty)?;
            }
            // Explicit id trailer (`id=N`) so the original `RecordId` survives
            // a text round trip even for sparse ids (finding E).
            writeln!(f, " }} id={}", rd.id.index())?;
        }

        for (idx, ft) in self.func_types.iter().enumerate() {
            write!(f, "\nfuncty.{idx} = ")?;
            write_func_ty(f, ft)?;
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
            write!(f, " @{} {}", global.name, global.ty)?;
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
            write!(
                f,
                "\nobligation {} {} {} {:?}",
                po.id.index(),
                po.kind,
                po.status,
                po.description,
            )?;
            // Scope clause (B4): which function this obligation is a
            // pre/postcondition OF. Omitted (back-compat) when None.
            if let Some(func) = &po.function {
                write!(f, " function {}", func.index())?;
            }
            if let Some(formula) = &po.formula {
                write!(f, " formula {:?} {:?}", formula.schema, formula.payload)?;
                if let Some(smtlib) = &formula.smtlib {
                    write!(f, " smtlib {:?}", smtlib)?;
                }
                if let Some(sort) = &formula.sort {
                    write!(f, " sort {:?}", sort)?;
                }
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
fn write_spec_module(f: &mut fmt::Formatter<'_>, sm: &crate::spec::SpecModule) -> fmt::Result {
    use crate::spec::SpecOrigin;
    writeln!(f, "\nspec_module {:?} {{", sm.name)?;
    match &sm.origin {
        SpecOrigin::Embedded => writeln!(f, "  origin embedded")?,
        SpecOrigin::External(path) => writeln!(f, "  origin external {path:?}")?,
    }
    writeln!(f, "  enforcement {}", sm.enforcement.tag())?;
    for v in &sm.vars {
        writeln!(f, "  var {:?} : {:?}", v.name, v.ty)?;
    }
    for a in &sm.actions {
        writeln!(f, "  action {a:?}")?;
    }
    for inv in &sm.invariants {
        writeln!(f, "  invariant {:?} : {:?}", inv.name, inv.formula)?;
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
        writeln!(
            f,
            "  proof machine {:?} action {:?} name {:?} kind {:?}",
            p.machine,
            p.action,
            p.proof_name,
            p.kind.tag(),
        )?;
    }
    writeln!(f, "}}")?;
    Ok(())
}

fn write_func_ty(f: &mut fmt::Formatter<'_>, ft: &FuncTy) -> fmt::Result {
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

impl fmt::Display for Function {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use crate::{CallingConv, Linkage};
        let ft_idx = self.ty.index();
        if self.linkage != Linkage::External {
            write!(f, "{} ", self.linkage)?;
        }
        if self.calling_conv != CallingConv::C {
            write!(f, "{} ", self.calling_conv)?;
        }
        write!(f, "fn @{}(functy.{ft_idx})", self.name)?;
        writeln!(f, " {{")?;

        // Producer provenance (v23). Same `; #...` comment-directive syntax as
        // proofs/attrs, so pre-v23 parsers skip it as an unknown directive
        // instead of failing. Known producers print their bare token; the
        // `Other` escape prints as a quoted (Debug-escaped) string.
        if let Some(producer) = &self.producer {
            writeln!(f, "    ; #producer: {producer}")?;
        }

        // Function-level proof annotations (finding B). Mirrors the
        // instruction-node `; #proof:` comment syntax; the parser reads these
        // back into `Function.proofs` before the first block.
        if !self.proofs.is_empty() {
            write!(f, "    ; #proof:")?;
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
            write!(f, "    ; #names:")?;
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
                write!(f, "    ; #scope: {i}")?;
                match sc.parent {
                    None => write!(f, " root")?,
                    Some(p) => write!(f, " parent={p}")?,
                }
                if let Some(span) = &sc.span {
                    write!(f, " at {} {} {}", span.file, span.line, span.col)?;
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
                "    ; #source-provenance: schema {} compiler {:?} semantic {:?} binding {:?}",
                provenance.schema,
                provenance.compiler_source_digest.to_string(),
                provenance.semantic_body_digest.to_string(),
                provenance.binding_digest.to_string(),
            )?;
            for source_loop in &provenance.loops {
                writeln!(
                    f,
                    "    ; #source-loop: {} hir {} header {}",
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
                        "    ; #source-binding: loop {} name {:?} hir {} {} {}",
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

/// Write `FuncAttrs` (and per-parameter `ParamAttrs`) as `;`-comment lines so
/// the text form carries the same optimization hints the binary codec does
/// (finding B). Empty attrs emit nothing.
fn write_func_attrs(f: &mut fmt::Formatter<'_>, attrs: &crate::FuncAttrs) -> fmt::Result {
    let func_flags = [
        (attrs.readonly, "readonly"),
        (attrs.readnone, "readnone"),
        (attrs.inlinehint, "inlinehint"),
        (attrs.cold, "cold"),
    ];
    if func_flags.iter().any(|(set, _)| *set) {
        write!(f, "    ; #attrs:")?;
        for (set, name) in func_flags {
            if set {
                write!(f, " {name}")?;
            }
        }
        writeln!(f)?;
    }
    for (i, pa) in attrs.params.iter().enumerate() {
        if pa.is_empty() {
            continue;
        }
        write!(f, "    ; #param_attrs {i}:")?;
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
        writeln!(f)?;
    }
    Ok(())
}

impl fmt::Display for Block {
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

fn write_instr_node(f: &mut fmt::Formatter<'_>, node: &InstrNode) -> fmt::Result {
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
        write!(f, "  ; #proof:")?;
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
        write!(f, "  ; #proof_ctx: assumes[")?;
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
        write!(f, "  ; #loc: {} {} {}", span.file, span.line, span.col)?;
    }
    // Lexical scope index (v33), into the enclosing function's `; #scope:` table.
    if let Some(scope) = node.scope {
        write!(f, "  ; #scope: {scope}")?;
    }

    Ok(())
}

fn val(id: &crate::value::ValueId) -> u32 {
    id.index()
}

fn write_inst(f: &mut fmt::Formatter<'_>, inst: &Inst) -> fmt::Result {
    match inst {
        Inst::SeqMapAddK { ty, seq, k } => {
            write!(f, "seq_map_add_k {ty} %{}, {k}", val(seq))
        }
        Inst::SeqMapNot { ty, seq } => {
            write!(f, "seq_map_not {ty} %{}", val(seq))
        }
        Inst::SeqMap { ty, seq, fwd } => {
            write!(f, "seq_map {ty} %{}, @func.{}", val(seq), fwd.index())
        }
        Inst::BinOp { op, ty, lhs, rhs } => {
            write!(f, "{op} {ty} %{}, %{}", val(lhs), val(rhs))
        }
        Inst::UnOp { op, ty, operand } => {
            write!(f, "{op} {ty} %{}", val(operand))
        }
        Inst::Overflow { op, ty, lhs, rhs } => {
            write!(f, "{op} {ty} %{}, %{}", val(lhs), val(rhs))
        }
        Inst::ICmp { op, ty, lhs, rhs } => {
            write!(f, "icmp {op} {ty} %{}, %{}", val(lhs), val(rhs))
        }
        Inst::FCmp { op, ty, lhs, rhs } => {
            write!(f, "fcmp {op} {ty} %{}, %{}", val(lhs), val(rhs))
        }
        Inst::Cast {
            op,
            src_ty,
            dst_ty,
            operand,
        } => {
            write!(f, "{op} {src_ty} %{} to {dst_ty}", val(operand))
        }
        Inst::Load {
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
        Inst::Store {
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
        Inst::Alloca { ty, count, align } => {
            write!(f, "alloca {ty}")?;
            if let Some(c) = count {
                write!(f, ", %{}", val(c))?;
            }
            if let Some(a) = align {
                write!(f, ", align {a}")?;
            }
            Ok(())
        }
        Inst::HeapAlloc {
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
        Inst::GEP {
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
        Inst::PtrData { ptr_ty, ptr } => {
            write!(f, "ptr_data {ptr_ty} %{}", val(ptr))
        }
        Inst::PtrMetadata {
            ptr_ty,
            metadata_ty,
            ptr,
        } => {
            write!(f, "ptr_metadata {ptr_ty} %{} to {metadata_ty}", val(ptr))
        }
        Inst::PtrFromParts {
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
        Inst::AtomicLoad { ty, ptr, ordering } => {
            write!(f, "atomic_load {ordering} {ty}, ptr %{}", val(ptr))
        }
        Inst::AtomicStore {
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
        Inst::AtomicRMW {
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
        Inst::CmpXchg {
            ty,
            ptr,
            expected,
            desired,
            success,
            failure,
        } => write!(
            f,
            "cmpxchg {ty} ptr %{}, %{}, %{} {success} {failure}",
            val(ptr),
            val(expected),
            val(desired),
        ),
        Inst::Fence { ordering } => write!(f, "fence {ordering}"),
        Inst::Br { target, args } => {
            write!(f, "br bb{}", target.index())?;
            write_block_args(f, args)
        }
        Inst::CondBr {
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
        Inst::Switch {
            value,
            default,
            default_args,
            cases,
            ..
        } => {
            write!(f, "switch %{} [", val(value))?;
            for case in cases {
                write!(f, " {}: bb{}", case.value, case.target.index())?;
                write_block_args(f, &case.args)?;
            }
            write!(f, " default: bb{}", default.index())?;
            write_block_args(f, default_args)?;
            write!(f, " ]")
        }
        Inst::Call { callee, args } => {
            write!(f, "call @func.{}", callee.index())?;
            write!(f, "(")?;
            for (i, a) in args.iter().enumerate() {
                if i > 0 {
                    write!(f, ", ")?;
                }
                write!(f, "%{}", val(a))?;
            }
            write!(f, ")")
        }
        Inst::CallIndirect {
            callee,
            sig,
            args,
            calling_conv,
        } => {
            write!(f, "call_indirect %{}(functy.{})(", val(callee), sig.index())?;
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
        Inst::Return { values } => {
            write!(f, "ret")?;
            for (i, v) in values.iter().enumerate() {
                if i > 0 {
                    write!(f, ",")?;
                }
                write!(f, " %{}", val(v))?;
            }
            Ok(())
        }
        Inst::ExtractField {
            ty,
            aggregate,
            field,
        } => write!(f, "extractfield {ty} %{}, {field}", val(aggregate)),
        Inst::InsertField {
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
        Inst::ExtractElement { ty, array, index } => {
            write!(f, "extractelement {ty} %{}, %{}", val(array), val(index))
        }
        Inst::InsertElement {
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
        Inst::Const { ty, value: c } => write!(f, "const {ty} {c}"),
        Inst::NullPtr => write!(f, "null ptr"),
        Inst::GlobalAddr { global } => write!(f, "global_addr @global.{}", global.index()),
        Inst::Undef { ty } => write!(f, "undef {ty}"),
        Inst::Assume { cond } => write!(f, "assume %{}", val(cond)),
        Inst::Assert { cond } => write!(f, "assert %{}", val(cond)),
        Inst::Unreachable => write!(f, "unreachable"),
        Inst::Copy { ty, operand } => write!(f, "copy {ty} %{}", val(operand)),
        Inst::Select {
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
        Inst::Borrow { ptr } => write!(f, "borrow %{}", val(ptr)),
        Inst::BorrowMut { ptr } => write!(f, "borrow_mut %{}", val(ptr)),
        Inst::EndBorrow { borrow_ptr } => write!(f, "end_borrow %{}", val(borrow_ptr)),
        // ARC instructions
        Inst::Retain { ptr } => write!(f, "retain %{}", val(ptr)),
        Inst::Release { ptr } => write!(f, "release %{}", val(ptr)),
        Inst::IsUnique { ptr } => write!(f, "is_unique %{}", val(ptr)),
        // Heap deallocation
        Inst::Dealloc { ptr } => write!(f, "dealloc %{}", val(ptr)),
        // Binding frames (typed SSA frames for quantifier lowering)
        Inst::OpenFrame { def } => {
            write!(f, "open_frame #{} {:?} {{", def.id.index(), def.name)?;
            for (i, slot) in def.slots.iter().enumerate() {
                if i > 0 {
                    write!(f, ", ")?;
                }
                write!(f, "{}: {}", slot.name, slot.ty)?;
            }
            write!(f, "}}")
        }
        Inst::BindSlot { frame, slot, value } => {
            write!(f, "bind_slot %{}, {}, %{}", val(frame), slot, val(value))
        }
        Inst::LoadSlot { frame, slot, ty } => {
            write!(f, "load_slot {} %{}, {}", ty, val(frame), slot)
        }
        Inst::CloseFrame { frame } => write!(f, "close_frame %{}", val(frame)),
        // Coroutine suspend: `coro_suspend %frame, <state_slot>, <next_state>, %value`
        Inst::CoroSuspend {
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
        Inst::Invoke {
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
        // `landingpad [cleanup] catch <i0>, <i1>, ..`
        Inst::LandingPad {
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
        Inst::Resume { exn } => write!(f, "resume %{}", val(exn)),
        // Dialect op: `dialect_op <dialect>.<op>(%0, %1) -> (i32, bool) [attr=val] v<version>`
        Inst::DialectOp(op) => write_dialect_op(f, op),
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
        ProofEvidence::InheritedFromCallee { callee, obligation } => {
            write!(f, "inherited {} {}", callee.index(), obligation.index())
        }
        ProofEvidence::CleanCic {
            term,
            context,
            lineage,
            // The textual format carries only the lineage-bound payload; the
            // kernel re-check directive travels in the structured (serde/binary)
            // format consumed by `trust_ir_build::validate`.
            kernel_recheck: _,
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
            write!(f, "]")
        }
    }
}

impl fmt::Display for Constant {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Constant::Int(v) => write!(f, "{v}"),
            // v24: prints the TRUE unsigned value (the point of the 128-bit-
            // faithful carrier). Canonicality (value > i128::MAX) means the
            // parser reads the literal back into the same variant by VALUE —
            // `parse(display(x)) == x` holds with no type context.
            Constant::U128(v) => write!(f, "{v}"),
            // v25 Bytes: hex payload keeps the text form injective and
            // parser-trivial for EVERY byte value (no escape grammar); the
            // utf8 claim is spelled in the token so it round-trips.
            Constant::Bytes { data, utf8 } => {
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
            Constant::Float(v) => write_constant_float(f, *v),
            Constant::Bool(b) => write!(f, "{b}"),
            Constant::Aggregate(elems) => {
                write!(f, "{{ ")?;
                for (i, e) in elems.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{e}")?;
                }
                write!(f, " }}")
            }
            Constant::Array(elems) => {
                write!(f, "array[ ")?;
                for (i, e) in elems.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{e}")?;
                }
                write!(f, " ]")
            }
            Constant::Vector(elems) => {
                write!(f, "vec[ ")?;
                for (i, e) in elems.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{e}")?;
                }
                write!(f, " ]")
            }
            Constant::Sequence(elems) => {
                write!(f, "seq[ ")?;
                for (i, e) in elems.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{e}")?;
                }
                write!(f, " ]")
            }
            Constant::Set(elems) => {
                write!(f, "set{{ ")?;
                for (i, e) in elems.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{e}")?;
                }
                write!(f, " }}")
            }
            Constant::Record(fields) => {
                write!(f, "record{{ ")?;
                for (i, (name, val)) in fields.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{name} = {val}")?;
                }
                write!(f, " }}")
            }
            Constant::Closure { func, captures } => {
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
            Constant::FnDef(func) => write!(f, "fndef<func.{}>", func.index()),
            Constant::SymbolAddr { symbol, addend } => {
                if *addend == 0 {
                    write!(f, "symaddr<{symbol}>")
                } else {
                    write!(f, "symaddr<{symbol} + {addend}>")
                }
            }
            Constant::PhantomData => write!(f, "phantomdata"),
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
        let ft_id = module.add_func_type(FuncTy {
            params: vec![Ty::I64, Ty::I64],
            returns: vec![Ty::I64],
            is_vararg: false,
        });

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
        module.add_function(func);
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
        });
        let output = format!("{}", module);
        assert!(output.contains("struct @Point"));
        assert!(output.contains("f64, f64"));
        assert!(output.contains("size=16"));
        assert!(output.contains("align=8"));
        // Explicit id trailer preserves the StructId across a text round trip.
        assert!(output.contains("id=0"));
    }

    #[test]
    fn display_const_instruction() {
        let mut module = Module::new("consts");
        let ft = module.add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::I32],
            is_vararg: false,
        });
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
        module.add_function(func);

        let output = format!("{}", module);
        assert!(output.contains("const i32 42"));
    }

    #[test]
    fn display_load_store() {
        let mut module = Module::new("mem");
        let ft = module.add_func_type(FuncTy {
            params: vec![Ty::Ptr],
            returns: vec![],
            is_vararg: false,
        });
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
        module.add_function(func);

        let output = format!("{}", module);
        assert!(output.contains("load i32, ptr %0"));
        assert!(output.contains("store i32 %1, ptr %0"));
    }

    #[test]
    fn display_alloca() {
        let mut module = Module::new("alloca_test");
        let ft = module.add_func_type(FuncTy {
            params: vec![],
            returns: vec![],
            is_vararg: false,
        });
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
        module.add_function(func);

        let output = format!("{}", module);
        assert!(output.contains("alloca i32"));
    }

    #[test]
    fn display_gep() {
        let mut module = Module::new("gep_test");
        let ft = module.add_func_type(FuncTy {
            params: vec![Ty::Ptr],
            returns: vec![],
            is_vararg: false,
        });
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
        module.add_function(func);

        let output = format!("{}", module);
        assert!(output.contains("gep i32, ptr %0, %1"));
    }

    #[test]
    fn display_branch_instructions() {
        let mut module = Module::new("branches");
        let ft = module.add_func_type(FuncTy {
            params: vec![Ty::Bool],
            returns: vec![Ty::I32],
            is_vararg: false,
        });
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

        module.add_function(func);

        let output = format!("{}", module);
        assert!(output.contains("condbr %0, bb1, bb2"));
        assert!(output.contains("br bb3(%1)"));
        assert!(output.contains("br bb3(%2)"));
        assert!(output.contains("bb3(%3: i32):"));
    }

    #[test]
    fn display_call() {
        let mut module = Module::new("call_test");
        let ft = module.add_func_type(FuncTy {
            params: vec![Ty::I32, Ty::I32],
            returns: vec![Ty::I32],
            is_vararg: false,
        });
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
        module.add_function(func);

        let output = format!("{}", module);
        assert!(output.contains("call @func.1(%0, %1)"));
    }

    #[test]
    fn display_cast() {
        let mut module = Module::new("cast_test");
        let ft = module.add_func_type(FuncTy {
            params: vec![Ty::I32],
            returns: vec![Ty::I64],
            is_vararg: false,
        });
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
        module.add_function(func);

        let output = format!("{}", module);
        assert!(output.contains("sext i32 %0 to i64"));
    }

    #[test]
    fn display_icmp() {
        let mut module = Module::new("icmp_test");
        let ft = module.add_func_type(FuncTy {
            params: vec![Ty::I32, Ty::I32],
            returns: vec![Ty::Bool],
            is_vararg: false,
        });
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
        module.add_function(func);

        let output = format!("{}", module);
        assert!(output.contains("icmp slt i32 %0, %1"));
    }

    #[test]
    fn display_proof_annotation() {
        let mut module = Module::new("proofs");
        let ft = module.add_func_type(FuncTy {
            params: vec![Ty::Ptr],
            returns: vec![Ty::I32],
            is_vararg: false,
        });
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
        module.add_function(func);

        let output = format!("{}", module);
        assert!(output.contains("#proof:"));
        assert!(output.contains("in_bounds"));
        assert!(output.contains("not_null"));
    }

    #[test]
    fn display_null_ptr() {
        let mut module = Module::new("null");
        let ft = module.add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::Ptr],
            is_vararg: false,
        });
        let mut func = Function::new(FuncId::new(0), "get_null", ft, b(0));
        let mut block = Block::new(b(0));
        block
            .body
            .push(InstrNode::new(Inst::NullPtr).with_result(v(0)));
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![v(0)] }));
        func.blocks.push(block);
        module.add_function(func);

        let output = format!("{}", module);
        assert!(output.contains("null ptr"));
    }

    #[test]
    fn display_unreachable() {
        let mut module = Module::new("unr");
        let ft = module.add_func_type(FuncTy {
            params: vec![],
            returns: vec![],
            is_vararg: false,
        });
        let mut func = Function::new(FuncId::new(0), "panic", ft, b(0));
        let mut block = Block::new(b(0));
        block.body.push(InstrNode::new(Inst::Unreachable));
        func.blocks.push(block);
        module.add_function(func);

        let output = format!("{}", module);
        assert!(output.contains("unreachable"));
    }

    #[test]
    fn display_atomic_operations() {
        let mut module = Module::new("atomics");
        let ft = module.add_func_type(FuncTy {
            params: vec![Ty::Ptr],
            returns: vec![],
            is_vararg: false,
        });
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
        module.add_function(func);

        let output = format!("{}", module);
        assert!(output.contains("atomic_load acquire i64, ptr %0"));
        assert!(output.contains("atomic_store release i64 %1, ptr %0"));
        assert!(output.contains("fence seq_cst"));
    }

    #[test]
    fn display_switch() {
        let mut module = Module::new("switch");
        let ft = module.add_func_type(FuncTy {
            params: vec![Ty::I32],
            returns: vec![],
            is_vararg: false,
        });
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
        module.add_function(func);

        let output = format!("{}", module);
        assert!(output.contains("switch %0"));
        assert!(output.contains("1: bb1"));
        assert!(output.contains("default: bb2"));
    }

    #[test]
    fn display_multiple_functions() {
        let mut module = Module::new("multi");
        let ft = module.add_func_type(FuncTy {
            params: vec![],
            returns: vec![],
            is_vararg: false,
        });
        for i in 0..3 {
            let mut func = Function::new(FuncId::new(i), format!("func_{i}"), ft, b(0));
            let mut block = Block::new(b(0));
            block
                .body
                .push(InstrNode::new(Inst::Return { values: vec![] }));
            func.blocks.push(block);
            module.add_function(func);
        }
        let output = format!("{}", module);
        assert!(output.contains("fn @func_0"));
        assert!(output.contains("fn @func_1"));
        assert!(output.contains("fn @func_2"));
    }

    #[test]
    fn display_overflow_instruction() {
        let mut module = Module::new("overflow");
        let ft = module.add_func_type(FuncTy {
            params: vec![Ty::I32, Ty::I32],
            returns: vec![Ty::I32, Ty::Bool],
            is_vararg: false,
        });
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
        module.add_function(func);

        let output = format!("{}", module);
        assert!(output.contains("add.overflow i32 %0, %1"));
        assert!(output.contains("%2, %3 ="));
    }

    #[test]
    fn display_select() {
        let mut module = Module::new("select");
        let ft = module.add_func_type(FuncTy {
            params: vec![Ty::Bool, Ty::I32, Ty::I32],
            returns: vec![Ty::I32],
            is_vararg: false,
        });
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
        module.add_function(func);

        let output = format!("{}", module);
        assert!(output.contains("select i32 %0, %1, %2"));
    }

    // --- NEW DISPLAY TESTS ---

    #[test]
    fn display_copy_instruction() {
        let mut module = Module::new("copy_test");
        let ft = module.add_func_type(FuncTy {
            params: vec![Ty::I32],
            returns: vec![Ty::I32],
            is_vararg: false,
        });
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
        module.add_function(func);

        let output = format!("{}", module);
        assert!(output.contains("copy i32 %0"));
    }

    #[test]
    fn display_undef_instruction() {
        let mut module = Module::new("undef_test");
        let ft = module.add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::I64],
            is_vararg: false,
        });
        let mut func = Function::new(FuncId::new(0), "f", ft, b(0));
        let mut block = Block::new(b(0));
        block
            .body
            .push(InstrNode::new(Inst::Undef { ty: Ty::I64 }).with_result(v(0)));
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![v(0)] }));
        func.blocks.push(block);
        module.add_function(func);

        let output = format!("{}", module);
        assert!(output.contains("undef i64"));
    }

    #[test]
    fn display_assume_instruction() {
        let mut module = Module::new("assume_test");
        let ft = module.add_func_type(FuncTy {
            params: vec![Ty::Bool],
            returns: vec![],
            is_vararg: false,
        });
        let mut func = Function::new(FuncId::new(0), "f", ft, b(0));
        let mut block = Block::new(b(0));
        block.params.push((v(0), Ty::Bool));
        block.body.push(InstrNode::new(Inst::Assume { cond: v(0) }));
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        func.blocks.push(block);
        module.add_function(func);

        let output = format!("{}", module);
        assert!(output.contains("assume %0"));
    }

    #[test]
    fn display_assert_instruction() {
        let mut module = Module::new("assert_test");
        let ft = module.add_func_type(FuncTy {
            params: vec![Ty::Bool],
            returns: vec![],
            is_vararg: false,
        });
        let mut func = Function::new(FuncId::new(0), "f", ft, b(0));
        let mut block = Block::new(b(0));
        block.params.push((v(0), Ty::Bool));
        block.body.push(InstrNode::new(Inst::Assert { cond: v(0) }));
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        func.blocks.push(block);
        module.add_function(func);

        let output = format!("{}", module);
        assert!(output.contains("assert %0"));
    }

    #[test]
    fn display_fcmp_instruction() {
        let mut module = Module::new("fcmp_test");
        let ft = module.add_func_type(FuncTy {
            params: vec![Ty::F64, Ty::F64],
            returns: vec![Ty::Bool],
            is_vararg: false,
        });
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
        module.add_function(func);

        let output = format!("{}", module);
        assert!(output.contains("fcmp oeq f64 %0, %1"));
    }

    #[test]
    fn display_cmpxchg_instruction() {
        let mut module = Module::new("cmpxchg_test");
        let ft = module.add_func_type(FuncTy {
            params: vec![Ty::Ptr, Ty::I64, Ty::I64],
            returns: vec![],
            is_vararg: false,
        });
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
            })
            .with_result(v(3)),
        );
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        func.blocks.push(block);
        module.add_function(func);

        let output = format!("{}", module);
        assert!(output.contains("cmpxchg i64 ptr %0, %1, %2 seq_cst acquire"));
    }

    #[test]
    fn display_atomicrmw_instruction() {
        let mut module = Module::new("rmw_test");
        let ft = module.add_func_type(FuncTy {
            params: vec![Ty::Ptr, Ty::I64],
            returns: vec![Ty::I64],
            is_vararg: false,
        });
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
        module.add_function(func);

        let output = format!("{}", module);
        assert!(output.contains("atomicrmw add acq_rel i64 ptr %0, %1"));
    }

    #[test]
    fn display_call_indirect_instruction() {
        let mut module = Module::new("calli_test");
        let ft_callee = module.add_func_type(FuncTy {
            params: vec![Ty::I32],
            returns: vec![Ty::I32],
            is_vararg: false,
        });
        let ft = module.add_func_type(FuncTy {
            params: vec![Ty::Ptr, Ty::I32],
            returns: vec![Ty::I32],
            is_vararg: false,
        });
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
        module.add_function(func);

        let output = format!("{}", module);
        assert!(output.contains("call_indirect %0(functy.0)(%1)"));
    }

    #[test]
    fn display_extract_element_instruction() {
        let mut module = Module::new("ee_test");
        let ft = module.add_func_type(FuncTy {
            params: vec![Ty::Ptr, Ty::I64],
            returns: vec![Ty::I32],
            is_vararg: false,
        });
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
        module.add_function(func);

        let output = format!("{}", module);
        assert!(output.contains("extractelement i32 %0, %1"));
    }

    #[test]
    fn display_insert_element_instruction() {
        let mut module = Module::new("ie_test");
        let ft = module.add_func_type(FuncTy {
            params: vec![Ty::Ptr, Ty::I64, Ty::I32],
            returns: vec![Ty::Ptr],
            is_vararg: false,
        });
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
        module.add_function(func);

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
        });
        let ft = module.add_func_type(FuncTy {
            params: vec![Ty::Struct(sid), Ty::I32],
            returns: vec![Ty::Struct(sid)],
            is_vararg: false,
        });
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
        module.add_function(func);

        let output = format!("{}", module);
        assert!(output.contains("insertfield struct.0 %0, 0, %1"));
    }

    #[test]
    fn display_float_binops() {
        let mut module = Module::new("fbinops");
        let ft = module.add_func_type(FuncTy {
            params: vec![Ty::F64, Ty::F64],
            returns: vec![Ty::F64],
            is_vararg: false,
        });
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
        module.add_function(func);

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
        let ft = module.add_func_type(FuncTy {
            params: vec![Ty::F64, Ty::I32],
            returns: vec![],
            is_vararg: false,
        });
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
        module.add_function(func);

        let output = format!("{}", module);
        assert!(output.contains("fneg f64 %0"));
        assert!(output.contains("not i32 %1"));
    }

    #[test]
    fn display_all_cast_ops() {
        let mut module = Module::new("casts");
        let ft = module.add_func_type(FuncTy {
            params: vec![Ty::I64, Ty::F64, Ty::Ptr],
            returns: vec![],
            is_vararg: false,
        });
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
        module.add_function(func);

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
        let ft = module.add_func_type(FuncTy {
            params: vec![],
            returns: vec![],
            is_vararg: false,
        });
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
        module.add_function(func);

        let output = format!("{}", module);
        assert!(output.contains("alloca i32, %0"));
    }

    #[test]
    fn display_constant_bool() {
        let mut module = Module::new("cbool");
        let ft = module.add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::Bool],
            is_vararg: false,
        });
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
        module.add_function(func);

        let output = format!("{}", module);
        assert!(output.contains("const bool true"));
    }

    #[test]
    fn display_constant_float() {
        let mut module = Module::new("cfloat");
        let ft = module.add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::F64],
            is_vararg: false,
        });
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
        module.add_function(func);

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
            let ft = module.add_func_type(FuncTy {
                params: vec![Ty::F64, Ty::F64],
                returns: vec![Ty::Bool],
                is_vararg: false,
            });
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
            module.add_function(func);

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
            let ft = module.add_func_type(FuncTy {
                params: vec![Ty::I32, Ty::I32],
                returns: vec![Ty::Bool],
                is_vararg: false,
            });
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
            module.add_function(func);

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
            let ft = module.add_func_type(FuncTy {
                params: vec![Ty::I64, Ty::I64],
                returns: vec![Ty::I64],
                is_vararg: false,
            });
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
            module.add_function(func);

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
            let ft = module.add_func_type(FuncTy {
                params: vec![Ty::I32, Ty::I32],
                returns: vec![],
                is_vararg: false,
            });
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
            module.add_function(func);

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
            let ft = module.add_func_type(FuncTy {
                params: vec![Ty::Ptr, Ty::I64],
                returns: vec![Ty::I64],
                is_vararg: false,
            });
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
            module.add_function(func);

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
            let ft = module.add_func_type(FuncTy {
                params: vec![],
                returns: vec![],
                is_vararg: false,
            });
            let mut func = Function::new(FuncId::new(0), "f", ft, b(0));
            let mut block = Block::new(b(0));
            block.body.push(InstrNode::new(Inst::Fence {
                ordering: *ordering,
            }));
            block
                .body
                .push(InstrNode::new(Inst::Return { values: vec![] }));
            func.blocks.push(block);
            module.add_function(func);

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
        let ft = module.add_func_type(FuncTy {
            params: vec![],
            returns: vec![],
            is_vararg: false,
        });
        let mut func = Function::new(FuncId::new(0), "f", ft, b(0));
        let mut block = Block::new(b(0));
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        func.blocks.push(block);
        module.add_function(func);

        let output = format!("{}", module);
        // "ret" with no values
        assert!(output.contains("    ret\n"));
    }

    #[test]
    fn display_multi_value_return() {
        let mut module = Module::new("multi_ret");
        let ft = module.add_func_type(FuncTy {
            params: vec![Ty::I32, Ty::I64],
            returns: vec![Ty::I32, Ty::I64],
            is_vararg: false,
        });
        let mut func = Function::new(FuncId::new(0), "f", ft, b(0));
        let mut block = Block::new(b(0));
        block.params.push((v(0), Ty::I32));
        block.params.push((v(1), Ty::I64));
        block.body.push(InstrNode::new(Inst::Return {
            values: vec![v(0), v(1)],
        }));
        func.blocks.push(block);
        module.add_function(func);

        let output = format!("{}", module);
        assert!(output.contains("ret %0, %1"));
    }

    #[test]
    fn display_switch_multiple_cases() {
        let mut module = Module::new("switch_multi");
        let ft = module.add_func_type(FuncTy {
            params: vec![Ty::I32],
            returns: vec![],
            is_vararg: false,
        });
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
        module.add_function(func);

        let output = format!("{}", module);
        assert!(output.contains("switch %0"));
        assert!(output.contains("0: bb1"));
        assert!(output.contains("1: bb2"));
        assert!(output.contains("default: bb3"));
    }

    #[test]
    fn display_block_without_params() {
        let mut module = Module::new("no_params");
        let ft = module.add_func_type(FuncTy {
            params: vec![],
            returns: vec![],
            is_vararg: false,
        });
        let mut func = Function::new(FuncId::new(0), "f", ft, b(0));
        let mut block = Block::new(b(0));
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        func.blocks.push(block);
        module.add_function(func);

        let output = format!("{}", module);
        // Should be "bb0:" without parentheses
        assert!(output.contains("bb0:"));
        assert!(!output.contains("bb0("));
    }

    #[test]
    fn display_dealloc_instruction() {
        let mut module = Module::new("dealloc_test");
        let ft = module.add_func_type(FuncTy {
            params: vec![Ty::Ptr],
            returns: vec![],
            is_vararg: false,
        });
        let mut func = Function::new(FuncId::new(0), "free_ptr", ft, b(0));
        let mut block = Block::new(b(0));
        block.params.push((v(0), Ty::Ptr));
        block.body.push(InstrNode::new(Inst::Dealloc { ptr: v(0) }));
        block
            .body
            .push(InstrNode::new(Inst::Return { values: vec![] }));
        func.blocks.push(block);
        module.add_function(func);

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
        });

        let output = format!("{}", module);
        assert!(output.contains("struct @Minimal { i32 } id=0"));
        assert!(!output.contains("size="));
        assert!(!output.contains("align="));
    }
}
